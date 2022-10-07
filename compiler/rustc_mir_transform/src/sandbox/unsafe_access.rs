//! Analyze each function to find unsafe memory accesses, using the unsafe heap
//! allocation site information collected from earlier.

use rustc_middle::ty::{TyCtxt};
use rustc_middle::mir::*;
use rustc_hir::def_id::{DefId};
use rustc_data_structures::fx::{FxHashSet};
use std::fs;

use super::wpa::{WPSummary, UnsafeSources};
use super::summarize_fn::{DefSite, FnID};
use super::utils::*;

/// Unsafe memory accesses in one Statement or one Terminator.
pub struct UnsafeAccess{
    _bb: u32,
    /// Index of the Statement/Termiantor in _bb.
    _index: u32,
    _is_terminator: bool,
    /// Unsafe Local of Place in this Statement/Terminator. Each S/T may have
    /// multiple Place.
    locals: Vec::<u32>,
}

pub type UnsafeAccesses = (FnID, Vec::<UnsafeAccess>);

/// Read in the wholle-program analysis result, i.e., unsafe sources.
pub fn read_wpa() -> WPSummary {
    let wpa_result_str = fs::read_to_string(get_wp_summary_path()).expect(
        "Read the WPA result to string");
    let unsafe_sources = serde_json::from_str::<UnsafeSources>(&wpa_result_str).
        expect("deserializing wpa result");
    let mut wpa_result = WPSummary::default();
    for fn_unsafe_source in unsafe_sources {
        wpa_result.insert(fn_unsafe_source.0, fn_unsafe_source.1);
    }

    wpa_result
}

/// Get the max of a given u32 and the u32 of the Local of a Place.
#[inline(always)]
fn get_max<'tcx>(max: u32, place: Place<'tcx>) -> u32 {
    let local = place.local.as_u32();
    return if local > max { local } else { max }
}

/// Cound the number of Place in a function. This is currently for debugging.
#[allow(dead_code)]
fn count_place_num<'tcx>(body: &'tcx Body<'tcx>) -> u32 {
    let mut max_local = body.arg_count as u32;
    for (_, bbd) in body.basic_blocks().iter_enumerated() {
        for (_, stmt) in bbd.statements.iter().enumerate() {
            match &stmt.kind {
                StatementKind::Assign(box (lhs_place, rvalue)) => {
                    max_local = get_max(max_local, *lhs_place);
                    let mut place_in_rvalue = Vec::<Place<'tcx>>::new();
                    get_place_in_rvalue(&rvalue, &mut place_in_rvalue);
                    for place in place_in_rvalue {
                        max_local = get_max(max_local, place);
                    }
                },
                StatementKind::SetDiscriminant {box place, ..} |
                StatementKind::Deinit(box place) |
                StatementKind::Retag(_, box place) |
                StatementKind::AscribeUserType(box (place, _), _) => {
                    max_local = get_max(max_local, *place);
                },
                StatementKind::CopyNonOverlapping(box cno) => {
                    let mut places = Vec::new();
                    get_place_in_operand(&cno.src, &mut places);
                    get_place_in_operand(&cno.dst, &mut places);
                    get_place_in_operand(&cno.count, &mut places);
                    for place in places {
                        max_local = get_max(max_local, place);
                    }
                }
                _ => {}
            }
        }

        let mut places = Vec::new();
        get_place_in_terminator(body, &bbd.terminator(), &mut places);
        for place in places {
            max_local = get_max(max_local, place);
        }
    }

    max_local
}

/// Collect the Local of all unsafe Place of a function. The algorithm is
/// simple: examine each StatementKind::Assign, and if any unsafe Place is
/// used in the RHS, then the LHS is regarded as unsafe as well. Repeat this
/// process until there is no new unsafe Place added.
fn collect_unsafe_locals<'tcx>(unsafe_sources: &FxHashSet<DefSite>,
                               body: &'tcx Body<'tcx>) -> FxHashSet<Local> {
    // Unsafe arguments and non-arg places(as u32).
    let mut unsafe_locals = FxHashSet::<Local>::default();
    let mut unsafe_bb = FxHashSet::<u32>::default();

    // Collect the Local of unsafe args and the BB of unsafe calls.
    for def_site in unsafe_sources {
        match def_site {
            DefSite::Arg(arg) => {
                unsafe_locals.insert(Local::from_u32(*arg));
            },
            DefSite::HeapAlloc(bb) | DefSite::OtherCall(bb) => {
                unsafe_bb.insert(*bb);
            },
            _ => {
                panic!("Native call should not be here");
            }
        }
    }

    // Get the LHS Place of unsafe calls.
    for (bb, bbd) in body.basic_blocks().iter_enumerated() {
        if unsafe_bb.contains(&bb.as_u32()) {
            // This bb ends with an unsafe call.
            match &bbd.terminator().kind {
                TerminatorKind::Call {func: _, args: _, destination, ..} => {
                    unsafe_locals.insert(destination.local);
                },
                _ => {
                    panic!("Should be a call");
                }
            }
        }
    }

    // Flow-insensitive data-flow analysis to find more unsafe places.
    let mut change = true;
    while change {
        change = false;
        for (_, bbd) in body.basic_blocks().iter_enumerated() {
            for (_, stmt) in bbd.statements.iter().enumerate() {
                match &stmt.kind {
                    StatementKind::Assign(box (lhs_place, rvalue)) => {
                        let mut place_in_rvalue = Vec::<Place<'tcx>>::new();
                        get_place_in_rvalue(&rvalue, &mut place_in_rvalue);
                        for place in place_in_rvalue {
                            if unsafe_locals.contains(&place.local) {
                                if unsafe_locals.insert(lhs_place.local) {
                                    change = true;
                                }
                                break;
                            }
                        }
                    },
                    _ => {}
                }
            }
        }
    }
    // Remove the return value Place.
    unsafe_locals.remove(&Local::from_u32(0));

    unsafe_locals
}

/// Check a Place to get the dereference to an unsafe Place, if there is one.
///
/// Questions: It is true that a Place has at most one dereference?
fn get_place_unsafe_deref<'tcx>(place: &Place<'tcx>,
                                stmt_unsafe_locals: &mut Vec<u32>,
                                unsafe_locals: &FxHashSet<Local>,
                                deref_num: &mut u32) {
    let mut deref_in_place: u32 = 0;
    for place_elem in place.projection {
        match place_elem {
            ProjectionElem::Deref => { deref_in_place += 1;}
            _ => {}
        }
    }
    if deref_in_place == 0 {
        return;
    }

    *deref_num += deref_in_place;
    assert!(deref_in_place < 2, "Place has multiple deref");

    let local = place.local;
    if unsafe_locals.contains(&local) {
        stmt_unsafe_locals.push(local.as_u32());
    }
}

/// Examine each statement and terminator to find unsafe memory accesses.
/// An unsafe memory access is defined as a dereference to an unsafe Place.
fn find_unsafe_accesses<'tcx>(unsafe_locals: FxHashSet<Local>, fn_id: FnID,
                              body: &'tcx Body<'tcx>, total_deref: &mut u32)
                              -> UnsafeAccesses {
    // Result.
    let mut unsafe_accesses = Vec::<UnsafeAccess>::new();

    // Total number of dereferences to Place in this function.
    let mut deref_num: u32 = 0;

    for (bb, bbd) in body.basic_blocks().iter_enumerated() {
        for (i, stmt) in bbd.statements.iter().enumerate() {
            // Handle a Statement.
            let mut places = Vec::new();
            get_place_in_stmt(stmt, &mut places);
            let mut stmt_unsafe_locals = Vec::new();
            for place in &places {
                get_place_unsafe_deref(place, &mut stmt_unsafe_locals,
                                       &unsafe_locals, &mut deref_num)
            }
            if !stmt_unsafe_locals.is_empty() {
                let unsafe_access = UnsafeAccess {
                    _bb: bb.as_u32(),
                    _index: i as u32,
                    _is_terminator: false,
                    locals: stmt_unsafe_locals,
                };
                unsafe_accesses.push(unsafe_access);
            }
        }

        // Handle Terminator
        let mut places = Vec::new();
        get_place_in_terminator(body, &bbd.terminator(), &mut places);
        let mut term_unsafe_locals = Vec::new();
        for place in &places {
            get_place_unsafe_deref(place, &mut term_unsafe_locals,
                                   &unsafe_locals, &mut deref_num);
        }
        if !term_unsafe_locals.is_empty() {
            let unsafe_access = UnsafeAccess {
                _bb: bb.as_u32(),
                _index: bbd.statements.len() as u32,
                _is_terminator: true,
                locals: Vec::new()
            };
            unsafe_accesses.push(unsafe_access);
        }
    }

    *total_deref += deref_num;

    (fn_id, unsafe_accesses)
}

/// Count the total number of unsafe accesses in the whole crate.
pub fn unsafe_access_num(unsafe_accesses_all: &Vec::<UnsafeAccesses>) -> usize {
    let mut unsafe_deref_num = 0;
    for unsafe_accesses in unsafe_accesses_all {
        for unsafe_access in &unsafe_accesses.1 {
            unsafe_deref_num += unsafe_access.locals.len();
        }
    }

    unsafe_deref_num
}

/// Count the memory accesses in this fn, and update total_deref.
fn count_access_in_fn<'tcx>(body: &'tcx Body<'tcx>, total_deref: &mut u32) {
    let mut access_num: u32 = 0;
    let mut places = Vec::new();
    for (_bb, bbd) in body.basic_blocks().iter_enumerated() {
        for (_, stmt) in bbd.statements.iter().enumerate() {
            get_place_in_stmt(stmt, &mut places);
        }
        get_place_in_terminator(body, &bbd.terminator(), &mut places);
    }

    for place in places {
        for place_elem in place.projection {
            match place_elem {
                ProjectionElem::Deref => { access_num += 1; }
                _ => {}
            }
        }
    }
    *total_deref += access_num;
}

/// Entrance of this module.
///
/// Local analysis to find unsafe memory accesses. It uses the three types of
/// unsafe sources (arg, heap-alloc call, and non-heap-alloc call) from
/// previous whole-program analysis.
pub fn analyze<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId,
                     unsafe_sources_all: &WPSummary,
                     unsafe_accesses_all: &mut Vec::<UnsafeAccesses>,
                     total_deref: &mut u32) {
    if ignore_fn(tcx, def_id) {
        return;
    }

    let fn_id = get_fn_fingerprint(tcx, def_id);
    let body = tcx.optimized_mir(def_id);
    let unsafe_sources = unsafe_sources_all.get(&fn_id);
    if unsafe_sources.is_none() {
        // This function does not have any unsafe resources. We just count its
        // memory dereferences.
        count_access_in_fn(body, total_deref);
        return;
    }

    // Collect all unsafe Place (represented in Local) based on unsafe sources.
    let unsafe_locals = collect_unsafe_locals(unsafe_sources.unwrap(), &body);

    // Find all unsafe accesses.
    let unsafe_accesses = find_unsafe_accesses(unsafe_locals, fn_id, &body,
                                               total_deref);

    unsafe_accesses_all.push(unsafe_accesses);
}
