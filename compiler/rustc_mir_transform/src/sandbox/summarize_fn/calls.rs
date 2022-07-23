//! Analyze each function to find its callees, the definition site(s) of each
//! argument of each callee, and def site(s) for the return value.

use rustc_middle::mir::*;
use rustc_middle::ty::{TyCtxt};
use rustc_hir::def_id::{DefId};
use rustc_data_structures::fx::{FxHashSet, FxHashMap};
use serde::{Deserialize, Serialize};
use std::fmt;

use crate::sandbox::utils::*;
use super::{DefSite, Summary, FnID};

static _DEBUG: bool = false;

/// Information of a callee used by a function. Speficially, we collect the
/// allocation/declaration sites for all the arguments of a callee. Note that
/// we do not need to distinguish each call to the same callee.
#[derive(Serialize, Deserialize)]
crate struct Callee {
    /// Unique ID of a function that is stable across compilation sessions.
    crate fn_id: FnID,
    pub fn_name: String,
    pub crate_name: String,
    /// DefId (DefIndex, CrateNum)
    crate def_id: (u32, u32),
    /// The basic block of a call and def sites for each argument. For example,
    /// (bb3, [[bb0, bb1], [bb2, _2]]) means the callee is called at BB3, and
    /// the call has two arguments, and the first argument is computed from the
    /// Terminator of BB0 and BB1, and the second is from the Terminator of bb2
    /// and argument _2.
    arg_defs: FxHashMap<u32, Vec<FxHashSet<DefSite>>>,
}

impl fmt::Debug for Callee {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} (ID:{:?}; arg_defs: {:?}", self.fn_name, self.def_id,
            self.arg_defs)
    }
}

/// Get the target Callee by DefId from the vector of Callee used by a fn.
///
/// This may not be that slow as it looks because a function usually only has
/// a limited number of callees. We did not use a HashSet for Summary.callees
/// because HashSet does not support get_mut(). We also did not use
/// HashMap<DefId, Callee> because serializing it will generate illegal JSON
/// ("key must be a string").
#[inline(always)]
fn get_callee(callees: &mut Vec<Callee>, def_id: DefId) -> Option<&mut Callee> {
    for callee in callees.iter_mut() {
        if break_def_id(def_id) == callee.def_id {
            return Some(callee);
        }
    }

    None
}

/// Update Callee.arg_defs by adding a new DefSite.
///
/// Inputs:
/// @call: The (BasicBlock, DefId) of the target callee.
/// @index: Index of the argument in Callee.arg_defs.
/// @site: A new DefSite
/// @summary: Summary.
#[inline(always)]
fn update_arg_defs(call: (u32, DefId), index: usize, site: DefSite,
                   summary: &mut Summary) {
    let callee = get_callee(&mut summary.callees, call.1).unwrap();
    // The next unwrap is safe as analyze_fn() processes each call.
    let callee_arg_defs = callee.arg_defs.get_mut(&call.0).unwrap();
    callee_arg_defs[index].insert(site);
}

/// Get the Local of the Place of the return value of a function call, if it
/// does not return an empty tuple or diverts.
#[inline(always)]
fn get_non_empty_ret(ret: &Option<(Place<'tcx>, BasicBlock)>, body: &Body<'tcx>)
   -> Option<Local> {
    if let Some((place, _)) = ret {
        if is_empty_ty(body.local_decls[place.local].ty) {
            return None;
        } else {
            return Some(place.local);
        }
    }

    None
}

/// Core procedure of finding definition sites of each argument of a fn call.
/// It first examines a basic block backwards, and then recursively examines
/// the BB's predecessors. It is similar to unsafe_def::find_unsafe_def_core.
///
/// Inputs:
/// @bb: Currently processed BasicBlock.
/// @body: Body of the processed function.
/// @call: (BasicBlock, DefId) of the currently processed call of a callee.
/// @locals: Local (Place) that contributes to the arguments of the call.
/// @visited: Already processed BB.
/// @summary: Summary of the target function.
fn find_arg_def(bb: BasicBlock, body: &Body<'tcx>,
                call: (u32, DefId),
                locals: &mut Vec<FxHashSet<Local>>,
                visited: &mut FxHashSet<BasicBlock>,
                summary: &mut Summary) {
    if !visited.insert(bb) || locals.is_empty() { return; }

    let bbd = &body.basic_blocks()[bb];
    let bb_index = bb.as_u32();
    // Process Terminator
    if let TerminatorKind::Call{func: Operand::Constant(f), args, destination,
        ..} = &bbd.terminator().kind {
        if let Some(call_ret) = get_non_empty_ret(destination, body) {
            // Found a potential definition site from a function call.
            for i in 0..locals.len() {
                let arg_locals = &mut locals[i];
                if arg_locals.contains(&call_ret) {
                    arg_locals.remove(&call_ret);
                    let def_site = def_site_from_call(f, bb_index);
                    match def_site {
                        DefSite::HeapAlloc(_) => {
                            update_arg_defs(call, i, def_site, summary);
                        },
                        DefSite::NativeCall(_) => {
                            get_local_in_args(args, arg_locals);
                        },
                        DefSite::OtherCall(_) => {
                            get_local_in_args(args, arg_locals);
                            update_arg_defs(call, i, def_site, summary);
                        },
                        _ => {}
                    }
                }
            }
        }
    }

    // Process each Statement backward.
    for i in (0..bbd.statements.len()).rev() {
        let stmt = &bbd.statements[i];
        match &stmt.kind {
            StatementKind::Assign(box (place, rvalue)) => {
                for arg_locals in locals.iter_mut() {
                    let local = place.local;
                    if arg_locals.contains(&local) {
                        arg_locals.remove(&local);
                        get_local_in_rvalue(rvalue, arg_locals);
                    }
                }
            },
            _ => {
                // Any other cases to handle?
            }
        }
    }

    // Recursively examine the current BB's predecessors.
    let predecessors = &body.predecessors()[bb];
    for pbb in predecessors {
        if predecessors.len() > 1 {
            find_arg_def(*pbb, body, call, &mut locals.clone(),
                         visited, summary);
        } else {
            find_arg_def(*pbb, body, call, locals, visited, summary);
        }
    }

    // After examine the first BB, check if any function arguments
    // contribute to the definition/declaration of function call arguments.
    if bb.index() == 0 {
        for i in 0..locals.len() {
            let arg_locals = &mut locals[i];
            for arg in body.args_iter() {
                if arg_locals.contains(&arg) {
                    arg_locals.remove(&arg);
                    update_arg_defs(call, i, DefSite::Arg(arg.as_u32()), summary);
                }
            }
        }
    }
}

/// Core procedure of finding the def sites for the return value of a fn.
///
/// Inputs:
/// @loc: Location of the Statement/Terminator from which to iterate backward.
/// @locals: Local of Place that contribute to the target return value.
/// @body: Body of the target function.
/// @visited: Processed BasicBlock.
/// @summary: Summary.
fn find_ret_def(loc: &Location, locals: &mut FxHashSet<Local>, body: &Body<'tcx>,
                visited: &mut FxHashSet<BasicBlock>, summary: &mut Summary) {
    let bb = loc.block;
    if visited.contains(&bb) || locals.is_empty() { return; }
    visited.insert(bb);

    let mut start_index = loc.statement_index;
    let bbd = &body.basic_blocks()[bb];
    let stmt_num = bbd.statements.len();
    if start_index == stmt_num {
        // Examine the BB starting from the Terminator.
        if let TerminatorKind::Call{func: Operand::Constant(f), args,
            destination, ..} = &bbd.terminator().kind {
            if let Some(local) = get_non_empty_ret(destination, body) {
                if locals.contains(&local) {
                    locals.remove(&local);
                    let def_site = def_site_from_call(f, bb.as_u32());
                    match def_site {
                        DefSite::HeapAlloc(_) => {
                            summary.ret_defs.0.insert(def_site);
                        },
                        DefSite::NativeCall(_) => {
                            get_local_in_args(args, locals);
                            // Should def_site be put to summary.ret_defs?
                        },
                        DefSite::OtherCall(_) => {
                            get_local_in_args(args, locals);
                            summary.ret_defs.0.insert(def_site);
                        }
                        _ => {}
                    }
                }
            }
        }
    } else {
        // This means we need to examine starting from a Statement.
        start_index += 1;
    }

    // Examine each Statement backward
    for i in (0..start_index).rev() {
        match &bbd.statements[i].kind {
            StatementKind::Assign(box (place, rvalue)) => {
                let local = place.local;
                if local.as_u32() == 0 || locals.contains(&local) {
                    locals.remove(&local);
                    get_local_in_rvalue(rvalue, locals);
                }
            },
            _ => {}
        }
    }

    // Examine bb's predecessors recursively.
    let predecessors = &body.predecessors()[bb];
    for pbb in predecessors {
        let loc = Location { block: *pbb,
            statement_index: body.basic_blocks()[*pbb].statements.len()};
        if predecessors.len() > 1 {
            find_ret_def(&loc, &mut locals.clone(), body, visited, summary);
        } else {
            find_ret_def(&loc, locals, body, visited, summary);
        }
    }

    // Check if any argument contributes to the return value.
    if bb.index() == 0 && !locals.is_empty() {
        body.args_iter().for_each(|arg|
            if locals.contains(&arg) {
                summary.ret_defs.1.push(DefSite::Arg(arg.as_u32()));
            });
    }
}

/// Check if the destination of a call is the return value of the caller.
/// When this function is called, it is certain that dest is not an empty type.
#[inline(always)]
fn dest_to_ret(dest: &Option<(Place<'tcx>, BasicBlock)>)
    -> bool {
    if let Some((place, _)) = dest {
        if place.local.index() != 0 { return false; }
        return true;
    }

    false
}

/// Add a new pair of (bb, arg_defs) to a Calle's arg_defs.
#[inline(always)]
fn add_arg_def_slot(bb_arg_defs: &mut FxHashMap<u32, Vec::<FxHashSet<DefSite>>>,
                    args: &Vec<Operand<'tcx>>, bb_index: u32) {
    let mut arg_defs = Vec::with_capacity(args.len());
    for _ in 0..args.len() {
        arg_defs.push(FxHashSet::default());
    }
    bb_arg_defs.insert(bb_index, arg_defs);
}

/// Analyze a function to find:
/// 1. Its callees and the definition sites of the arguments of each callee.
/// 2. The definition sites for its return value, if there is one.
pub(super)
fn analyze_fn(tcx: TyCtxt<'tcx>, body: &Body<'tcx>, summary: &mut Summary) {
    // BB that end with a call.
    let mut bb_with_calls = Vec::new();
    // Location of return value's def stmt and Local that contribute to it.
    let mut ret_defs = FxHashMap::<Location, FxHashSet::<Local>>::default();
    // Prepare data:
    // 1. BB with a call.
    // 2. BB with return value definition.
    for (bb, bbd) in body.basic_blocks().iter_enumerated() {
        let terminator = &bbd.terminator();
        let bb_index = bb.as_u32();
        if let TerminatorKind::Call{func: Operand::Constant(f), args,
            destination, ..} = &terminator.kind {
            bb_with_calls.push(bb);
            // Prepare arg_defs of Callee.
            let callee_id = get_fn_def_id(f);
            if !args.is_empty() {
                if let Some(callee) = get_callee(&mut summary.callees, callee_id) {
                    add_arg_def_slot(&mut callee.arg_defs, args, bb_index);
                } else {
                    let mut bb_arg_defs = FxHashMap::default();
                    add_arg_def_slot(&mut bb_arg_defs, args, bb_index);
                    summary.callees.push(Callee {
                        fn_id: get_fn_fingerprint(tcx, callee_id),
                        fn_name: get_fn_name(callee_id),
                        crate_name: get_crate_name(callee_id),
                        def_id: break_def_id(callee_id),
                        arg_defs: bb_arg_defs
                    });
                }
            }

            // Prepare for return value.
            if !is_empty_ty(body.return_ty()) && dest_to_ret(destination) {
                let loc = Location {
                    block: bb, statement_index: bbd.statements.len()
                };
                let mut locals = FxHashSet::<Local>::default();
                get_local_in_args(args, &mut locals);
                ret_defs.insert(loc, locals);
            }
            continue;
        }

        // Continue to prepare for return value.
        for i in 0..bbd.statements.len() {
            match &bbd.statements[i].kind {
                StatementKind::Assign(box (place, rvalue)) => {
                    if place.local.as_u32() == 0 {
                        // Found a def site for the return.
                        let loc = Location { block: bb, statement_index: i };
                        let mut locals = FxHashSet::<Local>::default();
                        get_local_in_rvalue(rvalue, &mut locals);
                        ret_defs.insert(loc, locals);
                        // There should be at most one ret def ("_0 = ...")
                        // in a BB so it should be safe to break from here.
                        break;
                    }
                },
                _ => {}
            }
        }
    }

    // Process each function call to find the def sites of its arguments.
    for bb in bb_with_calls {
        if let TerminatorKind::Call{func: Operand::Constant(f), args, ..} =
            &body.basic_blocks()[bb].terminator().kind {
            // Recorded visited BB to prevent infite recursions due to loops.
            let mut visited = FxHashSet::<BasicBlock>::default();
            // Local of the Place that contribute to function call arguments.
            let mut locals = Vec::<FxHashSet::<Local>>::with_capacity(args.len());
            // Collect the initial Local for each argument.
            for arg in args {
                let mut places = Vec::new();
                let mut arg_locals = FxHashSet::default();
                get_place_in_operand(arg, &mut places);
                for place in places { arg_locals.insert(place.local); }
                locals.push(arg_locals);
            }
            // Enter the core procedure of finding def sites for fn args.
            find_arg_def(bb, body, (bb.as_u32(), get_fn_def_id(f)), &mut locals,
                         &mut visited, summary);
        } else {
            panic!("Not a function");
        }
    }

    // Process the return value to find its def sites.
    for (loc, mut locals) in ret_defs {
        let mut visited = FxHashSet::<BasicBlock>::default();
        find_ret_def(&loc, &mut locals, body, &mut visited, summary);
    }
}
