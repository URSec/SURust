//! Library functions for the sandboxing unsafe code module.

use rustc_middle::mir::*;
use rustc_middle::ty::{self, TyCtxt, Ty};
use rustc_hir::def_id::{DefId,DefIndex,CrateNum,LOCAL_CRATE};
use rustc_data_structures::fx::{FxHashSet};
use nix::unistd::getppid;

use super::database::*;
use super::debug::*;
use super::summarize_fn::{DefSite,FnID};

#[inline(always)]
pub(crate) fn get_crate_name(def_id: DefId) -> String {
    ty::tls::with(|tcx| {
        return tcx.crate_name(def_id.krate).to_ident_string();
    })
}

#[inline(always)]
pub(crate) fn get_fn_name(def_id: DefId) -> String {
    ty::tls::with(|tcx| {
        match tcx.opt_item_name(def_id) {
            Some(name) => { name.to_ident_string() }
            None => { "closure_or_other_no_name_item".to_owned() }
        }
    })
}

/// Get the name of the currently compiled crate.
#[inline(always)]
pub(crate) fn get_local_crate_name() -> String {
    ty::tls::with(|tcx| {
        return tcx.crate_name(LOCAL_CRATE).to_ident_string();
    })
}

/// A helper function that filters out uninterested functions.
#[allow(dead_code)]
pub(crate) fn ignore_fn_dev<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> bool {
    if ignore_fn(tcx, def_id) {
        return true;
    }

    let name = tcx.opt_item_name(def_id);
    if name.is_none() {
        return true;
    }

    let name = name.unwrap();
    // The second condition is for debugging and development only.
    if name.is_empty() || !FN_TO_PROCESS.contains(&name.to_ident_string()) {
        return true;
    }

    return false;
}

/// Checks if a fn is a compiler builtin or from the native libraries such as
/// std in the "rust/library" directory.
///
/// Question: Do we need exclude all the crates in "rust/library"?
#[inline(always)]
pub(crate) fn ignore_fn<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> bool {
    // Ignore compiler builtins.
    if tcx.is_compiler_builtins(def_id.krate) {
        return true;
    }

    // Ignore standard and builtin libraries.
    let crate_name = get_crate_name(def_id);
    if NATIVE_LIBS.contains(&crate_name) { return true; }

    // Ignore functions without a name.
    // Jie Zhou: What are these functions exactly?
    let fn_name = tcx.opt_item_name(def_id);
    if fn_name.is_none() { return true; }
    if fn_name.unwrap().is_empty() { return true; }

    // Ignore main() from build_script_build
    if ignore_build_crate(&crate_name) { return true; }

    return false;
}

/// Ignore crates from build.rs.
/// Any others?
#[inline(always)]
pub(crate) fn ignore_build_crate(name: &str) -> bool {
    return name == "build_script_build" || name == "build_script_main";
}

/// Get the Place in an Operand.
#[inline(always)]
pub(crate) fn get_place_in_operand<'tcx>(operand: &Operand<'tcx>,
                                         places: &mut Vec<Place<'tcx>>) {
    match operand {
        // Should we ignore temporary values?
        Operand::Copy(place) => {
            places.push(*place);
        },
        Operand::Move(place) => {
            places.push(*place);
        },
        Operand::Constant(_) => {}
    }
}

/// Get the Place(s) in a Rvalue.
///
/// TODO? It seems that it is more convenient to let this function return
/// a vector of Place in rvalue.
pub(crate) fn get_place_in_rvalue<'tcx>(rvalue: &Rvalue<'tcx>,
                                        places: &mut Vec<Place<'tcx>>) {
    match rvalue {
        Rvalue::Use(operand) => {
            get_place_in_operand(operand, places);
        },
        Rvalue::Repeat(operand, _num) => {
           get_place_in_operand(operand, places);
        },
        Rvalue::Ref(_, _, place) => {
            places.push(*place);
        },
        Rvalue::ThreadLocalRef(_def_id) => {
            // Ignore TLS
        },
        Rvalue::AddressOf(_, place) => {
            places.push(*place);
        },
        Rvalue::Len(place) => {
            places.push(*place);
        },
        Rvalue::Cast(_, operand, _) => {
           get_place_in_operand(operand, places);
        },
        Rvalue::BinaryOp(_, box (ref lhs, ref rhs))
        | Rvalue::CheckedBinaryOp(_, box (ref lhs, ref rhs)) => {
           get_place_in_operand(lhs, places);
           get_place_in_operand(rhs, places);
        },
        Rvalue::UnaryOp(_, operand) => {
           get_place_in_operand(operand, places);
        },
        Rvalue::Discriminant(place) => {
            places.push(*place);
        },
        Rvalue::Aggregate(_, operands) => {
            // Do we need to collect each field? Or should we just find out the
            // single allocation site for the whole aggregate, if that is
            // represented in MIR?
            for operand in operands {
                get_place_in_operand(operand, places);
            }
        },
        Rvalue::ShallowInitBox(operand, _) => {
            get_place_in_operand(operand, places);
        },
        _ => {}
    }
}

/// A helper function that collects Local of Place in the arguments of a fn call.
///
/// Inputs:
/// @args: The args of a TerminatorKind::Call.
/// @locals: Destination for the Local of Place in @args.
#[inline(always)]
pub(crate) fn get_local_in_args<'tcx>(args: &Vec<Operand<'tcx>>,
                                      locals: &mut FxHashSet<Local>) {
    let mut places = Vec::<Place<'tcx>>::with_capacity(args.len());
    args.iter().for_each(|arg| get_place_in_operand(arg, &mut places));
    for place in places { locals.insert(place.local); }
}

/// A helper function that collects the Local of Place in a Rvalue.
///
/// Inputs:
/// @rvalue: The target Rvalue.
/// @locals: Destination for the Local of Place in @rvalue.
#[inline(always)]
pub(crate) fn get_local_in_rvalue<'tcx>(rvalue: &Rvalue<'tcx>,
                                        locals: &mut FxHashSet<Local>) {
    let mut places = Vec::new();
    get_place_in_rvalue(rvalue, &mut places);
    for place in places { locals.insert(place.local); }
}


/// Check if a type is the empty type, i.e., '()'.
pub(crate) fn is_empty_ty<'tcx>(t: Ty<'tcx>) -> bool {
    if let ty::Tuple(tys) = t.kind() {
        if tys.len() == 0 { return true; }
    }

    return false;
}

/// Get a function's DefId from a function Constant.
#[allow(dead_code)]
pub(crate) fn get_callee_id_local<'tcx>(f: &Constant<'tcx>) -> DefId {
    if let ty::FnDef(def_id, _) = *f.literal.ty().kind() {
        return def_id;
    }

    panic!("Not a function");
}

/// Break a DefId into a tuple of its DefIndex and CrateNum.
pub(crate) fn break_def_id(def_id: DefId) -> (u32, u32) {
    (def_id.index.as_u32(), def_id.krate.as_u32())
}

/// Create a DefId based on two u32 as DefIndex and CrateNum, respectively.
pub(crate) fn assemble_def_id((index, krate): (u32, u32)) -> DefId {
    DefId {
        index: DefIndex::from_u32(index),
        krate: CrateNum::from_u32(krate)
    }
}

/// Get the directory that contains all the summary files.
///
/// We assume that a Rust project is built by invoking `cargo`. The getppid()
/// would therefore be the pid of the cargo process.
pub(crate) fn get_summary_dir() -> String {
    return "/tmp/rust-sandbox-".to_owned() + &getppid().to_string();
}

/// Get the path of the whole-program summary.
///
/// TODO: Now we write it to "/tmp/rust-sandbox-summary" beause we still haven't
/// solved the synchronization between the analysis results of dependece crates
/// and the binary crate. Once that is solved, we should write it to
/// "/tmp/rust-sandbox-".to_owned() + &getppid().to_string() + "-summary""
pub(crate) fn get_wp_summary_path() -> String {
    return "/tmp/rust-sandbox-summary".to_owned();
}

/// Create a DefSite from a function call.
pub(crate) fn def_site_from_call<'tcx>(f: &Constant<'tcx>, bb_index: u32)
    -> DefSite {
    if let ty::FnDef(def_id, _) = *f.literal.ty().kind() {
        if NATIVE_LIBS.contains(&get_crate_name(def_id)) {
            if HEAP_ALLOC.contains(&get_fn_name(def_id)) {
                return DefSite::HeapAlloc(bb_index);
            } else {
                return DefSite::NativeCall(bb_index);
            }
        } else {
            return DefSite::OtherCall(bb_index);
        }
    }

    panic!("Not a function");
}

/// Get the inner value of DefPathHash (Fingerprint) of a function.
pub(crate) fn get_fn_fingerprint<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> FnID {
    FnID(tcx.def_path_hash(def_id).0.as_value())
}


/// Extract Place in a Statement.
pub(crate) fn get_place_in_stmt<'tcx>(stmt: &Statement<'tcx>,
                                      places: &mut Vec::<Place<'tcx>>) {
    match &stmt.kind {
        StatementKind::Assign(box (place, rvalue)) => {
            places.push(*place);
            get_place_in_rvalue(rvalue, places);
            // Will the "box ..." syntax creates a new heap object?
            // If so this might be too slow.
        },
        StatementKind::FakeRead(box (_cause, _place)) => {
            print_stmt("FakeRead", stmt);
            // TODO?: Handle FakeRead
            panic!("Need to examine this FakeRead");
        },
        StatementKind::SetDiscriminant {box place, ..} => {
            places.push(*place);
        },
        StatementKind::Deinit(box place) => {
            places.push(*place);
        },
        StatementKind::Retag(_, box place) => {
            // What exactly is a retag inst?
            print_stmt("Retag", stmt);
            places.push(*place);
        },
        StatementKind::AscribeUserType(box (place, _), _) => {
            // What exactly is an AscribeUserType? And the doc says this will
            // be an nop at execution time; do we need to handle it?
            print_stmt("AscribeUserType", stmt);
            places.push(*place);
        },
        StatementKind::CopyNonOverlapping(box cno) => {
            get_place_in_operand(&cno.src, places);
            get_place_in_operand(&cno.dst, places);
            // Do we really need to record the place of the count arg?
            get_place_in_operand(&cno.count, places);
        },
        StatementKind::StorageLive(_)
            | StatementKind::StorageDead(_)
            | StatementKind::Coverage(_)
            | StatementKind::Nop => { }
    }
}

/// Extract Place in a Terminator.
pub(crate) fn get_place_in_terminator<'tcx>(body: &'tcx Body<'tcx>,
                                 terminator: &Terminator<'tcx>,
                                 places: &mut Vec::<Place<'tcx>>) {
    match &terminator.kind {
        TerminatorKind::SwitchInt{discr, ..} => {
            get_place_in_operand(discr, places);
        },
        TerminatorKind::Drop{place, ..} => {
            places.push(*place);
        },
        TerminatorKind::DropAndReplace{place, value, ..} => {
            places.push(*place);
            get_place_in_operand(value, places);
        },
        TerminatorKind::Call{func: _, args, destination, ..} => {
            // For some unknown reason(s), sometimes printing a Call in println!
            // will crash the compiler.
            for arg in args {
                get_place_in_operand(arg, places);
            }
            // Get the Place of the LHS if the call returns something.
            if is_empty_ty(body.local_decls[destination.local].ty) {
                // Ignore return type of "()".
                return;
            }
            // Question: Should we ignore all locals, i.e., Place whose
            // projection is empty?
            places.push(*destination);
        },
        TerminatorKind::Assert{cond, ..} => {
            // Do we need to handle assertions?
            get_place_in_operand(cond, places);
        },
        TerminatorKind::Yield{value, resume: _, resume_arg, ..} => {
            get_place_in_operand(value, places);
            places.push(*resume_arg);
        },
        _ => {}
    }
}


