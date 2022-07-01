//! Library functions for the sandboxing unsafe code project.

use rustc_middle::mir::*;
use rustc_middle::ty::{self, TyCtxt};
use rustc_hir::def_id::{DefId};
use rustc_data_structures::fx::{FxHashSet};

use super::database::*;
use super::debug::*;

#[inline(always)]
crate fn get_crate_name(tcx: TyCtxt<'tcx>, def_id: DefId) -> String {
    return tcx.crate_name(def_id.krate).to_ident_string();
}

#[inline(always)]
#[allow(dead_code)]
crate fn get_fn_name(f: &Constant<'tcx>) -> String {
    ty::tls::with(|tcx| {
        return tcx.opt_item_name(get_fn_def_id(f)).unwrap().name.to_string();
    })
}

/// A helper function that filters out uninterested functions.
#[allow(dead_code)]
crate fn ignore_fn_dev(tcx: TyCtxt<'tcx>, def_id: DefId) -> bool {
    if ignore_fn(tcx, def_id) {
        return true;
    }

    let name = tcx.opt_item_name(def_id);
    if name.is_none() {
        return true;
    }

    let name = name.unwrap().name;
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
crate fn ignore_fn(tcx: TyCtxt<'tcx>, def_id: DefId) -> bool {
    // Ignore compiler builtins.
    if tcx.is_compiler_builtins(def_id.krate) {
        return true;
    }

    // Ignore standard and builtin libraries.
    let crate_name = get_crate_name(tcx, def_id);
    if BUILTIN_LIB.contains(&crate_name) { return true; }

    // Ignore functions without a name.
    // Jie Zhou: What are these functions exactly?
    let fn_name = tcx.opt_item_name(def_id);
    if fn_name.is_none() { return true; }
    if fn_name.unwrap().name.is_empty() { return true; }

    // Ignore main() from build_script_build
    if crate_name == "build_script_build" { return true; }

    return false;
}

/// Get the Place in an Operand.
#[inline(always)]
crate fn get_place_in_operand(operand: &Operand<'tcx>, places: &mut Vec<Place<'tcx>>) {
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
crate fn get_place_in_rvalue(rvalue: &Rvalue<'tcx>, places: &mut Vec<Place<'tcx>>) {
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
crate fn get_local_in_args(args: &Vec<Operand<'tcx>>, locals: &mut FxHashSet<Local>) {
    let mut places = Vec::<Place<'tcx>>::with_capacity(args.len());
    args.iter().for_each(|arg| get_place_in_operand(arg, &mut places));
    for place in places { locals.insert(place.local); }
}

/// A helper function that collects the Locao of Place in a Rvalue.
///
/// Inputs:
/// @rvalue: The target Rvalue.
/// @locals: Destination for the Local of Place in @rvalue.
#[inline(always)]
crate fn get_local_in_rvalue(rvalue: &Rvalue<'tcx>, locals: &mut FxHashSet<Local>) {
    let mut places = Vec::new();
    get_place_in_rvalue(rvalue, &mut places);
    for place in places { locals.insert(place.local); }
}


/// Get the Local of the Place of the return value of a function call, if it
/// does not return an empty tuple or diverts.
crate fn get_ret_local(ret: &Option<(Place<'tcx>, BasicBlock)>,
                       body: &Body<'tcx>) -> Option<Local> {
    if let Some((place, _)) = ret {
        if let ty::Tuple(tys) = body.local_decls[place.local].ty.kind() {
            // Empty return value "()".
            if tys.len() == 0 { return None; }
            else { return Some(place.local); }
        }
        return Some(place.local);
    }

    None
}

/// Get a function's DefId from a function Constant.
#[inline(always)]
crate fn get_fn_def_id(f: &Constant<'tcx>) -> DefId {
    if let ty::FnDef(def_id, _) = *f.literal.ty().kind() {
        return def_id;
    }

    panic!("Not a function");
}

/// Break a DefId into a tuple of its DefIndex and CrateNum.
#[inline(always)]
crate fn break_def_id(def_id: DefId) -> (u32, u32) {
    (def_id.index.as_u32(), def_id.krate.as_u32())
}
