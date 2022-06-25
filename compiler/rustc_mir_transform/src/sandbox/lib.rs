//! Library functions for the sandboxing unsafe code project.

use rustc_middle::mir::*;
use rustc_middle::ty::{self, TyCtxt};
use rustc_hir::def_id::{DefId};

use super::database::*;
use super::debug::*;

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
    if tcx.is_compiler_builtins(def_id.krate) {
        return true;
    }

    let crate_name = tcx.crate_name(def_id.krate).to_ident_string();
    if BUILTIN_LIB.contains(&crate_name) { return true; }

    let fn_name = tcx.opt_item_name(def_id);
    if fn_name.is_none() { return true; }
    if fn_name.unwrap().name.is_empty() { return true; }

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
