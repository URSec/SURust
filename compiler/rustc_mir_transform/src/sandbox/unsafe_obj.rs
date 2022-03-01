use rustc_middle::mir::*;
use rustc_middle::ty::{TyCtxt};
use rustc_hir::def_id::{DefId};
use rustc_data_structures::fx::{FxHashSet};

use super::debug::*;

/// An unsafe operation (a statement or a terminator) in an unsafe block/fn.
struct UnsafeOp <'tcx> {
    // All Place used in this statement or terminator
    places: Vec<Place<'tcx>>,
    _stmt: Option<&'tcx Statement<'tcx>>,
    _terminator: Option<&'tcx Terminator<'tcx>>,
    // Location of the statement or terminator
    _location: Location,
}

// Check if a fn, statement, or a terminator is unsafe or in a block.
#[allow(dead_code)]
fn is_unsafe(body: &Body<'tcx>, scope: SourceScope) -> bool {
    match body.source_scopes[scope].local_data.as_ref() {
        ClearCrossCrate::Clear => false,
        ClearCrossCrate::Set(v) => {
            match v.safety {
                Safety::ExplicitUnsafe(_) | Safety::FnUnsafe => true,
                _ => false
            }
        }
    }
}

// A helper function that filters out uninterested functions. This is for
// developement and debug only.
#[allow(dead_code)]
fn ignore_fn(tcx: TyCtxt<'tcx>, def_id: DefId) -> bool {
    let name = tcx.opt_item_name(def_id);
    if name.is_none() {
        return true;
    }
    let name = name.unwrap().name;
    if name.is_empty() || !FN_TO_PROCESS.contains(&name.to_ident_string()) {
        return true;
    }

    return false;
}

/// This function checks if a fn is a compiler builtin or from the native
/// libraries such as std in the "rust/library" directory.
/// Question: Do we need exclude all the crates in "rust/library"?
#[inline(always)]
fn is_builtin_or_std(tcx: TyCtxt<'tcx>, def_id: DefId) -> bool {
    if tcx.is_compiler_builtins(def_id.krate) {
        return true;
    }

    let crate_name = tcx.crate_name(def_id.krate).to_ident_string();
    return crate_name == "core" || crate_name == "std" ||
           crate_name == "alloc" ||
           crate_name == "test" ||
           crate_name == "backtrace";
}

#[inline(always)]
fn get_place_from_operand(operand: &Operand<'tcx>, places: &mut Vec<Place<'tcx>>) {
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

/// Handle StatementKind::Assign separately as the RValue can be complex.
fn get_place_in_rvalue(rvalue: &Rvalue<'tcx>, places: &mut Vec<Place<'tcx>>) {
    match rvalue {
        Rvalue::Use(operand) => {
            get_place_from_operand(operand, places);
        },
        Rvalue::Repeat(operand, _num) => {
           get_place_from_operand(operand, places);
        },
        Rvalue::Ref(_, _, place) => {
            places.push(*place);
        },
        Rvalue::ThreadLocalRef(_def_id) => {
            // TODO: How to deal with this?
            panic!("Unhandled Rvalue::ThreadLocalRef");
        },
        Rvalue::AddressOf(_, place) => {
            places.push(*place);
        },
        Rvalue::Len(place) => {
            places.push(*place);
        },
        Rvalue::Cast(_, operand, _) => {
           get_place_from_operand(operand, places);
        },
        Rvalue::BinaryOp(_, box (ref lhs, ref rhs))
        | Rvalue::CheckedBinaryOp(_, box (ref lhs, ref rhs)) => {
           get_place_from_operand(lhs, places);
           get_place_from_operand(rhs, places);
        },
        Rvalue::UnaryOp(_, operand) => {
           get_place_from_operand(operand, places);
        },
        Rvalue::Discriminant(place) => {
            places.push(*place);
        },
        Rvalue::Aggregate(_, operands) => {
            // Do we need to collect each field? Or should we just find out the
            // single allocation site for the whole aggregate, if that is
            // represented in MIR?
            for operand in operands {
                get_place_from_operand(operand, places);
            }
        },
        Rvalue::ShallowInitBox(operand, _) => {
            get_place_from_operand(operand, places);
        },
        _ => {}
    }
}

/// Handle CopyNonOverlapping separately as it is more complex than most
/// types StatementKind statements.
fn handle_copynonoverlap(_stmt: &CopyNonOverlapping<'tcx>, _places: &mut Vec<Place<'tcx>>) {
    // TODO: Handle CopyNonOverlapping
}

/// Examine each unsafe statement or terminator in unsafe blocks, and find
/// either the corresponding definition point in this function or
/// the declaration for pointers argument.
fn handle_unsafe_op(unsafe_ops: &Vec<Box<UnsafeOp<'tcx>>>, body: &Body<'tcx>) {
    let mut processed = FxHashSet::default();
    let mut places = Vec::new();

    for unsafe_op in unsafe_ops {
        for place in &unsafe_op.places {
            places.push(place);
        }
    }

    println!("[handle_places]");
    for place in places {
        let local = place.local;
        if processed.contains(&local.as_u32()) {
            continue;
        } else {
            processed.insert(local.as_u32());
        }

        match body.local_kind(local) {
            LocalKind::Var => {
                print_local("Var", local);
            },
            LocalKind::Arg => {
                print_local("Argument", local);
            },
            LocalKind::Temp => {
                print_local("Temp", local);
                // TODO
            },
            LocalKind::ReturnPointer => {
                print_local("ReturnPointer", local);
                // TODO
            }
        }
    }

}

/// This function finds the definition or declaration of each memory object
/// used in unsafe code.
///
/// TODO: Currently this function only finds the Place used in each Statement
/// and Terminator, but not the real definition site. A Place can be quite
/// complex. We need analyze each Place to extract the real allocation site.
pub fn find_unsafe_obj(tcx: TyCtxt<'tcx>, def_id: DefId) {
    // Filter out uninterested functions.
   if is_builtin_or_std(tcx, def_id) {
       return;
   }

    let name = tcx.opt_item_name(def_id);
    if name.is_none() || ignore_fn(tcx, def_id) {
        return;
    }

    // Start of the computation.
    println!("[find_unsafe_obj]: Processing {:?}", name);
    let body = tcx.optimized_mir(def_id);

    // Check if this is an unsafe fn.
    if is_unsafe(body, SourceInfo::outermost(body.span).scope) {
        // TODO: Process the whole function.
    }

    let mut unsafe_ops = Vec::new();
    // let mut unsafe_stmts = Vec::new();
    for (bb, data) in body.basic_blocks().iter_enumerated() {
        for (i, stmt) in data.statements.iter().enumerate() {
            if !is_unsafe(body, stmt.source_info.scope) {
                continue;
            }

            let mut unsafe_op = box UnsafeOp {places: Vec::new(),
                _stmt: Some(stmt), _terminator: None,
                _location: Location {block: bb, statement_index: i}};
            match &stmt.kind {
                StatementKind::Assign(box (place, rvalue)) => {
                    print_stmt_assign(stmt, rvalue);
                    unsafe_op.places.push(*place);
                    get_place_in_rvalue(rvalue, &mut unsafe_op.places);
                    // Will the "box ..." syntax creates a new heap object?
                    // If so this might be too slow.
                },
                StatementKind::FakeRead(box (_cause, _place)) => {
                    print_stmt("FakeRead", stmt);
                    // TODO: Handle FakeRead
                    panic!("Need manually examine this FakeRead");
                },
                StatementKind::SetDiscriminant {box place, ..} => {
                    print_stmt("SetDiscriminant", stmt);
                    unsafe_op.places.push(*place);
                },
                StatementKind::Retag(_, box place) => {
                    // What exactly is a retag inst?
                    print_stmt("Retag", stmt);
                    unsafe_op.places.push(*place);
                },
                StatementKind::AscribeUserType(box (place, _), _) => {
                    print_stmt("AscribeUserType", stmt);
                    unsafe_op.places.push(*place);
                },
                StatementKind::CopyNonOverlapping(box copy_non_overlap) => {
                    print_stmt("CopyNonOverlapping", stmt);
                    handle_copynonoverlap(copy_non_overlap, &mut unsafe_op.places);
                },
                StatementKind::StorageLive(_)
                | StatementKind::StorageDead(_)
                | StatementKind::LlvmInlineAsm(_)
                | StatementKind::Coverage(_)
                | StatementKind::Nop => { }

            }
            if !unsafe_op.places.is_empty() {
                unsafe_ops.push(unsafe_op);
            }
        }

        let terminator = &data.terminator();
        if !is_unsafe(body, terminator.source_info.scope) {
            continue;
        }

        let mut unsafe_op = box UnsafeOp {places: Vec::new(),
            _stmt: None, _terminator: Some(terminator),
            _location: Location {block: bb, statement_index: data.statements.len()}};
        match &terminator.kind {
            TerminatorKind::SwitchInt{discr, ..} => {
                print_terminator("SwitchInt", terminator);
                get_place_from_operand(discr, &mut unsafe_op.places);
            },
            TerminatorKind::Drop{place, ..} => {
                unsafe_op.places.push(*place);
            },
            TerminatorKind::DropAndReplace{place, value, ..} => {
                unsafe_op.places.push(*place);
                get_place_from_operand(value, &mut unsafe_op.places);
            },
            TerminatorKind::Call{func: _, args, ..} => {
                // For some unknown reason(s), printing a Call in println! will
                // crash the compiler.
                // What is the Place in "destination: Option<(Place<'tcx>, BasicBlock)"?
                for arg in args {
                    get_place_from_operand(arg, &mut unsafe_op.places);
                }
            },
            TerminatorKind::Assert{cond, ..} => {
                get_place_from_operand(cond, &mut unsafe_op.places);
            },
            TerminatorKind::Yield{value, resume: _, resume_arg, ..} => {
                get_place_from_operand(value, &mut unsafe_op.places);
                unsafe_op.places.push(*resume_arg);
            },
            _ => {}
        }
        if !unsafe_op.places.is_empty() {
            unsafe_ops.push(unsafe_op);
        }
    }

    if !unsafe_ops.is_empty() {
        handle_unsafe_op(&unsafe_ops, body);

        println!("Found {} unsafe statements/terminators", unsafe_ops.len());
    }
}
