use rustc_middle::mir::*;
use rustc_middle::ty::{self, TyCtxt};
use rustc_hir::def_id::{DefId};
use rustc_data_structures::fx::{FxHashSet, FxHashMap};

use super::debug::*;
use super::database::*;

// For debugging purpose.
static _DEBUG: bool = false;

/// An unsafe operation (a statement or a terminator) in an unsafe block/fn.
struct UnsafeOp <'tcx> {
    // All Place used in this statement or terminator.
    // Should we use SmallVec to improve performance?
    places: Vec<Place<'tcx>>,
    // Location of the statement or terminator
    location: Location,
}

#[allow(dead_code)]
enum Operation <'tcx> {
    Stmt(&'tcx Statement<'tcx>),
    Term(&'tcx Terminator<'tcx>)
}

#[allow(dead_code)]
enum UnsafeAllocSite<'tcx> {
    // A heap allocation call, such as Vec::new() or Box::new().
    Alloc(&'tcx Terminator<'tcx>),
    // Returned pointer from a non-heap-alloc function call.
    Ret(&'tcx Terminator<'tcx>),
    // Argument of a function.
    Arg(Local),
}

/// Check if a fn is unsafe, or if a statement/terminator in an unsafe block.
#[allow(dead_code)]
fn is_unsafe(body: &Body<'tcx>, scope: SourceScope) -> bool {
    match body.source_scopes[scope].local_data.as_ref() {
        ClearCrossCrate::Clear => false,
        ClearCrossCrate::Set(v) => {
            match v.safety {
                Safety::ExplicitUnsafe(_) | Safety::FnUnsafe => true,
                // TODO? Handle BuiltinUnsafe?
                _ => false
            }
        }
    }
}

/// A helper function that filters out uninterested functions. This is for
/// developement and debug only.
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

/// Checks if a fn is a compiler builtin or from the native libraries such as
/// std in the "rust/library" directory.
///
/// Question: Do we need exclude all the crates in "rust/library"?
#[inline(always)]
fn is_builtin_or_std(tcx: TyCtxt<'tcx>, def_id: DefId) -> bool {
    if tcx.is_compiler_builtins(def_id.krate) {
        return true;
    }

    let crate_name = tcx.crate_name(def_id.krate).to_ident_string();
    return BUILTIN_LIB.contains(&crate_name);
}

/// Get the Place in an Operand.
#[inline(always)]
fn get_place_in_operand(operand: &Operand<'tcx>, places: &mut Vec<Place<'tcx>>) {
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
fn get_place_in_rvalue(rvalue: &Rvalue<'tcx>, places: &mut Vec<Place<'tcx>>) {
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

/// Extract Place in a Statement.
fn get_place_in_stmt(stmt: &Statement<'tcx>, places: &mut Vec::<Place<'tcx>>) {
    match &stmt.kind {
        StatementKind::Assign(box (place, rvalue)) => {
            places.push(*place);
            get_place_in_rvalue(rvalue, places);
            // Will the "box ..." syntax creates a new heap object?
            // If so this might be too slow.
        },
        StatementKind::FakeRead(box (_cause, _place)) => {
            print_stmt("FakeRead", stmt);
            // TODO: Handle FakeRead?
            panic!("Need manually examine this FakeRead");
        },
        StatementKind::SetDiscriminant {box place, ..} => {
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
            print_stmt("CopyNonOverlapping", stmt);
            get_place_in_operand(&cno.src, places);
            get_place_in_operand(&cno.dst, places);
            // Do we really need to record the place of the count arg?
            get_place_in_operand(&cno.count, places);
        },
        StatementKind::StorageLive(_)
            | StatementKind::StorageDead(_)
            | StatementKind::LlvmInlineAsm(_)
            | StatementKind::Coverage(_)
            | StatementKind::Nop => { }
    }

}

/// Extract Place in a Terminator.
fn get_place_in_terminator(body: &'tcx Body<'tcx>, terminator: &Terminator<'tcx>,
    places: &mut Vec::<Place<'tcx>>) {
    match &terminator.kind {
        TerminatorKind::SwitchInt{discr, ..} => {
            print_terminator("SwitchInt", terminator);
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
            // Extract the Place from the LHS if the call returns something.
            if let Some((place, _)) = destination {
                // TODO? Should we ignore all locals, i.e., those Place whose
                // projection is empty?
                if let ty::Tuple(tys) = body.local_decls[place.local].ty.kind() {
                    // Ignore returns type of "()".
                    if tys.len() == 0 { return; }
                }
                places.push(*place);
            }
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

/// Check if a function is one that allocates a heap object, e.g, Vec::new().
fn is_heap_alloc(func: &Constant<'tcx>) -> bool {
    if let ty::FnDef(def_id, _) = *func.literal.ty().kind() {
        let name = ty::tls::with(|tcx| {
            tcx.opt_item_name(def_id).unwrap().name.to_ident_string()});
        // The name ignors the crate and module and struct and only keeps
        // the final method, e.g., "new" of "Box::<i32>::new". Perhaps we
        // should check where a method is from; we would otherwise run the
        // risk of introducing false positives.
        if HEAP_ALLOC.contains(&name) {
            println!("[Heap Alloc]: {:?}", func);

            return true;
        }
    }

    false
}

/// Core procedure of the finding the allocation sites of unsafe objects.
///
/// Inputs:
/// @place_locals: The Local of all the Place used directly or indirectly (e.g.,
///                by assignment) by unsafe code.
/// @bb: The currently processed BasicBlock.
/// @unsafe_op: The last unsafe operation in a BB, or None.
/// @visited: Already processed BasicBlock.
/// @op: The last unsafe Operation in an unsafe BB or the last Operation in other BB.
/// @body: The function body of the current BB.
/// @results: Unsafe allocation sites.
fn handle_unsafe_op_core(place_locals: &mut FxHashSet<Local>,
                         bb: BasicBlock, unsafe_op: Option<&UnsafeOp<'tcx>>,
                         visited: &mut FxHashSet<BasicBlock>,
                         body: &'tcx Body<'tcx>,
                         results: &mut Vec::<UnsafeAllocSite<'tcx>>) {
    // Prevent infinite recursion caused by loops.
    if visited.contains(&bb) {return;}
    visited.insert(bb);

    // Has handled all target Place.
    if place_locals.is_empty() {return;}

    let bbd = &body.basic_blocks()[bb];
    let stmt_num = bbd.statements.len();
    let location = match unsafe_op {
        Some(op) => op.location,
        None => Location {block: bb, statement_index: stmt_num}
    };
    let mut stmt_index = location.statement_index;
    if unsafe_op.is_none() || location.statement_index == stmt_num {
        // Examine a terminator.
        if let TerminatorKind::Call{func: Operand::Constant(f), args,
                                    destination, ..} = &bbd.terminator().kind {
            if let Some((place, _)) = destination {
                // if _DEBUG { println!("Unsafe Place: {:?}", place_locals); }
                // There are three cases:
                // 1. a heap allocation call such as Vec::new()
                // 2. a non-std-lib fn call that returns a pointer
                // 3. a std-lib fn call that returns a ptr, e.g, p = v.as_ptr()
                if place_locals.contains(&place.local) {
                    // Found a definition site for an unsafe Place.
                    if is_heap_alloc(f) {
                        results.push(UnsafeAllocSite::Alloc(bbd.terminator()));
                    } else {
                        // Get Place used in args of the call.
                        let mut place_in_args = Vec::<Place<'tcx>>::new();
                        args.iter().for_each(
                            |arg| get_place_in_operand(arg, &mut place_in_args));
                        // Can the next loop be rewritten in a functional style?
                        // Cannot use for_each as it requires a Fn that returns '()'.
                        for place in place_in_args {
                            place_locals.insert(place.local);
                        }

                        results.push(UnsafeAllocSite::Ret(bbd.terminator()));
                        // TODO: We need distinguish the 2nd and 3rd conditions
                        // because we do not process std libs.
                    }
                    place_locals.remove(&destination.unwrap().0.local);
                }
            }
        }
        stmt_index -= 1;
    }

    if stmt_num != 0 {
        // Examine each statement in the current BB backward.
        for i in (0..=stmt_index).rev() {
            let stmt = &bbd.statements[i];
            match &stmt.kind {
                StatementKind::Assign(box (place, rvalue)) => {
                    if place_locals.contains(&place.local) {
                        // Put the Place in rvalue to the unsafe Place set.
                        let mut place_in_rvalue = Vec::<Place<'tcx>>::new();
                        get_place_in_rvalue(&rvalue, &mut place_in_rvalue);
                        for place in place_in_rvalue {
                            place_locals.insert(place.local);
                        }
                        place_locals.remove(&place.local);
                    }
                },
                _  => {
                    // Any other cases to handle?
                }
            }
        }
    }

    // Recursively traverse backward to the current BB's predecessors.
    // Note that we need pass a clone of place_locals due to branches.
    for pbb in &body.predecessors()[bb] {
        if _DEBUG {
            println!("Initial unsafe Place for BB {:?}: {:?}", pbb, place_locals);
        }
        handle_unsafe_op_core(&mut place_locals.clone(), *pbb, None, visited,
                              body, results);
    }

    // After examing the entry BB, check if there are any unsafe Place from
    // the function's arguments.
    if bb.index() == 0  && !place_locals.is_empty() {
       for arg in body.args_iter() {
           if place_locals.contains(&arg) {
               results.push(UnsafeAllocSite::Arg(arg));
               place_locals.remove(&arg);
           }
       }
    }
}

/// Entrance of the unsafe operation (statement/terminator) analysis function.
/// For a BasicBlock that contains more than one unsafe operation, it traverses
/// the BB from the last unsafe operation backwards so that there is no need to
/// start a traversal procedure for each one of them.
fn handle_unsafe_op(unsafe_ops: &Vec<Box<UnsafeOp<'tcx>>>, body: &Body<'tcx>) {
    // The Local of Place.
    let mut place_locals = FxHashSet::<Local>::default();
    // Map each BasicBlock to the last unsafe operation in it.
    let mut bb_ops = FxHashMap::<BasicBlock, &UnsafeOp<'tcx>>::default();
    // Results
    let mut results = Vec::<UnsafeAllocSite<'tcx>>::new();

    for unsafe_op in unsafe_ops {
        // Collect all interested Place represented as u32.
        for place in &unsafe_op.places {
            place_locals.insert(place.local);
        }
        // Collect the last unsafe statement/terminator in a block.
        bb_ops.insert(unsafe_op.location.block, unsafe_op);
    }

    // Examine each BB that contains unsafe operation(s).
    for (bb, unsafe_op) in bb_ops {
        // Record visited BasicBlock to avoid infinite cycles due to loop.
        let mut visited = FxHashSet::<BasicBlock>::default();
        if _DEBUG {
            println!("[handle_unsafe_op]: Initial unsafe Place for BB {:?}: {:?}", bb, place_locals);
        }
        handle_unsafe_op_core(&mut place_locals, bb, Some(unsafe_op),
                              &mut visited, body, &mut results);
    }

}

/// Entrance of this module. It finds the definition or declaration site of each
/// heap memory object used in unsafe code.
pub fn find_unsafe_obj(tcx: TyCtxt<'tcx>, def_id: DefId) {
    // Filter out uninterested functions.
   if is_builtin_or_std(tcx, def_id) {
       return;
   }

    let name = tcx.opt_item_name(def_id);
    if name.is_none() || ignore_fn(tcx, def_id) {
        // Filter uninterested functions for fast development purpose.
        return;
    }

    // Start of the computation.
    println!("[find_unsafe_obj]: Processing function {}", name.unwrap().name);
    let body = tcx.optimized_mir(def_id);

    if is_unsafe(body, SourceInfo::outermost(body.span).scope) {
        // TODO: Process an unsafe function.
    }

    // Collect operations in unsafe blocks.
    let mut unsafe_ops = Vec::new();  // Unsafe statement/terminator.
    for (bb, data) in body.basic_blocks().iter_enumerated() {
        for (i, stmt) in data.statements.iter().enumerate() {
            if !is_unsafe(body, stmt.source_info.scope) {
                continue;
            }

            // Collect unsafe Statement.
            let mut unsafe_op = box UnsafeOp {places: Vec::new(),
                // stmt: Some(stmt), terminator: None,
                location: Location {block: bb, statement_index: i}};
            get_place_in_stmt(&stmt, &mut unsafe_op.places);
            if !unsafe_op.places.is_empty() {
                unsafe_ops.push(unsafe_op);
            }
            if _DEBUG {
                println!("Unsafe Statement: {:?}", stmt);
            }
        }

        let terminator = &data.terminator();
        if !is_unsafe(body, terminator.source_info.scope) {
            continue;
        }

        // Collect unsafe terminator.
        let mut unsafe_op = box UnsafeOp {places: Vec::new(),
            location: Location {block: bb, statement_index: data.statements.len()}};
        get_place_in_terminator(body, &terminator, &mut unsafe_op.places);
        if !unsafe_op.places.is_empty() {
            unsafe_ops.push(unsafe_op);
        }
        if _DEBUG {
            println!("Unsafe Terminator: {:?}", terminator);
        }
    }

    if !unsafe_ops.is_empty() {
        println!("Found {} unsafe statements/terminators", unsafe_ops.len());

        handle_unsafe_op(&unsafe_ops, body);
        println!("");
    }
}
