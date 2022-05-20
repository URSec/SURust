use rustc_middle::mir::*;
use rustc_middle::ty::{self, TyCtxt};
use rustc_hir::def_id::{DefId};
use rustc_data_structures::fx::{FxHashSet, FxHashMap};

use super::debug::*;
use super::database::*;

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
    Arg(Place<'tcx>),
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
    return crate_name == "core" || crate_name == "std" ||
           crate_name == "alloc" ||
           crate_name == "test" ||
           crate_name == "backtrace";
}

/// Get the Place in an Operand.
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

/// Get the Place(s) in a Rvalue.
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

/// Extract Place in a Statement.
fn get_place_in_stmt(stmt: &Statement<'tcx>, places: &mut Vec::<Place<'tcx>>) {
    match &stmt.kind {
        StatementKind::Assign(box (place, rvalue)) => {
            // print_stmt_assign(stmt, rvalue);
            places.push(*place);
            get_place_in_rvalue(rvalue, places);
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
            places.push(*place);
        },
        StatementKind::Retag(_, box place) => {
            // What exactly is a retag inst?
            print_stmt("Retag", stmt);
            places.push(*place);
        },
        StatementKind::AscribeUserType(box (place, _), _) => {
            print_stmt("AscribeUserType", stmt);
            places.push(*place);
        },
        StatementKind::CopyNonOverlapping(box copy_non_overlap) => {
            print_stmt("CopyNonOverlapping", stmt);
            get_place_in_copynonoverlap(copy_non_overlap, places);
        },
        StatementKind::StorageLive(_)
            | StatementKind::StorageDead(_)
            | StatementKind::LlvmInlineAsm(_)
            | StatementKind::Coverage(_)
            | StatementKind::Nop => { }
    }

}

/// Extract Place in a Terminator.
fn get_place_in_terminator(terminator: &Terminator<'tcx>,
    places: &mut Vec::<Place<'tcx>>) {
    match &terminator.kind {
        TerminatorKind::SwitchInt{discr, ..} => {
            print_terminator("SwitchInt", terminator);
            get_place_from_operand(discr, places);
        },
        TerminatorKind::Drop{place, ..} => {
            places.push(*place);
        },
        TerminatorKind::DropAndReplace{place, value, ..} => {
            places.push(*place);
            get_place_from_operand(value, places);
        },
        TerminatorKind::Call{func: _, args, ..} => {
            // For some unknown reason(s), sometimes printing a Call in println!
            // will crash the compiler.
            //
            // What is the Place in "destination: Option<(Place<'tcx>, BasicBlock)"?
            for arg in args {
                get_place_from_operand(arg, places);
            }
        },
        TerminatorKind::Assert{cond, ..} => {
            // Do we need to handle assertions?
            get_place_from_operand(cond, places);
        },
        TerminatorKind::Yield{value, resume: _, resume_arg, ..} => {
            get_place_from_operand(value, places);
            places.push(*resume_arg);
        },
        _ => {}
    }
}

/// Get Place in an CopyNonOverlapping Statement.
/// We handle it separately as it is more complex than most other Statement.
fn get_place_in_copynonoverlap(_stmt: &CopyNonOverlapping<'tcx>,
                               _places: &mut Vec<Place<'tcx>>) {
    // TODO: Handle CopyNonOverlapping
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
        if let TerminatorKind::Call{func: Operand::Constant(f), ..} =
            &bbd.terminator().kind {
            // There are three cases:
            // 1. a heap allocation call such as Vec::new()
            // 2. a non-std-lib fn call that returns a pointer
            // 3. a std-lib fn call that returns a pointer, e.g, p = v.as_ptr()
            // print_terminator("Call", &bbd.terminator());
            if is_heap_alloc(f) {
                results.push(UnsafeAllocSite::Alloc(bbd.terminator()));
            } else {
                // TODO: Handle case 2 and case 3.
            }
        }
        stmt_index -= 1;
        // TODO: Remove related Place in place_locals
    }

    // Examine starting from a Statement backward.
    for i in (0..=stmt_index).rev() {
        // TODO: Examine each statement in the current BB backward.
        let _stmt = &bbd.statements[i];
    }

    // TODO: Recursively traverse backward to the current BB's predecessors.
    // Note that we need pass a clone of place_locals due to branches.
    for pbb in &body.predecessors()[bb] {
        handle_unsafe_op_core(&mut place_locals.clone(), *pbb, None, visited,
                              body, results);
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
        handle_unsafe_op_core(&mut place_locals, bb, Some(unsafe_op),
                              &mut visited, body, &mut results);
    }
}

/// Entrance of this module. It finds the definition or declaration site of each
/// memory object used in unsafe code.
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
    println!("[find_unsafe_obj]: Processing {:?}", name);
    let body = tcx.optimized_mir(def_id);

    if is_unsafe(body, SourceInfo::outermost(body.span).scope) {
        // TODO: Process an unsafe function.
    }

    let mut unsafe_ops = Vec::new();  // Unsafe statement/terminator.
    for (bb, data) in body.basic_blocks().iter_enumerated() {
        for (i, stmt) in data.statements.iter().enumerate() {
            if !is_unsafe(body, stmt.source_info.scope) {
                continue;
            }

            // Handle unsafe Statement.
            let mut unsafe_op = box UnsafeOp {places: Vec::new(),
                // stmt: Some(stmt), terminator: None,
                location: Location {block: bb, statement_index: i}};
            get_place_in_stmt(&stmt, &mut unsafe_op.places);
            if !unsafe_op.places.is_empty() {
                unsafe_ops.push(unsafe_op);
            }
        }

        let terminator = &data.terminator();
        if !is_unsafe(body, terminator.source_info.scope) {
            continue;
        }

        // Handle unsafe terminator.
        let mut unsafe_op = box UnsafeOp {places: Vec::new(),
            location: Location {block: bb, statement_index: data.statements.len()}};
        get_place_in_terminator(&terminator, &mut unsafe_op.places);
        if !unsafe_op.places.is_empty() {
            unsafe_ops.push(unsafe_op);
        }
    }

    if !unsafe_ops.is_empty() {
        handle_unsafe_op(&unsafe_ops, body);

        println!("Found {} unsafe statements/terminators", unsafe_ops.len());
    }
}
