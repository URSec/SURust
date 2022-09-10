//! Analyze a function to find the definition sites of each Place used in
//! unsafe code.

use rustc_middle::mir::*;
use rustc_data_structures::fx::{FxHashSet,FxHashMap};

use crate::sandbox::utils::*;
use crate::sandbox::debug::*;
use super::{DefSite,Summary};

// For debugging purpose.
static _DEBUG: bool = false;

/// An unsafe operation (a statement or a terminator) in an unsafe block/fn.
struct UnsafeOp <'tcx> {
    // All Place used in this statement/terminator.
    // Should we use SmallVec to improve performance?
    places: Vec<Place<'tcx>>,
    // Location of the statement or terminator
    location: Location,
}

/// Check if a fn is unsafe, or if a statement/terminator in an unsafe block.
fn is_unsafe<'tcx>(body: &Body<'tcx>, scope: SourceScope) -> bool {
    match body.source_scopes[scope].local_data.as_ref() {
        ClearCrossCrate::Clear => false,
        ClearCrossCrate::Set(v) => {
            match v.safety {
                Safety::ExplicitUnsafe(_) | Safety::FnUnsafe => true,
                // TODO?: Handle BuiltinUnsafe
                _ => false
            }
        }
    }
}

/// Extract Place in a Statement.
fn get_place_in_stmt<'tcx>(stmt: &Statement<'tcx>, places: &mut Vec::<Place<'tcx>>) {
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
            if _DEBUG { print_stmt("CopyNonOverlapping", stmt); }
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
fn get_place_in_terminator<'tcx>(body: &'tcx Body<'tcx>,
                                 terminator: &Terminator<'tcx>,
                                 places: &mut Vec::<Place<'tcx>>) {
    match &terminator.kind {
        TerminatorKind::SwitchInt{discr, ..} => {
            if _DEBUG { print_terminator("SwitchInt", terminator); }
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

/// Collect unsafe allocation sites of an unsafe function. It does not need to
/// analyze the data flow of the function; instead, it only needs to collect all
/// fn arguments and return values of function calls.
///
/// Inputs:
/// @body: The body of the target function.
/// @results: The result vector of all unsafe allocation sites.
fn find_unsafe_fn_def<'tcx>(body: &'tcx Body<'tcx>,
                            results: &mut FxHashSet::<DefSite>) {
    for arg in body.args_iter() {
        results.insert(DefSite::Arg(arg.as_u32()));
    }

    for (bb, bbd) in body.basic_blocks().iter_enumerated() {
        match &bbd.terminator().kind {
            TerminatorKind::Call{func: Operand::Constant(f), ..} => {
                results.insert(def_site_from_call(f, bb.as_u32()));
            },
            _ => {}
        }
    }
}

/// Core procedure of finding definition site of each Place in unsafe code.
/// It iterates over each BB backwards and then the BB's predecessors to find
/// def sites. During the traversal, it collects new unsafe Place used to define
/// existing unsafe Place, e.g., if _2 is an unsafe Place, then "_2 = foo(_3);"
/// is an def site for _2, and _3 is a contributor to _2 and thus will be put
/// the unsafe Place set.
///
/// Inputs:
/// @place_locals: The Local of all the Place used directly or indirectly (e.g.,
///                by assignment) by unsafe code.
/// @bb: The currently processed BasicBlock.
/// @unsafe_op: The last unsafe operation in a BB, or None.
/// @visited: Already processed BasicBlock.
/// @body: The function body of the current BB.
/// @results: Unsafe def sites.
fn find_unsafe_def_core<'tcx>(place_locals: &mut FxHashSet<Local>,
                              bb: BasicBlock,
                              unsafe_op: Option<&UnsafeOp<'tcx>>,
                              visited: &mut FxHashSet<BasicBlock>,
                              body: &'tcx Body<'tcx>,
                              results: &mut FxHashSet::<DefSite>) {
    // Prevent infinite recursions caused by loops.
    if !visited.insert(bb) { return; }

    // Has handled all target Place.
    if place_locals.is_empty() { return; }

    let bbd = &body.basic_blocks()[bb];
    let stmt_num = bbd.statements.len();
    let location = match unsafe_op {
        Some(op) => op.location,
        None => Location { block: bb, statement_index: stmt_num }
    };
    let mut stmt_index = location.statement_index;
    if location.statement_index == stmt_num {
        // Examine a terminator.
        if let TerminatorKind::Call{func: Operand::Constant(f), args,
                                    destination, ..} = &bbd.terminator().kind {
            if place_locals.contains(&destination.local) {
                // Found a definition site for an unsafe Place.
                place_locals.remove(&destination.local);
                let def_site = def_site_from_call(f, bb.as_u32());
                match def_site {
                    DefSite::HeapAlloc(_) => {
                        results.insert(def_site);
                        // Question: Do we need to handle argument(s) to a
                        // heap allocation, e.g., Vec::from_raw_parts()?
                    },
                    DefSite::NativeCall(_) => {
                        // Since we do not analyze native functions, we need
                        // conservatively assume that all arguments to such
                        // a function contribute to the return value.
                        get_local_in_args(args, place_locals);
                        // No need to add this def_site to results. Or we can
                        // add only the def_site without adding args, and wait
                        // for WPA to process args.
                    },
                    DefSite::OtherCall(_) => {
                        // For a normal call, we only need to track args that
                        // contribute to the return value. However, we do not
                        // know which arg contributes until WPA.  So here we
                        // do not track args and wait for WPA.
                        results.insert(def_site);
                    },
                    _ => {}
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
                        place_locals.remove(&place.local);
                        // Put the Place in rvalue to the unsafe Place set.
                        let mut place_in_rvalue = Vec::<Place<'tcx>>::new();
                        get_place_in_rvalue(&rvalue, &mut place_in_rvalue);
                        for place in place_in_rvalue {
                            place_locals.insert(place.local);
                        }
                    }
                },
                _  => {
                    // Any other cases to handle?
                }
            }
        }
    }

    // Recursively traverse backward to the current BB's predecessors.
    let pbb_num = body.predecessors()[bb].len();
    for pbb in &body.predecessors()[bb] {
        if pbb_num > 1 {
            // Pass a clone of place_locals in case of branches.
            find_unsafe_def_core(&mut place_locals.clone(), *pbb, None,
                                 visited, body, results);
        } else {
            // There is only one predecessor. Just pass the original place_locals.
            find_unsafe_def_core(place_locals, *pbb, None, visited, body, results);
        }
    }

    // After examing the entry BB, check if there are any unsafe Place from
    // the function's arguments.
    if bb.index() == 0  && !place_locals.is_empty() {
       for arg in body.args_iter() {
           if place_locals.contains(&arg) {
               results.insert(DefSite::Arg(arg.as_u32()));
               place_locals.remove(&arg);
           }
       }
    }
}

/// Find unsafe definition sites within a non-unsafe function.
///
/// It first collects all the Place of operations (Statement/Terminator) in
/// unsafe blocks. It then calls the core procedure to iterate over each BB
/// that contains unsafe operations and the BB's predecessors to find def sites
/// that generate those unsafe Place.
fn find_unsafe_def<'tcx>(body: &'tcx Body<'tcx>, results: &mut FxHashSet<DefSite>) {
    // Collect operations in unsafe blocks.
    let mut unsafe_ops = Vec::new();
    for (bb, bbd) in body.basic_blocks().iter_enumerated() {
        for (i, stmt) in bbd.statements.iter().enumerate() {
            if !is_unsafe(body, stmt.source_info.scope) {
                continue;
            }

            // Collect unsafe Statement.
            let mut unsafe_op = UnsafeOp {
                places: Vec::new(),
                location: Location { block: bb, statement_index: i }
            };
            get_place_in_stmt(&stmt, &mut unsafe_op.places);
            if !unsafe_op.places.is_empty() {
                unsafe_ops.push(unsafe_op);
            }
            if _DEBUG { println!("Unsafe Statement:  {:?}", stmt); }
        }

        let terminator = &bbd.terminator();
        if !is_unsafe(body, terminator.source_info.scope) {
            continue;
        }

        // Collect unsafe terminator.
        let mut unsafe_op = UnsafeOp {
            places: Vec::new(),
            location: Location {
                block: bb, statement_index: bbd.statements.len()
            }};
        get_place_in_terminator(body, &terminator, &mut unsafe_op.places);
        if !unsafe_op.places.is_empty() {
            unsafe_ops.push(unsafe_op);
        }
        if _DEBUG {
            println!("Unsafe Terminator: {:?}", terminator.kind);
        }
    }

    if unsafe_ops.is_empty() {
        return;
    }

    if _DEBUG {
        println!("Found {} unsafe statements/terminators", unsafe_ops.len());
    }

    // Map each BasicBlock to the last unsafe operation in it.
    let mut bb_unsafe_ops = FxHashMap::<BasicBlock, UnsafeOp<'tcx>>::default();
    let mut place_locals = FxHashSet::<Local>::default();
    for unsafe_op in unsafe_ops {
        // Collect all interested Place as its Local.
        for place in &unsafe_op.places {
            place_locals.insert(place.local);
        }
        // Collect the last unsafe statement/terminator in a block.
        bb_unsafe_ops.insert(unsafe_op.location.block, unsafe_op);
    }

    // Examine each BB that contains unsafe operation(s).
    for (bb, unsafe_op) in bb_unsafe_ops {
        // Record visited BasicBlock to avoid infinite cycles due to loop.
        let mut visited = FxHashSet::<BasicBlock>::default();
        find_unsafe_def_core(&mut place_locals, bb, Some(&unsafe_op),
                             &mut visited, body, results);
    }

    if _DEBUG { print_unsafe_def(&results); }
}

/// Entrance of this module.
pub(super) fn analyze_fn<'tcx>(body: &'tcx Body<'tcx>, summary: &mut Summary) {
    if _DEBUG {
        let def_id = body.source.def_id();
        println!("[summarize_fn::analyze_fn]: Processing function {}:{}",
          get_crate_name(def_id), get_fn_name(def_id));
    }

    let mut results = FxHashSet::<DefSite>::default();
    if is_unsafe(body, SourceInfo::outermost(body.span).scope) {
        // Process an unsafe function.
        find_unsafe_fn_def(&body, &mut results);

        if _DEBUG { print_unsafe_def(&results); }
    } else {
        // Analyze a non-unsafe function.
        find_unsafe_def(body, &mut results);
    }

    if !results.is_empty() {
        summary.unsafe_defs = Some(results);
    }
}
