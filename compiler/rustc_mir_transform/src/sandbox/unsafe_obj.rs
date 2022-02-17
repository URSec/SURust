use rustc_middle::mir::*;
use rustc_middle::ty::{TyCtxt};
use rustc_middle::ty::query::Providers;
use rustc_hir::def_id::{DefId};
use rustc_data_structures::fx::{FxHashSet};

// This function whitelist is a helper for development only.
lazy_static!{
    static ref FN_TO_PROCESS: FxHashSet<String> = {
        let mut vec = Vec::new();
        vec.push("foo".to_string());
        vec.push("bar".to_string());
        // vec.push("main".to_string());
        // For exa (https://github.com/ogham/exa)
        vec.push("add_files_to_table".to_string());
        vec.push("translate_attribute_name".to_string());
        vec.push("listxattr_first".to_string());

        vec.into_iter().collect()
    };
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

/// Register sandboxing related queries.
crate fn provide(providers: &mut Providers) {
    providers.unsafe_obj_mir = |tcx, def_id| find_unsafe_obj(tcx, def_id);
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
fn print_stmt(type_name: &str, stmt: &Statement<'_>) {
    println!("[{}]: {:?}", type_name, stmt);
}

/// Handle StatementKind::Assign separately as the RValue can be complex.
fn handle_assign(_rvalue: &Rvalue<'tcx>, _result: &mut Vec<Place<'tcx>>) {
    // TODO
}

/// Handle CopyNonOverlapping separately as it is more complex than most
/// types StatementKind statements.
fn handle_copynonoverlap(_stmt: &CopyNonOverlapping<'tcx>, _result: &mut Vec<Place<'tcx>>) {
    // TODO: Handle CopyNonOverlapping
}

/// This function finds the definition or declaration of each memory object
/// used in unsafe code.
fn find_unsafe_obj(tcx: TyCtxt<'tcx>, def_id: DefId) -> Option<Vec<Place<'tcx>>> {
    // Filter out uninterested functions.
   if is_builtin_or_std(tcx, def_id) {
       return None;
   }

    let name = tcx.opt_item_name(def_id);
    if name.is_none() || ignore_fn(tcx, def_id) {
        return None;
    }

    // Start of the computation.
    println!("[find_unsafe_obj]: Processing {:?}", name);
    let body = tcx.optimized_mir(def_id);

    // Check if this is an unsafe fn.
    if is_unsafe(body, SourceInfo::outermost(body.span).scope) {
        // TODO: Process the whole function.
    }

    // let mut result = Vec::new();
    let mut result = Vec::new();
    // let mut unsafe_stmts = Vec::new();
    for bb in body.basic_blocks() {
        for stmt in &bb.statements {
            if !is_unsafe(body, stmt.source_info.scope) {
                continue;
            }
            // unsafe_stmts.push(stmt);
            // TODO: Process the stmt.
            match &stmt.kind {
                StatementKind::Assign(box (place, rvalue)) => {
                    print_stmt("Assign", stmt);
                    result.push(*place);
                    // TODO: Handle rvalue
                    handle_assign(rvalue, &mut result);
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
                    result.push(*place);
                },
                StatementKind::Retag(_, box place) => {
                    // What exactly is a retag inst?
                    print_stmt("Retag", stmt);
                    result.push(*place);
                },
                StatementKind::AscribeUserType(box (place, _), _) => {
                    print_stmt("AscribeUserType", stmt);
                    result.push(*place);
                },
                StatementKind::CopyNonOverlapping(box copy_non_overlap) => {
                    print_stmt("CopyNonOverlapping", stmt);
                    handle_copynonoverlap(copy_non_overlap, &mut result);
                },
                StatementKind::StorageLive(_)
                | StatementKind::StorageDead(_)
                | StatementKind::LlvmInlineAsm(_)
                | StatementKind::Coverage(_)
                | StatementKind::Nop => {
                    print_stmt("Others: {:?}", stmt);
                }

            }
        }

        // TODO: Process the terminator.
        let terminator = &bb.terminator();
        if !is_unsafe(body, terminator.source_info.scope) {
            continue;
        }
    }

    Some(result)
}
