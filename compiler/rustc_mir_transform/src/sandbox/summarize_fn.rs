//! Analyze and summarize the information for a function.  The summary will be
//! used for the later inter-procedural analysis that generates a final summary
//! for the whole program.

use rustc_middle::mir::*;
use rustc_middle::ty::{self, TyCtxt};
use rustc_hir::def_id::{DefId};
use rustc_data_structures::fx::{FxHashSet, FxHashMap};
use serde::{Deserialize, Serialize};
use std::fmt;

use super::lib::*;

/// Definition site of a Place can be one of the following cases:
/// 1. Global variable
/// 2. Local variable on the stack
/// 3. Return value of call, including heap allocation and other function call
/// 4. Function argument.
///
/// Currently we only aim to isolate unsafe heap memory, so we only handle
/// case 3 and 4.
#[derive(Hash, Eq, Serialize, Deserialize)]
enum DefSite {
    /// Location of a terminator.
    /// Since it will always be a Terminator, can we just use a BasicBlock?
    LocBB(u32),
    /// Local of an argument
    Arg(u32),
}

impl PartialEq for DefSite {
    fn eq(&self, other: &DefSite) -> bool {
        match (self, other) {
            (DefSite::LocBB(loc_bb), DefSite::LocBB(loc_bb1)) =>
                loc_bb == loc_bb1,
            (DefSite::Arg(arg), DefSite::Arg(arg1)) => arg == arg1,
            _ => false
        }
    }
}

/// Information of a callee used by a function. Speficially, we collect the
/// allocation/declaration sites for all the arguments of a callee. Note that
/// we do not need to distinguish each call to the same callee.
#[derive(Serialize, Deserialize)]
struct Callee {
    /// Callee name
    name: String,
    /// DefId {DefIndex, CrateNum}
    id: (u32, u32),
    /// The locations of the definition site for each argument. For example,
    /// [[l0, l1], [l2, _2]] means the caller has two arguments, and the first
    /// argument is computed from Terminator l0 and l1, and the second is from
    /// Terminator l2 and local _2 (an argument or local var).
    arg_def_sites: Vec<FxHashSet<DefSite>>,
}

/// Summary of a function.
#[derive(Serialize, Deserialize)]
pub struct Summary {
    // fn_name crate_name are not necessary.
    pub fn_name: String,
    pub crate_name: String,
    /// DefIndex
    id: (u32, u32),
    /// Callees used in this function. Key is DefId.
    callees: Vec<Callee>,
    /// Return value
    ret_def_sites: FxHashSet<DefSite>
}

impl fmt::Debug for DefSite {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let (message, loc) = match self {
            DefSite::LocBB(loc) => ("BB", loc),
            DefSite::Arg(arg) => ("Arg", arg)
        };
        write!(f, "{}: {}", message, loc)
    }
}

impl fmt::Debug for Callee {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} (ID:{:?}; arg_def_sites: {:?}", self.name, self.id,
            self.arg_def_sites)
    }
}

impl fmt::Debug for Summary {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}::{} {:?}:\nCallees: {:?}\nReturn: {:?}\n", self.crate_name,
            self.fn_name, self.id, self.callees, self.ret_def_sites)
    }
}

/// Get the target Callee by DefId.
///
/// This may not be that slow as it looks because a function usually only has
/// a limited number of callees. We did not use a HashSet for Summary.callees
/// because HashSet does not support get_mut(). We also did not use
/// HashMap<DefId, Callee> because serializing it will generate illegal JSON
/// ("key must be a string").
#[inline(always)]
fn get_callee(callees: &mut Vec<Callee>, def_id: DefId) -> &mut Callee {
    for callee in callees.iter_mut() {
        if break_def_id(def_id) == callee.id {
            return callee;
        }
    }

    panic!("Cannot find a callee");
}

/// Update Callee.arg_def_sites with a new DefSite.
///
/// Inputs:
/// @def_id: DefId of the target callee.
/// @index: Index of the argument in Callee.arg_def_sites.
/// @site: A new DefSite
/// @summary: Summary.
fn update_callee_arg_def_sites(def_id: DefId, index: usize, site: DefSite,
                               summary: &mut Summary) {
    let callee = get_callee(&mut summary.callees, def_id);
    // We use get_mut() instead of a simple [] to handle one corner case where
    // a variadic callee is called more than once with different number of
    // arguments AND during the init of Callee in analyze_fn(), the fewer-arg
    // call is processed before the more-arg call(s). In this case,
    // callee.arg_def_sites.len() would be smaller than index.  We expand the
    // arg_def_sites dynamically to solve this problem.
    match callee.arg_def_sites.get_mut(index) {
        Some(sites) => { sites.insert(site); },
        None => {
            let mut sites = FxHashSet::default();
            sites.insert(site);
            callee.arg_def_sites.push(sites);
        }
    }
}

/// Core procedure of finding allocation/declaration sites of each argument
/// of a function call. It first examines a basic block backwards, and then
/// recursively examines the BB's predecessors. It is similar to
/// unsafe_obj::find_unsafe_alloc_core.
///
/// Inputs:
/// @bb: Currently processed BasicBlock.
/// @body: Body of the processed function.
/// @callee_def_id: DefId of the currently processed callee.
/// @locals: Local (Place) that contributes to the arguments of the call.
/// @visited: Already processed BB.
/// @summary: Summary of the target function.
fn find_arg_def(bb: BasicBlock, body: &Body<'tcx>, callee_def_id: DefId,
    locals: &mut Vec<FxHashSet<Local>>, visited: &mut FxHashSet<BasicBlock>,
    summary: &mut Summary) {
    if visited.contains(&bb) || locals.is_empty() { return; }
    visited.insert(bb);

    let bbd = &body.basic_blocks()[bb];
    // Process Terminator
    if let TerminatorKind::Call{func: Operand::Constant(_f), args, destination,
        ..} = &bbd.terminator().kind {
        if let Some(local) = get_ret_local(destination, body) {
            // Found a definition site from a function call.
            for i in 0..locals.len() {
                let arg_locals = &mut locals[i];
                if arg_locals.contains(&local) {
                    arg_locals.remove(&local);
                    get_local_in_args(args, arg_locals);
                    update_callee_arg_def_sites(callee_def_id, i,
                        DefSite::LocBB(bb.as_u32()), summary);
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
            find_arg_def(*pbb, body, callee_def_id, &mut locals.clone(),
                         visited, summary);
        } else {
            find_arg_def(*pbb, body, callee_def_id, locals, visited, summary);
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
                    update_callee_arg_def_sites(callee_def_id, i,
                        DefSite::Arg(arg.as_u32()), summary);
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
        // This means we need to examine the BB from the Terminator.
        if let TerminatorKind::Call{func: _, args, destination, ..} =
            &bbd.terminator().kind {
            if let Some(local) = get_ret_local(destination, body) {
                if locals.contains(&local) {
                    locals.remove(&local);
                    get_local_in_args(args, locals);
                    summary.ret_def_sites.insert(DefSite::LocBB(bb.as_u32()));
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
                summary.ret_def_sites.insert(DefSite::Arg(arg.as_u32()));
            });
    }
}

/// Check if the destination of a call is the return value of the caller.
fn dest_to_ret(dest: &Option<(Place<'tcx>, BasicBlock)>, body: &Body<'tcx>)
    -> bool {
    if let Some((place, _)) = dest {
        if place.local.as_u32() != 0 { return false; }

        if let ty::Tuple(tys) = body.local_decls[place.local].ty.kind() {
            if tys.len() == 0 { return false; }
        }

        return true;
    }

    false
}

/// Analyze a function to find:
/// 1. Its callees and the definition sites of the arguments of each callee.
/// 2. The definition sites for its return value, if there is one.
fn analyze_fn(body: &Body<'tcx>, summary: &mut Summary) {
    // BB that end with a call.
    let mut bb_with_calls = Vec::new();
    // Callee functions that have been seen.
    let mut recorded_callee = FxHashSet::<DefId>::default();
    // Location of return value's def stmt and Local that contribute to it.
    let mut ret_def = FxHashMap::<Location, FxHashSet::<Local>>::default();
    // Whether this function returns something (not "()").
    let mut ret_none_empty = true;
    if let ty::Tuple(tys) = body.return_ty().kind() {
        if tys.len() == 0 { ret_none_empty = false ;}
    };
    // Prepare data:
    // 1. BB with a call.
    // 2. BB with return value definition.
    for (bb, bbd) in body.basic_blocks().iter_enumerated() {
        let terminator = &bbd.terminator();
        if let TerminatorKind::Call{func: Operand::Constant(f), args,
            destination, ..} = &terminator.kind {
            // Prepare for Callee
            bb_with_calls.push(bb);
            let def_id = get_fn_def_id(f);
            if !recorded_callee.contains(&def_id) {
                recorded_callee.insert(def_id);
                let mut arg_def_sites = Vec::with_capacity(args.len());
                if !args.is_empty() {
                    for _ in 0..args.len() {
                        arg_def_sites.push(FxHashSet::default());
                    }
                }
                summary.callees.push(Callee {
                    name: get_fn_name(f),
                    id: break_def_id(def_id),
                    arg_def_sites: arg_def_sites
                });
            }

            // Prepare for return value.
            if ret_none_empty && dest_to_ret(destination, body) {
                let loc = Location {
                    block: bb, statement_index: bbd.statements.len()
                };
                let mut locals = FxHashSet::<Local>::default();
                get_local_in_args(args, &mut locals);
                ret_def.insert(loc, locals);
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
                        ret_def.insert(loc, locals);
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
                let mut places = Vec::with_capacity(1);
                let mut arg_locals = FxHashSet::default();
                get_place_in_operand(arg, &mut places);
                for place in places { arg_locals.insert(place.local); }
                locals.push(arg_locals);
            }
            // Enter the core procedure of finding def sites for fn args.
            find_arg_def(bb, body, get_fn_def_id(f), &mut locals, &mut visited, summary);
        } else {
            panic!("Not a function");
        }
    }

    // Process the return value to find its def sites.
    for (loc, mut locals) in ret_def {
        let mut visited = FxHashSet::<BasicBlock>::default();
        find_ret_def(&loc, &mut locals, body, &mut visited, summary);
    }
}

/// Entrance of this module.
pub fn summarize(tcx: TyCtxt<'tcx>, def_id: DefId, summaries: &mut Vec::<Summary>) {
    // Filter out uninterested functions.
    if ignore_fn(tcx, def_id) { return; }

    let name = tcx.opt_item_name(def_id);

    // Init a summary.
    let crate_name = get_crate_name(tcx, def_id);
    let mut summary = Summary {
        fn_name:  name.unwrap().name.to_ident_string(),
        crate_name: crate_name.clone(),
        id: break_def_id(def_id),
        callees: Vec::new(),
        ret_def_sites: FxHashSet::default(),
    };

    println!("[summarize_fn]: Processing function {}::{}", crate_name, name.unwrap());
    let body = tcx.optimized_mir(def_id);

    analyze_fn(body, &mut summary);

    summaries.push(summary);
}
