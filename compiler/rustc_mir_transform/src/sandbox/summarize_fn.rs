//! Analyze and summarize the information for a function.  The summary will be
//! used for the later inter-procedural analysis that generates a final summary
//! for the whole program.

use rustc_middle::mir::*;
use rustc_middle::ty::{TyCtxt};
use rustc_hir::def_id::{DefId};
use rustc_data_structures::fx::{FxHashSet};
use serde::{Deserialize, Serialize};
use std::fmt;

use super::lib::*;

/// Allocation site of a Place can be one of the following cases:
/// 1. Global variable
/// 2. Local variable on the stack
/// 3. Return value of call, including heap allocation and other function call
/// 4. Function argument.
///
/// Currently we only aim to isolate unsafe heap memory, so we only handle
/// case 3 and 4.
#[derive(Hash, Eq, Serialize, Deserialize)]
enum AllocSite {
    /// Location of a terminator.
    /// Since it will always be a Terminator, can we just use a BasicBlock?
    LocBB(u32),
    /// Local of an argument
    Arg(u32),
}

impl PartialEq for AllocSite {
    fn eq(&self, other: &AllocSite) -> bool {
        match (self, other) {
            (AllocSite::LocBB(loc_bb), AllocSite::LocBB(loc_bb1)) =>
                loc_bb == loc_bb1,
            (AllocSite::Arg(arg), AllocSite::Arg(arg1)) => arg == arg1,
            _ => false
        }
    }
}

/// Information of a callee used by a function. Speficially, we collect the
/// allocation sites for all the arguments of a callee. Note that we do not
/// need to distinguish each call to the same callee.
#[derive(Serialize, Deserialize)]
struct Callee {
    /// Callee name
    name: String,
    /// DefId {DefIndex, CrateNum}
    id: (u32, u32),
    /// The locations of the allocation site for each argument. For example,
    /// [[l0, l1], [l2, _2]] means the caller has two arguments, and the first
    /// argument is computed from Terminator l0 and l1, and the second is from
    /// Terminator l2 and local _2 (an argument or local var).
    arg_alloc_sites: Option<Vec<FxHashSet<AllocSite>>>,
}

/// Summary of a function.
#[derive(Serialize, Deserialize)]
pub struct Summary {
    // fn_name is not necessary.
    fn_name: String,
    /// DefIndex
    fn_id: u32,
    /// Callees used in this function. Key is DefId.
    callees: Option<Vec<Callee>>,
    /// Return value
    ret: Option<Vec<AllocSite>>
}

impl fmt::Debug for Callee {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // TODO? Print out arguments' allocation sites.
        write!(f, "{} (ID:{:?}", self.name, self.id)
    }
}

impl fmt::Debug for Summary {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut callees = &Vec::new();
        if self.callees.is_some() {
            callees = self.callees.as_ref().unwrap();
        }
        write!(f, "{} (id: {}): Callees: {:?}", self.fn_name, self.fn_id, callees)
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
fn analyze_fn_core(bb: BasicBlock, body: &Body<'tcx>, callee_def_id: DefId,
    locals: &mut Vec<FxHashSet<Local>>, visited: &mut FxHashSet<BasicBlock>,
    summary: &mut Summary) {
    if visited.contains(&bb) || locals.is_empty() { return; }
    visited.insert(bb);

    let bbd = &body.basic_blocks()[bb];
    // Process Terminator
    if let TerminatorKind::Call{func: Operand::Constant(_f), args, destination,
        ..} = &bbd.terminator().kind {
        if let Some(local) = get_ret_local(destination, body) {
            // Found an allocation site from a function call.
            for i in 0..locals.len() {
                let arg_locals = &mut locals[i];
                if arg_locals.contains(&local) {
                    arg_locals.remove(&local);
                    let mut places_in_args = Vec::<Place<'tcx>>::new();
                    args.iter().for_each(
                        |arg| get_place_in_operand(arg, &mut places_in_args));
                    for place in places_in_args {
                        arg_locals.insert(place.local);
                    }
                    get_callee(summary.callees.as_mut().unwrap(), callee_def_id).
                        arg_alloc_sites.as_mut().unwrap()[i].insert(
                            AllocSite::LocBB(bb.as_u32()));
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
                        let mut places_rvalue = Vec::new();
                        get_place_in_rvalue(&rvalue, &mut places_rvalue);
                        for place in places_rvalue {
                            arg_locals.insert(place.local);
                        }
                    }
                }
            },
            _ => {
                // Any other cases to handle?
            }
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
                    get_callee(summary.callees.as_mut().unwrap(), callee_def_id).
                        arg_alloc_sites.as_mut().unwrap()[i].insert(
                            AllocSite::Arg(arg.as_u32()));
                }
            }
        }
    }
}

/// Analyze a function to find its callees and the allocations sites of all
/// Place used by the callees.
fn analyze_fn(tcx: TyCtxt<'tcx>, body: &Body<'tcx>, summary: &mut Summary) {
    // BB that end with a call.
    let mut bb_with_calls = Vec::new();
    // Callee functions that have been seen.
    let mut recorded = FxHashSet::<DefId>::default();
    for (bb, data) in body.basic_blocks().iter_enumerated() {
        let terminator = &data.terminator();
        // Init
        if let TerminatorKind::Call{func: Operand::Constant(f), args, ..} =
            &terminator.kind {
            bb_with_calls.push(bb);
            if summary.callees.is_none() {
                summary.callees = Some(Vec::new());
            }
            let def_id = get_fn_def_id(f);
            if !recorded.contains(&def_id) {
                recorded.insert(def_id);
                let arg_alloc_sites = if args.is_empty() { None } else {
                    let mut arg_alloc_sites = Vec::with_capacity(args.len());
                    for _ in 0..args.len() {
                        arg_alloc_sites.push(FxHashSet::default());
                    }
                    Some(arg_alloc_sites) };
                summary.callees.as_mut().unwrap().push(Callee {
                    name: tcx.opt_item_name(def_id).unwrap().to_string(),
                    id: break_def_id(def_id),
                    arg_alloc_sites: arg_alloc_sites
                });
            }
        }
    }

    // Process each function call.
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
            // Enter the core procedure of finding alloc sites for fn args.
            analyze_fn_core(bb, body, get_fn_def_id(f), &mut locals,
                            &mut visited, summary);
        } else {
            panic!("Not a function");
        }
    }

    // TODO: Process the return value.
}

/// Entrance of this module.
pub fn summarize(tcx: TyCtxt<'tcx>, def_id: DefId, summaries: &mut Vec::<Summary>) {
    // Filter out uninterested functions.
    if ignore_fn_dev(tcx, def_id) { return; }

    let name = tcx.opt_item_name(def_id);

    // Init a summary.
    let mut summary = Summary {
        fn_name:  name.unwrap().name.to_ident_string(),
        fn_id: def_id.index.as_u32(),
        callees: None,
        ret: None,
    };

    println!("[summarize_fn]: Processing function {} ({:?})", name.unwrap(), def_id.index);
    let body = tcx.optimized_mir(def_id);
    analyze_fn(tcx, body, &mut summary);

    summaries.push(summary);
}
