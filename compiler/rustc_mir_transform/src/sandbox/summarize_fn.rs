//! Analyze and summarize the information for a function.  The summary will be
//! used for the later inter-procedural analysis that generates a final summary
//! for the whole program.

// use rustc_middle::mir::*;
use rustc_middle::ty::{TyCtxt};
use rustc_hir::def_id::{DefId};
// use rustc_data_structures::fx::{FxHashSet, FxHashMap};
use serde::{Deserialize, Serialize};
use std::fmt;

use super::unsafe_obj::*;

/// Allocation site of a Place can be one of the following cases:
/// 1. Global variable
/// 2. Local variable on the stack
/// 3. Return value of call, including heap allocation and other function call
/// 4. Function argument.
///
/// Currently we only aim to isolate unsafe heap memory, so we only handle
/// case 3 and 4.
#[derive(Serialize, Deserialize)]
enum AllocSite {
    /// Location of a terminator.
    /// Since it will always be a Terminator, can we just use a BasicBlock?
    LocBB(u32),
    /// Local of an argument
    Arg(u32),
}

/// Information of a callee used by a function. Speficially, we collect the
/// allocation sites for all the arguments of a callee. Note that we do not
/// need to distinguish each call to the same callee.
#[derive(Serialize, Deserialize)]
struct Callee {
    /// DefId {DefIndex, CrateNum}
    callee_id: (u32, u32),
    /// The locations of the allocation site for each argument. For example,
    /// [[l0, l1], [l2, _2]] means the caller has two arguments, and the first
    /// argument is computed from Terminator l0 and l1, and the second is from
    /// Terminator l2 and local _2 (an argument or local var).
    arg_alloc_sites: Vec<Vec<AllocSite>>,
}

/// Summary of a function.
#[derive(Serialize, Deserialize)]
pub struct Summary {
    // fn_name is not necessary.
    fn_name: String,
    /// DefIndex
    fn_id: u32,
    /// Callees used in this function
    callees: Option<Vec<Callee>>,
    /// Return value
    ret: Option<Vec<AllocSite>>
}

impl fmt::Debug for Summary {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // TODO: Extract the callee and ret information of a Summary.
        write!(f, "{} (id: {})", self.fn_name, self.fn_id)
    }
}

/// Entrance of this module.
pub fn summarize(tcx: TyCtxt<'tcx>, def_id: DefId, summaries: &mut Vec::<Summary>) {
    // Filter out uninterested functions.
    if ignore_fn(tcx, def_id) { return; }

    let name = tcx.opt_item_name(def_id);

    // Init a summary.
    let summary = Summary {
        fn_name:  name.unwrap().name.to_ident_string(),
        fn_id: def_id.index.as_u32(),
        callees: None,
        ret: None,
    };

    println!("[summarize_fn]: Processing function {} ({:?})", name.unwrap(), def_id);
    let _body = tcx.optimized_mir(def_id);
    // TODO: Analyze and summarize this function.

    summaries.push(summary);
}
