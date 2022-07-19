//! Whole-program analysis. Specifically,
//!
//!   1. build a call graph of the whole program.
//!   2. find unsafe heap alloc sites inter-procedurally.

use std::fs::{read_dir,read_to_string,remove_dir_all};
use rustc_data_structures::fx::{FxHashMap,FxHashSet};
use std::{fmt,io};

use super::summarize_fn::{Summary};
use super::utils::*;

static _DEBUG: bool = false;

#[derive(Hash, Eq, Clone, Copy)]
struct FnID<'tcx> {
    crate_name: &'tcx str,
    fn_name: &'tcx str,
}

struct CallGraphNode<'tcx> {
    func: FnID<'tcx>,
    callees: FxHashSet<FnID<'tcx>>,
    callers: FxHashSet<FnID<'tcx>>,
}

struct CallGraph<'tcx> (FxHashMap<FnID<'tcx>, CallGraphNode<'tcx>>);

impl PartialEq for FnID<'_> {
    fn eq(&self, other: &FnID<'_>) -> bool {
        return self.crate_name == other.crate_name &&
               self.fn_name == other.fn_name;
    }
}

impl fmt::Debug for FnID<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}:{}", self.crate_name, self.fn_name)
    }
}

/// Read the fn summaries of each crate from the summary files, and then
/// deserialize the summaries to a vector of Summary.
fn read_summaries() -> io::Result<Vec::<Vec<Summary>>> {
    let mut dep_summaries = Vec::<Vec<Summary>>::new();

    // Collect summaries.
    for fn_summaries in read_dir(get_summary_dir())? {
        let summaries = read_to_string(fn_summaries?.path())?;
        dep_summaries.push(serde_json::from_str::<Vec<Summary>>(&summaries)?);
    }

    Ok(dep_summaries)
}

/// Build the call graph based on all the fn summaries.
fn build_call_graph(summaries: &'tcx Vec<Vec<Summary>>) -> CallGraph<'tcx> {
    let mut cg = CallGraph(FxHashMap::default());
    for summaries_crate in summaries {
        for summary in summaries_crate {
            let fn_id = FnID {
                crate_name: summary.crate_name.as_str(),
                fn_name: summary.fn_name.as_str()
            };

            // Create a new CallGraphNode for the current fn if not exist.
            if !cg.0.contains_key(&fn_id) {
                cg.0.insert(fn_id, CallGraphNode {
                    func: fn_id,
                    callees: FxHashSet::default(),
                    callers: FxHashSet::default()
                });
            }

            // Iterate over this fn's callee list and writes each caller-callee
            // data to CallGraph.
            for callee in &summary.callees {
                let callee_id = FnID {
                    crate_name: callee.crate_name.as_str(),
                    fn_name: callee.fn_name.as_str()
                };
                // Add callee.
                cg.0.get_mut(&fn_id).unwrap().callees.insert(callee_id);
                // Add caller.
                if let Some(callee_node) = cg.0.get_mut(&callee_id) {
                    callee_node.callers.insert(fn_id);
                } else {
                    let mut callee_node = CallGraphNode {
                        func: callee_id,
                        callees: FxHashSet::default(),
                        callers: FxHashSet::default()
                    };
                    callee_node.callers.insert(fn_id);
                    cg.0.insert(callee_id, callee_node);
                }
            }
        }
    }

    if _DEBUG { print_cg(&cg); }

    cg
}

/// Entrance of this module.
///
/// We currently only develop for projects built by invoking cargo.
/// If an app is compiled directly by invoking rustc, there would be no
/// summary files generated in /tmp/rust-sandbox-ppid.
pub fn wpa(main_summaries: Vec<Summary>) {
    let dep_summaries = read_summaries();
    if dep_summaries.is_err() { return; }

    let mut all_summaries = dep_summaries.unwrap();
    all_summaries.push(main_summaries);

    // Buld a call graph.
    let _cg = build_call_graph(&all_summaries);

    // Delete the summary folder. This is necessayr because a compilation
    // may happen to have the same ppid as one older compilation.
    let _ = remove_dir_all(get_summary_dir());
}

/// Print the call graph of the program.
fn print_cg(cg: &CallGraph<'_>) {
    for (fn_id, node) in &cg.0 {
        if fn_id.fn_name == "main" {
            println!("Fn: {}:{}", node.func.crate_name, node.func.fn_name);
            println!("Callees: {:?}", node.callees);
        }
    }
}
