//! Whole-program analysis. Specifically,
//!
//!   1. build a call graph of the whole program.
//!   2. find unsafe heap alloc sites inter-procedurally.

use std::fs::{read_dir, read_to_string, remove_dir_all};
use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use std::{fmt, io};

use super::summarize_fn::{Summary, FnID};
use super::utils::*;

static _DEBUG: bool = false;

struct CallGraphNode<'a> {
    // crete_name and fn_name are for debugging. No need for them for analysis.
    crate_name: &'a str,
    fn_name: &'a str,
    callees: FxHashSet<FnID>,
    callers: FxHashSet<FnID>,
}

impl fmt::Debug for CallGraphNode<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}:{}", self.crate_name, self.fn_name)
    }
}

/// Call graph of the whole program.
struct CallGraph<'a> (FxHashMap<FnID, CallGraphNode<'a>>);

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

/// Build the call graph based using all the fn summaries.
fn build_call_graph(summaries: &'a Vec<Vec<Summary>>) -> CallGraph<'a> {
    let mut cg = CallGraph(FxHashMap::default());
    for summaries_crate in summaries {
        for summary in summaries_crate {
            let caller_id = summary.fn_id;
            // Create a new CallGraphNode for the current fn if not exist.
            if !cg.0.contains_key(&caller_id) {
                cg.0.insert(caller_id, CallGraphNode {
                    crate_name: &summary.crate_name,
                    fn_name: &summary.fn_name,
                    callees: FxHashSet::default(),
                    callers: FxHashSet::default()
                });
            }

            // Iterate over this fn's callee list and writes each caller-callee
            // data to CallGraph.
            for callee in &summary.callees {
                let callee_id = callee.fn_id;
                // Add callee to caller's callee set.
                cg.0.get_mut(&caller_id).unwrap().callees.insert(callee_id);
                // Add caller to callee's caller set.
                if let Some(callee_node) = cg.0.get_mut(&callee_id) {
                    callee_node.callers.insert(caller_id);
                } else {
                    let mut callee_node = CallGraphNode {
                        crate_name: &callee.crate_name,
                        fn_name: &callee.fn_name,
                        callees: FxHashSet::default(),
                        callers: FxHashSet::default()
                    };
                    callee_node.callers.insert(caller_id);
                    cg.0.insert(callee_id, callee_node);
                }
            }
        }
    }

    cg
}

/// Dump the call graph of the main crate for debugging.
fn debug(main_summaries: Vec<Summary>) {
    // From directly invoking rustc on an application.
    let summaries = vec![main_summaries];
    build_call_graph(&summaries).dump();
    return;
}

impl CallGraph<'a> {
    /// Print the call graph of the program.
    fn dump(&self) {
        for node in self.0.values() {
            println!("{}:{} calls:", node.crate_name, node.fn_name);
            if node.callees.is_empty() {
                println!("Nothing");
            } else {
                for callee_id in &node.callees {
                    let callee_node = self.0.get(&callee_id).unwrap();
                    print!("{:?}; ", callee_node);
                }
                println!();
            }
            println!();
        }
    }
}

/// Entrance of this module.
///
/// We currently only develop for projects built by invoking cargo.
/// If an app is compiled directly by invoking rustc, there would be no
/// summary files generated in /tmp/rust-sandbox-ppid.
pub fn wpa(main_summaries: Vec<Summary>) {
    if _DEBUG { debug(main_summaries); return; }

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
