//! Whole-program analysis. Specifically,
//!
//!   1. Build a call graph of the whole program.
//!   2. Find unsafe heap alloc sites inter-procedurally.
//!   3. Find may-unsafe fn arguments and non-heap-alloc calls inter-procedurally.

use std::fs::{read_dir, read_to_string};
use std::fs::{remove_dir_all};
use rustc_data_structures::fx::{FxHashMap, FxHashSet};
use std::{fmt, io};
use std::collections::VecDeque;
use std::process::{Command, Stdio};
use std::fs;

use super::summarize_fn::{Summary, FnID, DefSite};
use super::utils::*;

static _DEBUG: bool = false;

/// A Python script that counts the number of compiled dependency crates.
/// This is not elegant. Ideally we should write the logic of the python script
/// directly in Rust. The current version is only for fast developmenet.
static _COUNT_DEP_PY: &str = "../../misc/scripts/compiled_dep_crates.py";

/// A node in the call graph.
///
/// It is semantically more clear to recursively use CallGraphNode for a node's
/// callers and callees. However, it might not be possible to do so using safe
/// Rust. See: https://github.com/URSec/SURust/issues/3
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

impl<'a> CallGraph<'a> {
    /// Get the CallGraphNode of a function.
    fn get(&self, fn_id: &FnID) -> &CallGraphNode<'_> {
        return &self.0.get(fn_id).unwrap();
    }

    /// Get a function's callers.
    fn get_callers(&self, fn_id: &FnID) -> &FxHashSet<FnID> {
        return &CallGraph::get(self, fn_id).callers;
    }
}

/// A def site in the global perspective.
#[derive(Hash, Eq, Clone, Copy)]
struct GlobalDefSite {
    fn_id: FnID,
    def_site: DefSite,
}

impl PartialEq for GlobalDefSite {
    fn eq(&self, other: &GlobalDefSite) -> bool {
        return self.fn_id == other.fn_id && self.def_site == other.def_site;
    }
}

/// Whole-program summary.
pub type WPSummary = FxHashMap<FnID, FxHashSet<DefSite>>;

/// All the unsafe sources.
pub(crate) type UnsafeSources = Vec::<(FnID, FxHashSet<DefSite>)>;

/// Count the number of summary files in the temporary summary directory.
/// Essentially, it gets the result of `ls | wc -l` and converts it to an u32.
#[allow(dead_code)]
fn curr_dep_crate_num(summary_dir: &str) -> io::Result<u32> {
    let ls = Command::new("ls").arg(summary_dir).stdout(Stdio::piped()).spawn()?;
    let wc = Command::new("wc").arg("-l").stdin(ls.stdout.unwrap()).output()?;
    Ok(String::from_utf8(wc.stdout).unwrap().as_str().trim().parse::<u32>().unwrap())
}

/// Read the fn summaries of each crate from the summary files, and then put
/// them to a HashMap for later use.
fn read_summaries() -> io::Result<FxHashMap<FnID, Summary>> {
    let summary_dir = get_summary_dir();
    // When the main crate is being compiled, all its dependent should be ready.

    let mut dep_summaries = FxHashMap::<FnID, Summary>::default();
    // Collect summaries.
    for summaries in read_dir(summary_dir)? {
        let summaries_str = read_to_string(summaries?.path())?;
        let summaries_vec = serde_json::from_str::<Vec<Summary>>(&summaries_str)?;
        for summary in summaries_vec {
            // Is it deep copy for summary here?
            dep_summaries.insert(summary.fn_id, summary);
        }
    }

    Ok(dep_summaries)
}

/// Write the result of the WPA to a file that will be used by all compile units.
///
/// Since we just deleted the directory of summaries, here we simply put
/// the overall summary file in "/tmp".
fn write_wpa_summary(summary: WPSummary) {
    // We need to move the analysis results to a vector because the original
    // summary's key is FnID, which is not a string and thus cannot be
    // serialized by serde_json.
    let mut summary_vec = UnsafeSources::new();
    for (fn_id, def_sites) in summary {
        summary_vec.push((fn_id, def_sites));
    }
    let serialized = serde_json::to_string(&summary_vec).unwrap();
    fs::write(get_wp_summary_path(), &serialized).expect(
        "Write whole-program summary to file");
}

/// Build the call graph using all the fn summaries.
fn build_call_graph<'a>(summaries: &'a FxHashMap<FnID, Summary>) -> CallGraph<'a> {
    let mut cg = CallGraph(FxHashMap::default());
    for (caller_id, summary) in summaries {
        // Create a new CallGraphNode for the current fn if not exist.
        if !cg.0.contains_key(caller_id) {
            cg.0.insert(*caller_id, CallGraphNode {
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
                callee_node.callers.insert(*caller_id);
            } else {
                let mut callee_node = CallGraphNode {
                    crate_name: &callee.crate_name,
                    fn_name: &callee.fn_name,
                    callees: FxHashSet::default(),
                    callers: FxHashSet::default()
                };
                callee_node.callers.insert(*caller_id);
                cg.0.insert(callee_id, callee_node);
            }
        }
    }

    cg
}

/// Update the whole-program summary with a newly found def site.
fn update_wp_summary(wp_summary: &mut WPSummary,
                     fn_id: &FnID, def_site: &DefSite) {
    if let Some(def_sites) = wp_summary.get_mut(fn_id) {
        def_sites.insert(*def_site);
    } else {
        let mut def_sites = FxHashSet::default();
        def_sites.insert(*def_site);
        wp_summary.insert(*fn_id, def_sites);
    }
}

/// Find unsafe heap allocation sites. We use a worklist-based algorithm to
/// handle the recursive nature of the process of finding def site. There are
/// four variants of DefSite. HeapAlloc means a heap alloc site is found.
/// NativeCall is ignored because we do not analyze native libraries.
/// OtherCall is the most complex case. We need to find the def site for the
/// return value of the callee, and those def sites have two types:
/// arguments of the callee, which come from the def sites in the body of the
/// caller, and non-argument def sites in the body of the callee.
/// The last type is Arg. We need to examine all the callers of the
/// currently processed function to find the def sites in the callers that
/// contribute to the target arguments of the call to the callee.
fn find_unsafe_alloc<'a>(summaries: &FxHashMap<FnID, Summary>,
                         cg: &CallGraph<'a>,
                         wp_summary: &mut WPSummary) {
    // A worklist of GlobalDefSite to be processed.
    let mut to_process = VecDeque::<GlobalDefSite>::new();
    // Record processed def sites to prevent infinite loop.
    let mut processed = FxHashSet::<GlobalDefSite>::default();

    // Init: Put unsafe def sites collected from unsafe_def to the worklist.
    for (fn_id, summary) in summaries {
        if let Some(unsafe_defs) = &summary.unsafe_defs {
            for def_site in unsafe_defs {
                to_process.push_back(GlobalDefSite {
                    fn_id: *fn_id,
                    def_site: *def_site
                });
            }
        }
    }

    // Worklist-based algorithm.
    while !to_process.is_empty() {
        let def_site_glob = to_process.pop_front().unwrap();
        if processed.contains(&def_site_glob) {
            continue;
        }
        processed.insert(def_site_glob);

        let (fn_id, def_site) = (def_site_glob.fn_id, def_site_glob.def_site);
        match def_site {
            DefSite::HeapAlloc(_) => {
                // Found a heap allocation site. Put it to results.
                update_wp_summary(wp_summary, &fn_id, &def_site);
            },
            DefSite::NativeCall(_) => {
                // No need to do anything as we do not analyze native fn.
            },
            DefSite::OtherCall(bb) => {
                // Find all the DefSite that contribute to the return value
                // of the callee in bb. There are might be multiple callees
                // due to trait object.
                let caller_summary = summaries.get(&fn_id).unwrap();
                for callee in caller_summary.get_callee_bb(bb) {
                    let callee_id = callee.fn_id;
                    if caller_summary.is_foreign_callee(&callee_id) {
                        // Skip FFI calls.
                        continue;
                    }
                    let callee_summary = summaries.get(&callee_id);
                    if callee_summary.is_none() {
                        if caller_summary.is_dyn_callee(&callee_id) {
                            continue;
                        }
                        panic!("Cannot find callee {}, called by {}",
                            callee.name(), caller_summary.name());
                    }

                    let callee_summary = callee_summary.unwrap();
                    for def_site in &callee_summary.ret_defs.0 {
                        // Examine non-arg contributors to the return value.
                        match def_site {
                            DefSite::HeapAlloc(_) => {
                                // Found a heap alloc site.
                                update_wp_summary(wp_summary, &callee_id, &def_site);
                            },
                            DefSite::OtherCall(_) => {
                                to_process.push_back(GlobalDefSite {
                                    fn_id: callee_id,
                                    def_site: *def_site
                                });
                            },
                            _ => {
                                panic!("Not a DefSite::HeapAlloc or OtherCall");
                            }
                        }
                    }
                    for def_site in &callee_summary.ret_defs.1 {
                        // Examine argument contributors to the return value.
                        match def_site {
                            DefSite::Arg(arg) => {
                                for arg_def in callee.get_arg_defs(bb, *arg) {
                                    to_process.push_back(GlobalDefSite {
                                        fn_id: fn_id,
                                        def_site: *arg_def,
                                    });
                                }
                            },
                            _ => {
                                panic!("Not a DefSite::Arg");
                            }
                        }
                    }

                }
            },
            DefSite::Arg(arg_loc) => {
                // Examine all callers of fn_id to find their corresponding
                // calls to fn_id, and then find the def sites of the target
                // argument in the calls.
                for caller_id in cg.get_callers(&fn_id) {
                    let caller_sumamry = summaries.get(caller_id).unwrap();
                    let callee = caller_sumamry.get_callee_global(&fn_id);
                    for arg_defs in callee.arg_defs.values() {
                        for def_site in &arg_defs[(arg_loc - 1) as usize] {
                            to_process.push_back(GlobalDefSite {
                                fn_id: *caller_id,
                                def_site: *def_site,
                            });
                        }
                    }
                }
            }
        }
    }

    if _DEBUG {
        println!("Found {} unsafe allocation sites", wp_summary.len());
    }
}

/// Find unsafe fn arguments and non-heap-alloc calls that return unsafe value.
/// This function, combined with find_unsafe_alloc, prepares unsafe sources
/// for later local analysis to find unsafe memory accesses.
///
/// Specifically, in addition to the unsafe heap allocation sites that were
/// found before by find_unsafe_alloc, it finds two more unsafe sources:
/// unsafe function arguments and unsafe non-heap-alloc calls.
///
/// Similar to find_unsafe_alloc, this function also uses a worklist-based
/// algorithm. It starts with all the unsafe heap allocation sites found before.
/// It examines two situations. First, if an unsafe souce is used as an argument
/// to a non-heap-alloc call, the argument of the callee is also an unsafe
/// resouce and the algorithm puts the argument to the worklist.
/// Second, if an unsafe source contributes to the return value of the function
/// that contains it, then for all the callers of this function, the calls to
/// it are also unsafe sources.
fn find_unsafe_arg_call<'a>(summaries: &FxHashMap<FnID, Summary>,
                            cg: &CallGraph<'a>,
                            wp_summary: &mut WPSummary) {
    // A worklist of GlobalDefSite to be processed.
    let mut to_process = VecDeque::<GlobalDefSite>::new();
    // Record processed GlobalDefSite to prevent infinite loop.
    let mut processed = FxHashSet::<GlobalDefSite>::default();

    // Init: Put all the unsafe heap allocation sites to the worklist.
    for (fn_id, def_sites) in wp_summary.iter() {
        for def_site in def_sites {
            // Ensure all the DefSite collected before are HeapAlloc.
            assert!(matches!(*def_site, DefSite::HeapAlloc(_)),
                "Not a heap allocation");
            to_process.push_back(GlobalDefSite {
                fn_id: *fn_id,
                def_site: *def_site
            });
        }
    }

    // A worklist-based algorithm.
    while !to_process.is_empty() {
        let def_site_glob = to_process.pop_front().unwrap();
        if !processed.insert(def_site_glob) {
            continue;
        }

        // For the currently-processed unsafe GlobalDefSite, get the FnID of the
        // function that contains it, and the local DefSite of it.
        let (fn_id, def_site) = (def_site_glob.fn_id, def_site_glob.def_site);
        match def_site {
            DefSite::HeapAlloc(_) | DefSite::OtherCall(_) | DefSite::Arg(_) => {
                let fn_summary = summaries.get(&fn_id);
                if fn_summary.is_none() {
                    // It is possible that fn_id is a native library function.
                    // This happens for DefSite:Arg.
                    continue;
                }
                let fn_summary = fn_summary.unwrap();

                // Find calls in this function that use the unsafe source as an
                // argument, and put the corresponding argument to the worklist.
                for callee in &fn_summary.callees {
                    for (bb, all_arg_defs) in &callee.arg_defs {
                        match def_site {
                            DefSite::HeapAlloc(unsafe_call) |
                            DefSite::OtherCall(unsafe_call) => {
                                if *bb == unsafe_call {
                                    // Skip the unsafe call iteself.
                                    continue;
                                }
                            },
                            _ => {}
                        }

                        // Check if the def sites for any argument of a call
                        // contains the target unsafe def_site.
                        for arg in 1..=all_arg_defs.len() {
                            if all_arg_defs[arg - 1].contains(&def_site) {
                                let unsafe_arg = GlobalDefSite {
                                    fn_id: callee.fn_id,
                                    def_site: DefSite::Arg(arg as u32)
                                };
                                update_wp_summary(wp_summary, &unsafe_arg.fn_id,
                                                  &unsafe_arg.def_site);
                                to_process.push_back(unsafe_arg);
                            }
                        }
                    }
                }

                // If the current unsafe def_site contributes to the return of
                // the current function, find all calls to this function and
                // put them to the worklist.
                if fn_summary.ret_defs_contains(&def_site) {
                    for caller_id in cg.get_callers(&fn_id) {
                        let caller_summary = summaries.get(caller_id).unwrap();
                        let callee = caller_summary.get_callee_global(&fn_id);
                        for call_site in callee.arg_defs.keys() {
                            let unsafe_call_site = GlobalDefSite {
                                fn_id: *caller_id,
                                def_site: DefSite::OtherCall(*call_site)
                            };
                            update_wp_summary(wp_summary, &caller_id,
                                              &unsafe_call_site.def_site);
                            to_process.push_back(unsafe_call_site);
                        }
                    }
                }
            },
            _ => {}
        }
    }
}

/// Dump the call graph of the main crate for debugging.
fn debug(main_summaries: Vec<Summary>) {
    // From directly invoking rustc on an application.
    let mut summaries = FxHashMap::<FnID, Summary>::default();
    for summary in main_summaries {
        summaries.insert(summary.fn_id, summary);
    }
    build_call_graph(&summaries).dump();
    return;
}

impl<'a> CallGraph<'a> {
    /// Print the call graph of the program.
    fn dump(&self) {
        for node in self.0.values() {
            println!("{}:{} calls:", node.crate_name, node.fn_name);
            if node.callees.is_empty() {
                println!("Nothing");
            } else {
                for callee_id in &node.callees {
                    let callee_node = self.get(&callee_id);
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
    if dep_summaries.is_err() {
        panic!("Failed to read in function summary files of dependent crates");
    }

    let mut all_summaries = dep_summaries.unwrap();
    for summary in main_summaries {
        all_summaries.insert(summary.fn_id, summary);
    }

    // Build a call graph.
    let cg = build_call_graph(&all_summaries);

    // Whole-program summary for later analysis to find unsafe memory accesses.
    // Question: Will it be a little faster to use Vec<DefSite> in the HashMap?
    let mut wp_summary = WPSummary::default();

    // Find unsafe heap allocations.
    find_unsafe_alloc(&all_summaries, &cg, &mut wp_summary);

    // Find may-unsafe function arguments and non-heap-alloc calls.
    find_unsafe_arg_call(&all_summaries, &cg, &mut wp_summary);

    // Delete the summary folder. This is necessary because a compilation
    // may happen to have the same ppid as one older compilation.
    let _ = remove_dir_all(get_summary_dir());

    // Write the final whole-program summary to a file for later analysis.
    write_wpa_summary(wp_summary);
}
