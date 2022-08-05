//! Analyze and summarize a function. Speficially, we analyze each function to
//! find the following information:
//!
//!   1. All callees of the fn. This will be used for later call graph analysis.
//!   2. Definition sites of each argument of a function call.
//!   3. Definition sites of each Place used in unsafe code.
//!
//! The summary will be used later for the inter-procedural analysis that
//! generates a final summary for the whole program, which will then be used
//! to do memory isolation.

crate mod calls;
crate mod unsafe_def;

use rustc_middle::ty::{TyCtxt};
use rustc_hir::def_id::{DefId, LOCAL_CRATE};
use rustc_data_structures::fx::{FxHashSet, FxHashMap};
use serde::{Deserialize, Serialize};
use std::fmt;
use std::fs;

use super::utils::*;

static _DEBUG: bool = false;

/// Definition site of a Place can be one of the following cases:
///
/// 1. Global variable
/// 2. Local variable on the stack
/// 3. Return value of call, including heap allocation and other function call
/// 4. Function argument, which could originally come from 1, 2, or 3
///
/// Currently we only aim to isolate unsafe heap memory, so we only handle
/// case 3 and 4.
///
/// We distinguish the types of calls. This is necessary in later WPA.
/// Specifically, if we see a Place e.g., _10, is used by unsafe code, and
/// _10 is defined by a function call, i.e., _10 = func(...), we need to figure
/// out what func is. If func is a heap allocation function such as Vec::new(),
/// then we have found an unsafe heap allocation site. If func is a native
/// library function, no further actions will be executed because we do not
/// analyze native library functions. Otherwise, func is a normal function
/// and the analysis should go to query what contribute(s) to the return value
/// of func. Note that there is no need to analyze the arguments of func in WPA
/// because unsafe_def has done it.
#[derive(Hash, Eq, Serialize, Deserialize, Copy, Clone)]
crate enum DefSite {
    // Since a call is always a Terminator, we use its BB's index as its location.
    /// Location of a call to a heap allocation.
    HeapAlloc(u32),
    /// Location of a call to a native library function.
    NativeCall(u32),
    /// Location of a call to other functions.
    OtherCall(u32),
    /// Local of an argument
    Arg(u32),
}

impl PartialEq for DefSite {
    fn eq(&self, other: &DefSite) -> bool {
        match (self, other) {
            (DefSite::HeapAlloc(ha), DefSite::HeapAlloc(ha1)) => ha == ha1,
            (DefSite::NativeCall(nc), DefSite::NativeCall(nc1)) => nc == nc1,
            (DefSite::OtherCall(oc), DefSite::OtherCall(oc1)) => oc == oc1,
            (DefSite::Arg(arg), DefSite::Arg(arg1)) => arg == arg1,
            _ => false
        }
    }
}

impl fmt::Debug for DefSite {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let (message, loc) = match self {
            DefSite::HeapAlloc(loc) | DefSite::NativeCall(loc) |
                DefSite::OtherCall(loc) => ("BB", loc),
            DefSite::Arg(arg) => ("Arg", arg)
        };
        write!(f, "{}: {}", message, loc)
    }
}

/// The def_id::DefPathHash, i.e., Fingerprint, of a function.
///
/// This is not as beautiful as it should be: Ideally we should directly use
/// DefPathHash instead of the inner representation. However, we would then
/// have to implement Serialize & Deserialize for DefPathHash. Serialize is
/// usually easy to implement but Deserialize is more complex. This is similar
/// to why we use u32 a lot to represent BasicBlock and def_id's components.
/// We should fix these issues later.
#[derive(Serialize, Deserialize, Hash, Eq, Copy, Clone)]
crate struct FnID(crate (u64, u64));

impl PartialEq for FnID {
    fn eq(&self, other: &FnID) -> bool {
        return self.0 == other.0;
    }
}

/// Information of a callee used by a function. Speficially, we collect the
/// allocation/declaration sites for all the arguments of a callee.
#[derive(Serialize, Deserialize)]
crate struct Callee {
    /// Unique ID of a function that is stable across compilation sessions.
    crate fn_id: FnID,
    pub fn_name: String,
    pub crate_name: String,
    /// DefId (DefIndex, CrateNum)
    crate def_id: (u32, u32),
    /// The basic block of a call and def sites for each argument. For example,
    /// (bb3, [[bb0, bb1], [bb2, _2]]) means the callee is called at BB3, and
    /// the call has two arguments, and the first argument is computed from the
    /// Terminator of BB0 and BB1, and the second is from the Terminator of bb2
    /// and argument _2.
    crate arg_defs: FxHashMap<u32, Vec<FxHashSet<DefSite>>>,
}

impl fmt::Debug for Callee {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} (ID:{:?}; arg_defs: {:?}", self.fn_name, self.def_id,
            self.arg_defs)
    }
}

/// Summary of a function.
#[derive(Serialize, Deserialize)]
pub struct Summary {
    /// The function's unique ID (fingerprint).
    crate fn_id: FnID,
    pub fn_name: String,
    pub crate_name: String,
    /// DefId
    def_id: (u32, u32),
    /// Callees used in this function. Key is DefId.
    crate callees: Vec<Callee>,
    /// DefSite of Place in return value (CallSite, Arg)
    crate ret_defs: (FxHashSet<DefSite>, Vec::<DefSite>),
    /// DefSite of Place in unsafe code
    crate unsafe_defs: Option<FxHashSet<DefSite>>
}

impl Summary {
    crate fn get_callee(&self, fn_id: &FnID) -> &Callee {
        for callee in &self.callees {
            if callee.fn_id == *fn_id {
                return callee;
            }
        }
        panic!("Cannot find the target callee");
    }
}

impl fmt::Debug for Summary {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}::{} {:?}:\nCallees: {:?}\nReturn: {:?}\n", self.crate_name,
            self.fn_name, self.def_id, self.callees, self.ret_defs)
    }
}

/// Entrance of this module.
pub fn summarize(tcx: TyCtxt<'tcx>, def_id: DefId, summaries: &mut Vec::<Summary>) {
    // Filter out uninterested functions.
    if ignore_fn(tcx, def_id) { return; }

    // Init a summary.
    let crate_name = get_crate_name(def_id);
    let fn_name = tcx.opt_item_name(def_id).unwrap().name.to_ident_string();
    if _DEBUG {
        println!("[summarize_fn::calls]: Processing fn {}", tcx.def_path_debug_str(def_id));
    }

    let mut summary = Summary {
        fn_id: get_fn_fingerprint(tcx, def_id),
        fn_name: fn_name,
        crate_name: crate_name,
        def_id: break_def_id(def_id),
        callees: Vec::new(),
        ret_defs: (FxHashSet::default(), Vec::new()),
        unsafe_defs: None
    };

    let body = tcx.optimized_mir(def_id);

    // Analyze calls and return values.
    calls::analyze_fn(tcx, body, &mut summary);

    // Find the def sites of Place used in unsafe code.
    unsafe_def::analyze_fn(body, &mut summary);

    summaries.push(summary);
}

/// Check if a Summary is for the main() fn.
pub fn is_main(tcx: TyCtxt<'tcx>, summary: &Summary) -> bool {
    if summary.fn_name != "main" { return false; }

    // Check signature. There might be other main fn which have different
    // signatures than the main() in the application itself.
    let body = tcx.optimized_mir(assemble_def_id(summary.def_id));
    if body.arg_count == 0 && is_empty_ty(body.return_ty()) { return true; }
    return false;
}

/// Write the summaries of a crate to a temporary file.
//
// Jie Zhou: For some unknown reason(s), besides the directory for the
// crates used in the target app, there may be extra directories to be
// created and those directories contain files named probe{1,2,3..}.
// Some probe* files are empty. Don't know why they are generated and
// what they are exactly.
pub fn write_summaries_to_file(tcx: TyCtxt<'tcx>, summaries: &Vec<Summary>) {
    let local_crate_name = get_local_crate_name();
    if ignore_build_crate(&local_crate_name) {
        return;
    }

    let dir = get_summary_dir();
    // Create the directory for the summary files of all dependent crates.
    // No need to sync. It is harmless to fail for "File exists".
    let _ = fs::create_dir(&dir);

    // Serialize summaries to a string and write the string to a file.
    let serialized = serde_json::to_string(&summaries).unwrap();
    let output_file = dir + "/" + &local_crate_name + "-" +
        &tcx.stable_crate_id(LOCAL_CRATE).to_u64().to_string();
    fs::write(output_file.as_str(), &serialized).
        expect("Failed to write summaries");

     if _DEBUG {
         println!("\nSerialized Summaries: {:?}", serialized);
     }
}
