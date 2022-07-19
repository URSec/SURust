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
use rustc_hir::def_id::{DefId};
use rustc_data_structures::fx::{FxHashSet};
use serde::{Deserialize, Serialize};
use std::fmt;
use std::fs;
use std::path::Path;

use super::utils::*;
use calls::*;

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
#[derive(Hash, Eq, Serialize, Deserialize)]
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


/// Summary of a function.
#[derive(Serialize, Deserialize)]
pub struct Summary {
    pub fn_name: String,
    pub crate_name: String,
    /// DefId
    id: (u32, u32),
    /// Callees used in this function. Key is DefId.
    crate callees: Vec<Callee>,
    /// DefSite of Place in Return value
    ret_def_sites: FxHashSet<DefSite>,
    /// DefSite of Place in unsafe code
    unsafe_def_sites: Option<FxHashSet<DefSite>>
}

impl fmt::Debug for Summary {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}::{} {:?}:\nCallees: {:?}\nReturn: {:?}\n", self.crate_name,
            self.fn_name, self.id, self.callees, self.ret_def_sites)
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
        println!("[summarize_fn::calls]: Processing fn {}::{}", crate_name, fn_name);
    }

    let mut summary = Summary {
        fn_name: fn_name,
        crate_name: crate_name,
        id: break_def_id(def_id),
        callees: Vec::new(),
        ret_def_sites: FxHashSet::default(),
        unsafe_def_sites: None
    };

    let body = tcx.optimized_mir(def_id);

    // Analyze calls and return values.
    calls::analyze_fn(body, &mut summary);

    // Find the def sites of Place used in unsafe code.
    unsafe_def::analyze_fn(body, &mut summary);

    summaries.push(summary);
}

/// Check if a Summary is for the main() fn.
pub fn is_main(tcx: TyCtxt<'tcx>, summary: &Summary) -> bool {
    if summary.fn_name != "main" { return false; }

    // Check signature. There might be other main fn which have different
    // signatures than the main() in the application itself.
    let body = tcx.optimized_mir(create_defid(summary.id));
    if body.arg_count == 0 && is_empty_ty(body.return_ty()) { return true; }
    return false;
}

/// Write the summaries of a crate to a temporary file.
pub fn write_summaries_to_file(summaries: &Vec<Summary>) {
    let local_crate_name = get_local_crate_name();
    if ignore_build_crate(&local_crate_name) { return; }

    let dir = get_summary_dir();
    if !Path::new(&dir).exists() {
        // Jie Zhou: For some unknown reason(s), besides the directory for the
        // crates used in the target app, there may be extra directories to be
        // created and those directories contain files named probe{1,2,3..}.
        // Some probe* files are empty. Don't know why they are generated and
        // what they are exactly.
        fs::create_dir(&dir).
            expect(&(["Failed to mkdir for crate ", &local_crate_name].join("")));
    }

    // Serialize summaries to a string and write the string to a file.
    let serialized = serde_json::to_string(&summaries).unwrap();
    fs::write(dir + "/" + &local_crate_name, &serialized).
        expect("Failed to write summaries");

     if _DEBUG {
         println!("\nSerialized Summaries: {:?}", serialized);
     }
}
