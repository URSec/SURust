//! Whole-program analysis. Specifically, we analyze the call graph.

static _DEBUG: bool = false;

use std::fs::{read_dir,read_to_string};
use std::io;

use super::summarize_fn::*;
use super::lib::*;

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

/// Entrance of this module.
pub fn wpa(_main_summaries: Vec<Summary>) {
    let dep_summaries = read_summaries();
    if dep_summaries.is_err() {
        // We currently only develop for projects built by invoking cargo.
        // If an app is compiled directly by invoking rustc, there would be no
        // temporary summary files generated in /tmp/rust-sandbox-ppid.
        return;
    }

    // TODO: Start to do analysis.
}
