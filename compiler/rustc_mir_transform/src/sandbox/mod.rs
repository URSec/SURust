//! Sandboxing unsafe Rust
//! This module serves three goals:
//! 1. Identify unsafe memory objects.
//! 2. Identify unsafe operations.
//! 3. Sandbox unsafe memory and operations.
//!
//! However, after step 1, we need the compiler to stop parallel compilation
//! and do a summary-based inter-procedural analysis to propagate the use of
//! unsafe objects (taint propagation) based on what we get from step 1.

pub mod unsafe_obj;
pub mod summarize_fn;
crate mod debug;
crate mod database;
