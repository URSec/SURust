use crate::MirPass;
use rustc_middle::mir::*;
use rustc_middle::ty::{TyCtxt};

// This pass looks for all memory objects used by unsafe code.
pub struct UnsafeObj;

impl<'tcx> MirPass<'tcx> for UnsafeObj {
    fn run_pass(&self, _tcx: TyCtxt<'tcx>, _body: &mut Body<'tcx>) {

    }
}
