// Copyright 2015 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! This pass just dumps MIR at a specified point.

use std::borrow::Cow;
use std::fmt;
use std::fs::File;
use std::io;

use rustc::mir::Mir;
use rustc::mir::transform::{MirPass, MirPassIndex, MirSource, MirSuite, PassHook};
use rustc::session::config::{OutputFilenames, OutputType};
use rustc::ty::TyCtxt;
use util as mir_util;

pub struct Marker(pub &'static str);

impl MirPass for Marker {
    fn name<'a>(&'a self) -> Cow<'a, str> {
        Cow::Borrowed(self.0)
    }

    fn run_pass<'a, 'tcx>(&self,
                          _tcx: TyCtxt<'a, 'tcx, 'tcx>,
                          _source: MirSource,
                          _mir: &mut Mir<'tcx>)
    {
    }
}

pub struct Disambiguator {
    is_after: bool
}

impl fmt::Display for Disambiguator {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        let title = if self.is_after { "after" } else { "before" };
        write!(formatter, "{}", title)
    }
}

pub struct DumpMir;

impl PassHook for DumpMir {
    fn on_mir_pass<'a, 'tcx: 'a>(&self,
                                 tcx: TyCtxt<'a, 'tcx, 'tcx>,
                                 suite: MirSuite,
                                 pass_num: MirPassIndex,
                                 pass_name: &str,
                                 source: MirSource,
                                 mir: &Mir<'tcx>,
                                 is_after: bool)
    {
        if mir_util::dump_enabled(tcx, pass_name, source) {
            mir_util::dump_mir(tcx,
                               Some((suite, pass_num)),
                               pass_name,
                               &Disambiguator { is_after },
                               source,
                               mir,
                               |_, _| Ok(()) );
            for (index, promoted_mir) in mir.promoted.iter_enumerated() {
                let promoted_source = MirSource::Promoted(source.item_id(), index);
                mir_util::dump_mir(tcx,
                                   Some((suite, pass_num)),
                                   pass_name,
                                   &Disambiguator { is_after },
                                   promoted_source,
                                   promoted_mir,
                                   |_, _| Ok(()) );
            }
        }
    }
}

pub fn emit_mir<'a, 'tcx>(
    tcx: TyCtxt<'a, 'tcx, 'tcx>,
    outputs: &OutputFilenames)
    -> io::Result<()>
{
    let path = outputs.path(OutputType::Mir);
    let mut f = File::create(&path)?;
    mir_util::write_mir_pretty(tcx, None, &mut f)?;
    Ok(())
}
