//! Analyze each function to find its callees, the definition site(s) of each
//! argument of each callee, and def site(s) for the return value.

use rustc_middle::mir::*;
use rustc_middle::ty::{self, TyCtxt, InstanceDef};
use rustc_hir::def_id::{DefId};
use rustc_data_structures::fx::{FxHashSet, FxHashMap};

use crate::sandbox::utils::*;
use super::{DefSite, Summary, Callee};

static _DEBUG: bool = false;

impl Callee {
    /// Add a new pair of (bb, arg_defs) to a Calle's arg_defs.
    fn add_arg_def_slot<'tcx>(&mut self, args: &Vec<Operand<'tcx>>, bb: u32) {
        let mut arg_defs = Vec::with_capacity(args.len());
        for _ in 0..args.len() {
            arg_defs.push(FxHashSet::default());
        }
        self.arg_defs.insert(bb, arg_defs);
    }
}

impl Summary {
    /// Get the target Callee by DefId from the vector of Callee used by a fn.
    ///
    /// This may not be that slow as it looks because a function usually only has
    /// a limited number of callees. We did not use a HashSet for Summary.callees
    /// because HashSet does not support get_mut(). We also did not use
    /// HashMap<DefId, Callee> because serializing it will generate illegal JSON
    /// ("key must be a string").
    fn get_callee_local(&mut self, def_id: DefId) -> Option<&mut Callee> {
        for callee in self.callees.iter_mut() {
            if break_def_id(def_id) == callee.def_id {
                return Some(callee);
            }
        }

        None
    }

    /// Update Callee.arg_defs by adding a new DefSite.
    ///
    /// Inputs:
    /// @call: The (BasicBlock, DefId) of the target callee.
    /// @index: Index of the argument in Callee.arg_defs.
    /// @site: A new DefSite
    fn update_arg_defs(&mut self, call: (u32, DefId),
                       index: usize, site: DefSite) {
        let callee = self.get_callee_local(call.1).unwrap();
        // The next unwrap is safe as analyze_fn() processes each call.
        let callee_arg_defs = callee.arg_defs.get_mut(&call.0).unwrap();
        callee_arg_defs[index].insert(site);
    }

}

/// Get the Local of the Place of the return value of a function call, if it
/// does not return an empty tuple or divert.
fn get_non_empty_ret<'tcx>(ret: Place<'tcx>, body: &Body<'tcx>) -> Option<Local> {
    if is_empty_ty(body.local_decls[ret.local].ty) {
        return None;
    } else {
        return Some(ret.local);
    }
}

/// Core procedure of finding definition sites of each argument of a fn call.
/// It first examines a basic block backwards, and then recursively examines
/// the BB's predecessors. It is similar to unsafe_def::find_unsafe_def_core.
///
/// Inputs:
/// @bb: Currently processed BasicBlock.
/// @body: Body of the processed function.
/// @call: (BasicBlock, DefId) of the currently processed call of a callee.
/// @locals: Local (Place) that contributes to the arguments of the call.
/// @visited: Already processed BB.
/// @summary: Summary of the target function.
fn find_arg_def<'tcx>(bb: BasicBlock, body: &Body<'tcx>,
                      call: (u32, DefId),
                      locals: &mut Vec<FxHashSet<Local>>,
                      visited: &mut FxHashSet<BasicBlock>,
                      summary: &mut Summary) {
    if !visited.insert(bb) || locals.is_empty() { return; }

    let bbd = &body.basic_blocks()[bb];
    let bb_index = bb.as_u32();
    // Process Terminator
    if let TerminatorKind::Call{func: Operand::Constant(f), args, destination,
        ..} = &bbd.terminator().kind {
        if let Some(call_ret) = get_non_empty_ret(*destination, body) {
            // Found a potential definition site from a function call.
            for i in 0..locals.len() {
                let arg_locals = &mut locals[i];
                if arg_locals.contains(&call_ret) {
                    arg_locals.remove(&call_ret);
                    let def_site = def_site_from_call(f, bb_index);
                    match def_site {
                        DefSite::HeapAlloc(_) => {
                            summary.update_arg_defs(call, i, def_site);
                        },
                        DefSite::NativeCall(_) => {
                            get_local_in_args(args, arg_locals);
                        },
                        DefSite::OtherCall(_) => {
                            get_local_in_args(args, arg_locals);
                            summary.update_arg_defs(call, i, def_site);
                        },
                        _ => {}
                    }
                }
            }
        }
    }

    // Process each Statement backward.
    for i in (0..bbd.statements.len()).rev() {
        let stmt = &bbd.statements[i];
        match &stmt.kind {
            StatementKind::Assign(box (place, rvalue)) => {
                for arg_locals in locals.iter_mut() {
                    let local = place.local;
                    if arg_locals.contains(&local) {
                        arg_locals.remove(&local);
                        get_local_in_rvalue(rvalue, arg_locals);
                    }
                }
            },
            _ => {
                // Any other cases to handle?
            }
        }
    }

    // Recursively examine the current BB's predecessors.
    let predecessors = &body.predecessors()[bb];
    for pbb in predecessors {
        if predecessors.len() > 1 {
            find_arg_def(*pbb, body, call, &mut locals.clone(),
                         visited, summary);
        } else {
            find_arg_def(*pbb, body, call, locals, visited, summary);
        }
    }

    // After examine the first BB, check if any function arguments
    // contribute to the definition/declaration of function call arguments.
    if bb.index() == 0 {
        for i in 0..locals.len() {
            let arg_locals = &mut locals[i];
            for arg in body.args_iter() {
                if arg_locals.contains(&arg) {
                    arg_locals.remove(&arg);
                    summary.update_arg_defs(call, i, DefSite::Arg(arg.as_u32()));
                }
            }
        }
    }
}

/// Core procedure of finding the def sites for the return value of a fn.
///
/// Inputs:
/// @loc: Location of the Statement/Terminator from which to iterate backward.
/// @locals: Local of Place that contribute to the target return value.
/// @body: Body of the target function.
/// @visited: Processed BasicBlock.
/// @summary: Summary.
///
/// TODO: We assume that there is no MIR code like _5 = foo(_5, ..), i.e.,
/// the return of a call is assigned to a Place that is also used as one of the
/// arguments. We should add assert for this. We would otherwise run the risk
/// of missing the def sites for such Place.
fn find_ret_def<'tcx>(loc: &Location, locals: &mut FxHashSet<Local>,
                      body: &Body<'tcx>, visited: &mut FxHashSet<BasicBlock>,
                      summary: &mut Summary) {
    let bb = loc.block;
    if visited.contains(&bb) || locals.is_empty() { return; }
    visited.insert(bb);

    let mut start_index = loc.statement_index;
    let bbd = &body.basic_blocks()[bb];
    let stmt_num = bbd.statements.len();
    if start_index == stmt_num {
        // Examine the BB starting from the Terminator.
        if let TerminatorKind::Call{func: Operand::Constant(f), args,
            destination, ..} = &bbd.terminator().kind {
            if let Some(local) = get_non_empty_ret(*destination, body) {
                if locals.contains(&local) {
                    locals.remove(&local);
                    let def_site = def_site_from_call(f, bb.as_u32());
                    match def_site {
                        DefSite::HeapAlloc(_) => {
                            summary.ret_defs.0.insert(def_site);
                        },
                        DefSite::NativeCall(_) => {
                            get_local_in_args(args, locals);
                            // Should def_site be put to summary.ret_defs?
                        },
                        DefSite::OtherCall(_) => {
                            get_local_in_args(args, locals);
                            summary.ret_defs.0.insert(def_site);
                        }
                        _ => {}
                    }
                }
            }
        }
    } else {
        // This means we need to examine starting from a Statement.
        start_index += 1;
    }

    // Examine each Statement backward
    for i in (0..start_index).rev() {
        match &bbd.statements[i].kind {
            StatementKind::Assign(box (place, rvalue)) => {
                let local = place.local;
                if local.as_u32() == 0 || locals.contains(&local) {
                    locals.remove(&local);
                    get_local_in_rvalue(rvalue, locals);
                }
            },
            _ => {}
        }
    }

    // Examine bb's predecessors recursively.
    let predecessors = &body.predecessors()[bb];
    for pbb in predecessors {
        let loc = Location { block: *pbb,
            statement_index: body.basic_blocks()[*pbb].statements.len()};
        if predecessors.len() > 1 {
            find_ret_def(&loc, &mut locals.clone(), body, visited, summary);
        } else {
            find_ret_def(&loc, locals, body, visited, summary);
        }
    }

    // Check if any argument contributes to the return value.
    if bb.index() == 0 && !locals.is_empty() {
        body.args_iter().for_each(|arg|
            if locals.contains(&arg) {
                summary.ret_defs.1.push(DefSite::Arg(arg.as_u32()));
            });
    }
}

/// Resolve a callee as precisely as possible.
///
/// When calling a trait fn, the def_id returned from callee.literal.ty.kind()
/// is always the fn declaration or default impl in the trait. Here we try to
/// resolve the concrete callee as precisely as possible. Sometimes it is
/// impossible to get the exact callee when the call is through a trait object.
/// For such cases, we need to conservatively assume all the implementors of
/// the trait are possible. Therefore, this resolve_callee returns a set of
/// functions instead of only one.
///
/// However, it is possible that not all the resolved candidate callees survive.
/// For example, in crate futures_task-0.3.21, trait fn UnsafeFutureObj::into_raw
/// is implemented 10 times, and our resolving procedure finds all the 10 impl.
/// However, summarize::summarize() only sees 4 of them. We need to record such
/// dyn calls so that when later the WPA fails to find the Summary of a callee,
/// it would know the cause could be this.
/// Jie Zhou: It is not clear to me why some impl disappear. A guess: the
/// compiler may decide that such impl are dead code.
///
/// Note that there are unhandled cases of InstanceDef. It is fine now leaving
/// them unhandled as none of the test program triggered the panic.
fn resolve_callee<'tcx>(tcx: TyCtxt<'tcx>, callee: &Constant<'tcx>)
    -> FxHashSet<DefId> {
    let mut resolved_ids = FxHashSet::<DefId>::default();
    if let ty::FnDef(callee_id, substs) = *callee.literal.ty().kind() {
        if tcx.trait_of_item(callee_id).is_none() {
            // Not a trait fn.
            resolved_ids.insert(callee_id);
            return resolved_ids;
        }

        // Resolving a trait function.
        if let Some(instance) = ty::Instance::resolve(
            tcx, ty::ParamEnv::reveal_all(), callee_id, substs).unwrap() {
            let instance_id = instance.def_id();
            if  instance_id == callee_id {
                // Should be one of the two cases:
                // 1. Directly call a default trait fn, e.g., Trait::foo(..).
                // 2. Call via a dyn trait, which may be (somehow) resolved to
                // the default impl of the trait fn. For example:
                //   trait Trait { fn foo() {...} }
                //   impl Trait for S { fn foo() {...} }
                //   fn bar(o: &dyn Trait) { o.foo(); }
                //   bar(&s); // s is an S.
                //
                // The call `o.foo()` is somehow resolved to Trait::foo(), for
                // which I think "unresolvable" is more reasonable. Luckily,
                // we can check if the InstanceDef is Virtual to distinguish
                // it from a direct call to the default trait fn impl.
                match instance.def {
                    InstanceDef::Item(_) => {
                        // Should be from calling a default trait fn.
                        resolved_ids.insert(callee_id);
                        return resolved_ids;
                    },
                    InstanceDef::Virtual(..) => {
                        // Dynamic dispatch (dyn Trait). Handle this case below.
                    },
                    InstanceDef::VtableShim(_) |
                    InstanceDef::ReifyShim(_) |
                    InstanceDef::FnPtrShim(..) => {
                        // Is it correct to handle those the same as Virtual?
                    },
                    InstanceDef::CloneShim(..) => {
                        // Compiler-generated <T as Clone>::clone(). Do we need
                        // to resolve all the implementors of it?
                        resolved_ids.insert(callee_id);
                        return resolved_ids;
                    },
                    InstanceDef::Intrinsic(_) |
                    InstanceDef::ClosureOnceShim{..} |
                    InstanceDef::DropGlue(..) => {
                        // TODO: Do we need to handle them specicially?
                        panic!("Unhanndled InstanceDef");
                    }
                }
            } else {
                // Successfully resolved the exact trait fn.
                resolved_ids.insert(instance_id);
                return resolved_ids;
            }
        }

        // Processing an unresolved case or resolved call by dyn trait.
        let trait_id = tcx.trait_of_item(callee_id).expect("DefId of Trait");
        let mut impl_ids = Vec::<DefId>::new();
        let impls = tcx.trait_impls_of(trait_id);
        // Collect all the impl of this trait.
        for impl_id in impls.blanket_impls() {
            impl_ids.push(*impl_id);
        }
        for impl_id_v in impls.non_blanket_impls().values() {
            for impl_id in impl_id_v {
                impl_ids.push(*impl_id);
            }
        }

        // Find all implemented functions for callee_id.
        for impl_id in impl_ids {
            let impl_decl_map = tcx.impl_item_implementor_ids(impl_id);
            if impl_decl_map.contains_key(&callee_id) {
                resolved_ids.insert(*impl_decl_map.get(&callee_id).unwrap());
            } else {
                // This should be when the call is via a trait object but the
                // type that impl the trait does not really impl the fn, e.g.,
                //
                //   trait Trait {
                //       fn foo() {...}
                //       ... // Other fn.
                //   }
                //   impl<T: Trait> Trait for S<T> {
                //       fn bar(t: T) { t.foo(); // Will call the Trait::foo().}
                //       // S does not impl foo().
                //   }
                //
                // The call to foo() in bar() cannot be resolved as there may be
                // multiple types that impl Trait.
                resolved_ids.insert(callee_id);
            }
        }

        return resolved_ids;
    }

    panic!("Not a function");
}

/// Analyze a function to find:
/// 1. Its callees and the definition sites of the arguments of each callee.
/// 2. The definition sites for its return value, if there is one.
pub(super)
fn analyze_fn<'tcx>(tcx: TyCtxt<'tcx>, body: &Body<'tcx>, summary: &mut Summary) {
    // BB that end with a call.
    let mut bb_with_calls = Vec::new();
    // Location of return value's def stmt and Local that contribute to it.
    let mut ret_defs = FxHashMap::<Location, FxHashSet::<Local>>::default();
    // Cache of a BB and the DefId of its resolved callee(s).
    let mut callee_def_ids = FxHashMap::<u32, Vec<DefId>>::default();
    // Prepare data:
    // 1. BB with a call.
    // 2. BB with return value definition.
    for (bb, bbd) in body.basic_blocks().iter_enumerated() {
        let terminator = &bbd.terminator();
        let bb_index = bb.as_u32();
        if let TerminatorKind::Call{func: Operand::Constant(callee), args,
            destination, ..} = &terminator.kind {
            bb_with_calls.push(bb);
            // Prepare arg_defs of Callee.
            let resolved_callees = resolve_callee(tcx, callee);

            // Record callees that cannot be resolved statically. See the
            // comment of resolve_callee() for why we need this.
            if resolved_callees.len() > 1 {
                for callee_id in &resolved_callees {
                    summary.dyn_callees.insert(get_fn_fingerprint(tcx, *callee_id));
                }
            }

            for callee_id in resolved_callees {
                if !callee_def_ids.contains_key(&bb_index) {
                    callee_def_ids.insert(bb_index, Vec::new());
                }
                callee_def_ids.get_mut(&bb_index).unwrap().push(callee_id);
                let callee_fn_id = get_fn_fingerprint(tcx, callee_id);

                if tcx.is_foreign_item(callee_id) {
                    // The Callee is a foreign item. The later WPA will ignore
                    // foreign functions. Another implementation option is to
                    // not add such a Callee to Summary. However, we add it
                    // anyway for the completeness of the call graph.
                    summary.foreign_callees.insert(callee_fn_id);
                }

                if let Some(callee) = summary.get_callee_local(callee_id) {
                    // Has seen a call to this callee before.
                    callee.add_arg_def_slot(args, bb_index);
                } else {
                    let mut callee = Callee {
                        fn_id: callee_fn_id,
                        fn_name: get_fn_name(callee_id),
                        crate_name: get_crate_name(callee_id),
                        def_id: break_def_id(callee_id),
                        arg_defs: FxHashMap::default()
                    };
                    callee.add_arg_def_slot(args, bb_index);
                    summary.callees.push(callee);
                }
            }

            // Prepare for return value.
            if !is_empty_ty(body.return_ty()) && destination.local.index() == 0 {
                let loc = Location {
                    block: bb, statement_index: bbd.statements.len()
                };
                let mut locals = FxHashSet::<Local>::default();
                get_local_in_args(args, &mut locals);
                ret_defs.insert(loc, locals);
            }
            continue;
        }

        // Continue to prepare for return value.
        for i in 0..bbd.statements.len() {
            match &bbd.statements[i].kind {
                StatementKind::Assign(box (place, rvalue)) => {
                    if place.local.as_u32() == 0 {
                        // Found a def site for the return.
                        let loc = Location { block: bb, statement_index: i };
                        let mut locals = FxHashSet::<Local>::default();
                        get_local_in_rvalue(rvalue, &mut locals);
                        ret_defs.insert(loc, locals);
                        // There should be at most one ret def ("_0 = ...")
                        // in a BB so it should be safe to break from here.
                        break;
                    }
                },
                _ => {}
            }
        }
    }

    // Process each function call to find the def sites of its arguments.
    for bb in bb_with_calls {
        if let TerminatorKind::Call{func: _, args, ..} =
            &body.basic_blocks()[bb].terminator().kind {
            // Recorded visited BB to prevent infite recursions due to loops.
            let mut visited = FxHashSet::<BasicBlock>::default();
            // Local of the Place that contribute to function call arguments.
            let mut locals = Vec::<FxHashSet::<Local>>::with_capacity(args.len());
            // Collect the initial Local for each argument.
            for arg in args {
                let mut places = Vec::new();
                let mut arg_locals = FxHashSet::default();
                get_place_in_operand(arg, &mut places);
                for place in places { arg_locals.insert(place.local); }
                locals.push(arg_locals);
            }
            // Enter the core procedure of finding def sites for fn args.
            for callee_id in callee_def_ids.get(&bb.as_u32()).unwrap() {
                find_arg_def(bb, body, (bb.as_u32(), *callee_id), &mut locals,
                    &mut visited, summary);
            }
        } else {
            panic!("Not a function");
        }
    }

    // Process the return value to find its def sites.
    for (loc, mut locals) in ret_defs {
        let mut visited = FxHashSet::<BasicBlock>::default();
        find_ret_def(&loc, &mut locals, body, &mut visited, summary);
    }
}
