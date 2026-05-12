//! Lifetime checking for proof_with / declare_with.
//!
//! These functions erase tracked/ghost parameters from fn signatures before the borrow
//! checker runs, so Rust's NLL cannot enforce lifetime constraints on those parameters.
//! This module performs a first-pass lifetime check during VIR lowering to catch
//! incompatible lifetimes early.

use crate::context::BodyCtxt;
use crate::util::err_span;
use rustc_hir::def::Res;
use rustc_hir::{ExprKind, QPath};
use rustc_span::Span;
use rustc_span::def_id::DefId;
use vir::ast::VirErr;

/// Check that a proof_with argument's lifetime is compatible with the callee's expected lifetime.
///
/// The expected type (from `lower_ty` on the callee's `declare_with` HIR type) has
/// `ReLateParam(callee, 'a)` regions. We need to:
/// 1. Map callee's late-bound `'a` to the caller's corresponding lifetime via the call args
/// 2. Get the proof_with arg's lifetime from its declaration
/// 3. Check that the arg's lifetime outlives the expected lifetime in the caller's scope
pub(crate) fn check_proof_with_lifetime<'tcx>(
    bctx: &BodyCtxt<'tcx>,
    tcx: rustc_middle::ty::TyCtxt<'tcx>,
    callee_def_id: DefId,
    call_hir_id: rustc_hir::HirId,
    _node_substs: &'tcx rustc_middle::ty::List<rustc_middle::ty::GenericArg<'tcx>>,
    arg_hir_id: rustc_hir::HirId,
    _expected_ty_raw: rustc_middle::ty::Ty<'tcx>,
    expected_ty_instantiated: rustc_middle::ty::Ty<'tcx>,
    call_span: Span,
    arg_index: usize,
) -> Result<(), VirErr> {
    use rustc_middle::ty::{Region, RegionKind, TypeVisitable, TypeVisitor};
    use std::ops::ControlFlow;

    struct RegionCollector<'tcx> {
        regions: Vec<Region<'tcx>>,
    }
    impl<'tcx> TypeVisitor<rustc_middle::ty::TyCtxt<'tcx>> for RegionCollector<'tcx> {
        type Result = ControlFlow<()>;
        fn visit_region(&mut self, r: Region<'tcx>) -> Self::Result {
            self.regions.push(r);
            ControlFlow::Continue(())
        }
    }

    fn collect_regions<'tcx>(ty: rustc_middle::ty::Ty<'tcx>) -> Vec<Region<'tcx>> {
        let mut collector = RegionCollector { regions: vec![] };
        let _ = ty.visit_with(&mut collector);
        collector.regions
    }

    // Extract named regions from the expected type (could be ReLateParam or ReEarlyParam)
    let expected_regions = collect_regions(expected_ty_instantiated);

    // Get DefId for a named region
    fn region_def_id<'tcx>(
        tcx: rustc_middle::ty::TyCtxt<'tcx>,
        owner_def_id: DefId,
        region: &rustc_middle::ty::Region<'tcx>,
    ) -> Option<rustc_span::def_id::DefId> {
        match region.kind() {
            RegionKind::ReLateParam(lp) => match lp.kind {
                rustc_middle::ty::LateParamRegionKind::Named(def_id) => Some(def_id),
                _ => None,
            },
            RegionKind::ReEarlyParam(ep) => {
                let generics = tcx.generics_of(owner_def_id);
                let param = generics.param_at(ep.index as usize, tcx);
                Some(param.def_id)
            }
            _ => None,
        }
    }

    let named_regions: Vec<_> = expected_regions
        .iter()
        .filter(|r| region_def_id(tcx, callee_def_id, r).is_some())
        .collect();

    if named_regions.is_empty() {
        return Ok(()); // No named lifetimes to check
    }

    // Get the callee's poly fn_sig to find which params use each late-bound region
    let callee_poly_sig = tcx.fn_sig(callee_def_id).instantiate_identity();
    let callee_sig_inputs = callee_poly_sig.skip_binder().inputs();

    // Get the caller's liberated fn_sig to find real lifetime regions for caller params
    let caller_def_id = bctx.fun_id;
    let caller_poly_sig = tcx.fn_sig(caller_def_id).instantiate_identity();
    let caller_liberated = tcx.liberate_late_bound_regions(caller_def_id, caller_poly_sig);
    let caller_inputs = caller_liberated.inputs();

    // Build mapping: callee late-bound region DefId → caller ReLateParam region
    // by matching callee fn_sig params with call args
    let mut callee_to_caller_region: std::collections::HashMap<
        rustc_span::def_id::DefId,
        rustc_middle::ty::Region<'tcx>,
    > = std::collections::HashMap::new();

    // Extract call arg HirIds from the HIR expression
    let call_arg_hir_ids: Vec<rustc_hir::HirId> = {
        let hir_node = tcx.hir_node(call_hir_id);
        match hir_node {
            rustc_hir::Node::Expr(expr) => match &expr.kind {
                ExprKind::Call(_, hir_args) => hir_args.iter().map(|a| a.hir_id).collect(),
                rustc_hir::ExprKind::MethodCall(_, receiver, hir_args, _) => {
                    let mut ids = vec![receiver.hir_id];
                    ids.extend(hir_args.iter().map(|a| a.hir_id));
                    ids
                }
                _ => return Ok(()), // Can't extract args
            },
            _ => return Ok(()),
        }
    };

    // For each callee fn_sig param, find bound regions and match with call arg
    for (param_idx, callee_param_ty) in callee_sig_inputs.iter().enumerate() {
        // Find named regions (ReBound or ReEarlyParam) in this callee param
        let named_param_regions: Vec<_> = collect_regions(*callee_param_ty)
            .into_iter()
            .filter_map(|r| match r.kind() {
                RegionKind::ReBound(rustc_middle::ty::BoundVarIndexKind::Bound(debruijn), br)
                    if debruijn == rustc_middle::ty::INNERMOST =>
                {
                    if let rustc_middle::ty::BoundRegionKind::Named(def_id) = br.kind {
                        Some(def_id)
                    } else {
                        None
                    }
                }
                RegionKind::ReEarlyParam(ep) => {
                    let generics = tcx.generics_of(callee_def_id);
                    Some(generics.param_at(ep.index as usize, tcx).def_id)
                }
                _ => None,
            })
            .collect();

        if named_param_regions.is_empty() || param_idx >= call_arg_hir_ids.len() {
            continue;
        }

        // Try to resolve the call arg to a caller parameter to get its real lifetime
        let arg_hir_id_for_param = call_arg_hir_ids[param_idx];
        if let Some(caller_param_idx) =
            resolve_expr_to_param_index(tcx, caller_def_id, arg_hir_id_for_param)
        {
            if caller_param_idx < caller_inputs.len() {
                let caller_param_ty = caller_inputs[caller_param_idx];
                let caller_regions = collect_regions(caller_param_ty);
                let caller_named_regions: Vec<_> = caller_regions
                    .into_iter()
                    .filter(|r| {
                        matches!(r.kind(), RegionKind::ReLateParam(_) | RegionKind::ReEarlyParam(_))
                    })
                    .collect();

                // Map each bound region to the corresponding caller region
                // (simple 1:1 mapping by position within the type)
                for (region_def_id, caller_region) in
                    named_param_regions.iter().zip(caller_named_regions.iter())
                {
                    callee_to_caller_region.insert(*region_def_id, *caller_region);
                }
            }
        }
    }

    if callee_to_caller_region.is_empty() {
        // Couldn't determine the mapping — skip the check
        return Ok(());
    }

    // Get the proof_with arg's type with real regions
    let actual_arg_region =
        get_arg_late_param_region(tcx, caller_def_id, caller_inputs, arg_hir_id);

    // For each named region in the expected type, check compatibility
    for expected_region in &named_regions {
        let callee_lt_def_id = match region_def_id(tcx, callee_def_id, expected_region) {
            Some(did) => did,
            None => continue,
        };

        let Some(expected_caller_region) = callee_to_caller_region.get(&callee_lt_def_id) else {
            continue; // Can't check this region
        };

        let Some(actual_region) = actual_arg_region else {
            continue; // Can't determine actual region
        };

        // Compare: does actual_region outlive expected_caller_region?
        let actual_did = region_def_id(tcx, caller_def_id, &actual_region);
        let expected_did = region_def_id(tcx, caller_def_id, expected_caller_region);

        if let (Some(actual_did), Some(expected_did)) = (actual_did, expected_did) {
            if actual_did == expected_did {
                continue; // Same lifetime — OK
            }

            // Check if actual outlives expected in the caller's where-clause bounds
            if check_region_outlives(tcx, caller_def_id, actual_region, *expected_caller_region) {
                continue; // Outlives relationship declared — OK
            }

            // Lifetime mismatch!
            let actual_name = tcx.item_name(actual_did);
            let expected_name = tcx.item_name(expected_did);
            return err_span(
                call_span,
                format!(
                    "proof_with argument {} has incompatible lifetime: \
                     expected lifetime `'{}`, got `'{}`\n\
                     help: consider adding `'{}: '{}`",
                    arg_index + 1,
                    expected_name,
                    actual_name,
                    actual_name,
                    expected_name,
                ),
            );
        }
    }

    Ok(())
}

/// Try to resolve an expression (by HirId) to a function parameter index.
/// Returns Some(index) if the expression is a simple reference to a function parameter.
fn resolve_expr_to_param_index<'tcx>(
    tcx: rustc_middle::ty::TyCtxt<'tcx>,
    fn_def_id: DefId,
    arg_hir_id: rustc_hir::HirId,
) -> Option<usize> {
    let hir_node = tcx.hir_node(arg_hir_id);
    let expr = match hir_node {
        rustc_hir::Node::Expr(e) => e,
        _ => return None,
    };
    if let ExprKind::Path(QPath::Resolved(None, path)) = &expr.kind {
        if let Res::Local(local_hir_id) = path.res {
            let local_def_id = fn_def_id.as_local()?;
            let body = tcx.hir_body_owned_by(local_def_id);
            for (i, param) in body.params.iter().enumerate() {
                if param.pat.hir_id == local_hir_id {
                    return Some(i);
                }
            }
        }
    }
    None
}

/// Get the first named region (ReLateParam or ReEarlyParam) from a proof_with arg's type.
/// The arg is typically a function parameter of the caller.
fn get_arg_late_param_region<'tcx>(
    tcx: rustc_middle::ty::TyCtxt<'tcx>,
    caller_def_id: DefId,
    caller_inputs: &[rustc_middle::ty::Ty<'tcx>],
    arg_hir_id: rustc_hir::HirId,
) -> Option<rustc_middle::ty::Region<'tcx>> {
    use rustc_middle::ty::RegionKind;

    if let Some(param_idx) = resolve_expr_to_param_index(tcx, caller_def_id, arg_hir_id) {
        if param_idx < caller_inputs.len() {
            let param_ty = caller_inputs[param_idx];
            let regions: Vec<_> = {
                use rustc_middle::ty::{Region, TypeVisitable, TypeVisitor};
                use std::ops::ControlFlow;
                struct Collector<'tcx> {
                    regions: Vec<Region<'tcx>>,
                }
                impl<'tcx> TypeVisitor<rustc_middle::ty::TyCtxt<'tcx>> for Collector<'tcx> {
                    type Result = ControlFlow<()>;
                    fn visit_region(&mut self, r: Region<'tcx>) -> Self::Result {
                        if matches!(
                            r.kind(),
                            RegionKind::ReLateParam(_) | RegionKind::ReEarlyParam(_)
                        ) {
                            self.regions.push(r);
                        }
                        ControlFlow::Continue(())
                    }
                }
                let mut c = Collector { regions: vec![] };
                let _ = param_ty.visit_with(&mut c);
                c.regions
            };
            return regions.into_iter().next();
        }
    }

    None
}

/// Check if region `a` outlives region `b` based on the caller's where-clause bounds.
/// Compares by DefId since regions may be in different representations (ReLateParam vs ReEarlyParam).
fn check_region_outlives<'tcx>(
    tcx: rustc_middle::ty::TyCtxt<'tcx>,
    caller_def_id: DefId,
    actual: rustc_middle::ty::Region<'tcx>,
    expected: rustc_middle::ty::Region<'tcx>,
) -> bool {
    use rustc_middle::ty::{ClauseKind, RegionKind};

    fn local_region_def_id<'tcx>(
        tcx: rustc_middle::ty::TyCtxt<'tcx>,
        owner_def_id: DefId,
        r: rustc_middle::ty::Region<'tcx>,
    ) -> Option<rustc_span::def_id::DefId> {
        match r.kind() {
            RegionKind::ReLateParam(lp) => match lp.kind {
                rustc_middle::ty::LateParamRegionKind::Named(def_id) => Some(def_id),
                _ => None,
            },
            RegionKind::ReEarlyParam(ep) => {
                let generics = tcx.generics_of(owner_def_id);
                Some(generics.param_at(ep.index as usize, tcx).def_id)
            }
            _ => None,
        }
    }

    let actual_did = local_region_def_id(tcx, caller_def_id, actual);
    let expected_did = local_region_def_id(tcx, caller_def_id, expected);

    if actual_did.is_none() || expected_did.is_none() {
        return false;
    }

    // Check the caller's predicates for 'actual: 'expected (by DefId)
    let predicates = tcx.predicates_of(caller_def_id);
    for (pred, _) in predicates.predicates {
        if let Some(ClauseKind::RegionOutlives(outlives)) = pred.kind().no_bound_vars() {
            let pred_longer = local_region_def_id(tcx, caller_def_id, outlives.0);
            let pred_shorter = local_region_def_id(tcx, caller_def_id, outlives.1);
            if pred_longer == actual_did && pred_shorter == expected_did {
                return true;
            }
        }
    }

    // 'static outlives anything
    if actual.is_static() {
        return true;
    }

    false
}
