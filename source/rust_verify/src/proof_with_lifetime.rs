//! Lifetime checking for proof_with / declare_with.
//!
//! These functions erase tracked/ghost parameters from fn signatures before the borrow
//! checker runs, so Rust's NLL cannot enforce lifetime constraints on those parameters.
//! This module performs a first-pass lifetime check during VIR lowering to catch
//! incompatible lifetimes early.
//!
//! Strategy: use rustc's `InferCtxt` to do a subtype check between the actual arg type
//! (with real caller regions) and the expected type (with caller regions derived from
//! exec arg matching). This reuses Rust's region constraint solver rather than
//! reimplementing outlives checking.

use crate::context::BodyCtxt;
use crate::util::err_span;
use rustc_hir::def::Res;
use rustc_hir::{ExprKind, QPath};
use rustc_middle::ty::error::TypeErrorToStringExt;
use rustc_span::Span;
use rustc_span::def_id::DefId;
use rustc_trait_selection::regions::InferCtxtRegionExt;
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
    callee_def_id: DefId,
    call_hir_id: rustc_hir::HirId,
    arg_hir_id: rustc_hir::HirId,
    expected_ty_raw: rustc_middle::ty::Ty<'tcx>,
    call_span: Span,
    arg_index: usize,
) -> Result<(), VirErr> {
    use rustc_infer::infer::TyCtxtInferExt;
    use rustc_middle::ty::{Region, RegionKind, TypeFoldable, TypeVisitable, TypeVisitor};
    use std::ops::ControlFlow;

    let tcx = bctx.ctxt.tcx;

    // --- Helpers ---

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

    /// Get DefId for a named region in a given function's scope.
    fn region_def_id<'tcx>(
        tcx: rustc_middle::ty::TyCtxt<'tcx>,
        owner_def_id: DefId,
        region: Region<'tcx>,
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
            RegionKind::ReBound(_, br) => {
                if let rustc_middle::ty::BoundRegionKind::Named(def_id) = br.kind {
                    Some(def_id)
                } else {
                    None
                }
            }
            _ => None,
        }
    }

    // --- Step 1: Check if expected type has any regions worth checking ---

    let raw_regions = collect_regions(expected_ty_raw);
    let callee_region_def_ids: Vec<_> =
        raw_regions.iter().filter_map(|r| region_def_id(tcx, callee_def_id, *r)).collect();

    if callee_region_def_ids.is_empty() {
        return Ok(()); // No lifetime params in the ghost type
    }

    // --- Step 2: Get the actual arg type with real regions ---

    let caller_def_id = bctx.fun_id;
    let caller_poly_sig = tcx.fn_sig(caller_def_id).instantiate_identity();
    let caller_liberated = tcx.liberate_late_bound_regions(caller_def_id, caller_poly_sig);
    let caller_inputs = caller_liberated.inputs();

    let param_idx = resolve_expr_to_param_index(tcx, caller_def_id, arg_hir_id);
    let actual_ty_with_regions = match param_idx {
        Some(idx) if idx < caller_inputs.len() => caller_inputs[idx],
        _ => return Ok(()), // Can't determine actual type with regions
    };

    // --- Step 3: Build callee→caller region mapping from exec args ---

    let callee_poly_sig = tcx.fn_sig(callee_def_id).instantiate_identity();
    let callee_sig_inputs = callee_poly_sig.skip_binder().inputs();

    // Extract call arg HirIds from the HIR
    let call_arg_hir_ids: Vec<rustc_hir::HirId> = {
        let hir_node = tcx.hir_node(call_hir_id);
        match hir_node {
            rustc_hir::Node::Expr(expr) => match &expr.kind {
                ExprKind::Call(_, hir_args) => hir_args.iter().map(|a| a.hir_id).collect(),
                ExprKind::MethodCall(_, receiver, hir_args, _) => {
                    let mut ids = vec![receiver.hir_id];
                    ids.extend(hir_args.iter().map(|a| a.hir_id));
                    ids
                }
                _ => return Ok(()),
            },
            _ => return Ok(()),
        }
    };

    // Map callee region DefId → caller Region by matching callee fn_sig params with call args
    let mut callee_to_caller: std::collections::HashMap<rustc_span::def_id::DefId, Region<'tcx>> =
        std::collections::HashMap::new();

    for (param_idx, callee_param_ty) in callee_sig_inputs.iter().enumerate() {
        let param_regions: Vec<_> = collect_regions(*callee_param_ty)
            .into_iter()
            .filter_map(|r| {
                let did = region_def_id(tcx, callee_def_id, r)?;
                Some(did)
            })
            .collect();

        if param_regions.is_empty() || param_idx >= call_arg_hir_ids.len() {
            continue;
        }

        let arg_hir = call_arg_hir_ids[param_idx];
        if let Some(caller_param_idx) = resolve_expr_to_param_index(tcx, caller_def_id, arg_hir) {
            if caller_param_idx < caller_inputs.len() {
                let caller_param_ty = caller_inputs[caller_param_idx];
                let caller_regions: Vec<_> = collect_regions(caller_param_ty)
                    .into_iter()
                    .filter(|r| {
                        matches!(r.kind(), RegionKind::ReLateParam(_) | RegionKind::ReEarlyParam(_))
                    })
                    .collect();

                for (callee_did, caller_region) in param_regions.iter().zip(caller_regions.iter()) {
                    callee_to_caller.insert(*callee_did, *caller_region);
                }
            }
        }
    }

    // --- Step 4: Build expected type with caller regions using InferCtxt ---

    let infcx = tcx.infer_ctxt().build(rustc_type_ir::TypingMode::PostAnalysis);

    // For ghost-only regions not found in exec args, create fresh region variables
    for callee_did in &callee_region_def_ids {
        if !callee_to_caller.contains_key(callee_did) {
            let fresh =
                infcx.next_region_var(rustc_infer::infer::RegionVariableOrigin::Misc(call_span));
            callee_to_caller.insert(*callee_did, fresh);
        }
    }

    // Fold expected_ty_raw, replacing callee regions with mapped caller regions
    let expected_ty_caller =
        expected_ty_raw.fold_with(&mut rustc_middle::ty::RegionFolder::new(tcx, &mut |r, _| {
            if let Some(callee_did) = region_def_id(tcx, callee_def_id, r) {
                if let Some(caller_region) = callee_to_caller.get(&callee_did) {
                    return *caller_region;
                }
            }
            r
        }));

    // --- Step 5: Add callee's where-clause region bounds as constraints ---

    let callee_predicates = tcx.predicates_of(callee_def_id);
    for (pred, _) in callee_predicates.predicates {
        if let Some(rustc_middle::ty::ClauseKind::RegionOutlives(outlives)) =
            pred.kind().no_bound_vars()
        {
            let longer_did = region_def_id(tcx, callee_def_id, outlives.0);
            let shorter_did = region_def_id(tcx, callee_def_id, outlives.1);

            if let (Some(longer_did), Some(shorter_did)) = (longer_did, shorter_did) {
                if let (Some(&caller_longer), Some(&caller_shorter)) =
                    (callee_to_caller.get(&longer_did), callee_to_caller.get(&shorter_did))
                {
                    // Add constraint: caller_longer: caller_shorter
                    // (sub_regions(a, b) means a <= b, i.e., b outlives a)
                    infcx.sub_regions(
                        rustc_infer::infer::SubregionOrigin::RelateParamBound(
                            call_span,
                            actual_ty_with_regions,
                            None,
                        ),
                        caller_shorter,
                        caller_longer,
                    );
                }
            }
        }
    }

    // --- Step 6: Subtype check: actual_ty <: expected_ty ---

    let param_env = tcx.param_env(caller_def_id);
    let cause = rustc_infer::traits::ObligationCause::dummy();

    if let Err(error) = infcx.at(&cause, param_env).sub(
        rustc_infer::infer::DefineOpaqueTypes::Yes,
        actual_ty_with_regions,
        expected_ty_caller,
    ) {
        return err_span(
            call_span,
            format!(
                "proof_with argument {} has incompatible lifetime: {}",
                arg_index + 1,
                error.to_string(tcx)
            ),
        );
    }

    // --- Step 7: Resolve region constraints and check for errors ---

    let assumed_wf: Vec<rustc_middle::ty::Ty<'tcx>> = vec![];
    let errors = infcx.resolve_regions(caller_def_id.expect_local(), param_env, assumed_wf);

    if !errors.is_empty() {
        return err_span(
            call_span,
            format!(
                "proof_with argument {} has incompatible lifetime: {:?}",
                arg_index + 1,
                errors
            ),
        );
    }

    Ok(())
}

/// Try to resolve an expression (by HirId) to a function parameter index.
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
