use vir::messages::AstId;

use rustc_hir::HirId;
use rustc_span::SpanData;

use vir::ast::{Datatype, Dt, Fun, Function, Krate, Mode, Path, Pattern};
use vir::modes::ErasureModes;

use crate::verus_items::{DummyCaptureItem, VerusItem, VerusItems};
use rustc_hir::def_id::LocalDefId;
use rustc_mir_build_verus::verus::{
    BodyErasure, CallErasure, LoopErasure, LoopSpecEvaluationLocation, NodeErase, TreeErase,
    VarErasure, VerusErasureCtxt, set_verus_aware_def_ids, set_verus_erasure_ctxt,
};
use rustc_span::Span;
use std::collections::HashMap;
use std::collections::HashSet;
use std::sync::Arc;
use vir::ast::VirErr;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum CompilableOperator {
    IntIntrinsic,
    Implies,
    RcNew,
    ArcNew,
    BoxNew,
    SmartPtrClone { is_method: bool },
    GhostExec,
    TrackedNew,
    TrackedExec,
    TrackedExecBorrow,
    TrackedGet,
    TrackedBorrow,
    TrackedBorrowMut,
    UseTypeInvariant,
    ClosureToFnProof(Mode),
    GhostBorrowMut,
    MutRefTracked,
    ShrRefStructWrap,
}

/// Information about each call in the AST (each ExprKind::Call).
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ResolvedCall {
    /// The call is to a spec or proof function, and should be erased
    SpecPure,
    /// The call is to a spec or proof function, but may have proof-mode arguments
    SpecAllowProofArgs,
    /// The call is to an operator like == or + that should be compiled.
    CompilableOperator(CompilableOperator),
    /// The call is to a function, and we record the name of the function here
    /// (both unresolved and resolved), as well as (in_ghost, assume_external) flags.
    /// This is replaced by CallModes as soon as the modes are available.
    Call(Fun, Fun, bool, bool),
    /// Path and variant of datatype constructor
    Ctor(Path, vir::ast::Ident),
    /// Path and variant of datatype constructor. Used for ExprKind::Struct nodes.
    BracesCtor(Path, vir::ast::Ident, Arc<Vec<vir::ast::Ident>>, bool),
    /// The call is to a dynamically computed function, and is exec
    NonStaticExec,
    /// The call is to a dynamically computed function, and is proof
    NonStaticProof(Arc<Vec<Mode>>),
    /// Erase the node and all subtrees completely. Suitable for ad hoc directives
    /// like `constraint_type`.
    MiscEraseAbsolutely,
    /// InferSpecForLoopIter. May need to be erased depending on mode-checking results
    InferSpecForLoopIter(AstId),
    /// Loop spec (invariant, decreases, etc.). HirId is the HirId of the loop body.
    LoopSpec(HirId, LoopSpecKind),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LoopSpecKind {
    Invariant,
    Decreases,
    Ensures,
    InvariantExceptBreak,
}

impl LoopSpecKind {
    /// For the given loop spec kind, at which program points is that expression "evaluated"?
    ///
    /// This is needed for the analysis to correctly determine whether the given expressions
    /// are prophetic, since propheticness depends on the locations of the expressions relative
    /// to borrows.
    ///
    /// For Invariant, our answer is an overapproximation, as the specifics of where
    /// an 'invariant' is evaluated depend on fiddly variables like loop_isolation level
    /// and whether the loop has a 'break' statement. However, the distinction only ever matters
    /// for rare cases when the condition has side-effects, so it doesn't matter very much.
    ///
    /// For soundness purposes, the only one that really matters is the 'Decreases' case
    /// (since it's the only clause which is restricted to be non-prophetic).
    /// For the other cases, they only matter for the sake of matching the documented behavior
    /// of requiring prophetic uses to be marked with 'after_borrow'.
    fn loop_spec_evaluation_location(&self) -> LoopSpecEvaluationLocation {
        match self {
            LoopSpecKind::Invariant => LoopSpecEvaluationLocation::BodyStartAndPostLoop,
            LoopSpecKind::Decreases => LoopSpecEvaluationLocation::BodyStart,
            LoopSpecKind::Ensures => LoopSpecEvaluationLocation::PostLoop,
            LoopSpecKind::InvariantExceptBreak => LoopSpecEvaluationLocation::BodyStart,
        }
    }
}

#[derive(Clone)]
pub struct ErasureHints {
    /// Copy of the entire VIR crate that was created in the first run's HIR -> VIR transformation
    pub vir_crate: Krate,
    /// Connect expression and pattern HirId to corresponding vir AstId
    pub hir_vir_ids: Vec<(HirId, AstId)>,
    /// Details of each call in the first run's HIR
    pub resolved_calls: Vec<(HirId, SpanData, ResolvedCall)>,
    /// Details of some patterns in first run's HIR
    pub resolved_pats: Vec<(SpanData, Pattern)>,
    /// Results of mode (spec/proof/exec) inference from first run's VIR
    pub erasure_modes: ErasureModes,
    /// Modes specified directly during rust_to_vir
    pub direct_var_modes: Vec<(HirId, Mode)>,
    /// List of #[verifier(external)] functions.  (These don't appear in vir_crate,
    /// so we need to record them separately here.)
    pub external_functions: Vec<Fun>,
    /// List of function spans ignored by the verifier. These should not be erased
    pub ignored_functions: Vec<(rustc_span::def_id::DefId, SpanData)>,
    pub(crate) bodies: Vec<(LocalDefId, BodyErasure)>,
    pub(crate) shadow_check: Vec<HirId>,
    pub(crate) extra_erase_ast_ids: Vec<vir::messages::Span>,
    pub(crate) extra_erase_hir_ids_including_adjustments: Vec<HirId>,
}

/// How to erase the given var usage
///  - var_mode: mode of the variable (as declared at its binding)
///  - mode: mode of this particular usage
///  - shadow_check: could this possibly need a shadow check?
///
/// Generally speaking, if the mode is spec, it should be erased.
/// However, spec uses of a non-spec variable may still need a shadow var.
/// (If the variable itself is spec, we don't generate any shadow var for it at all.)
///
/// The shadow_check is used to exclude cases like vars used in `old` (always non-prophetic)
/// or `after_borrow` (always prophetic, and thus its propheticness is accounted for by modes.rs).
fn mode_to_var_erase(var_mode: Mode, mode: Mode, shadow_check: bool) -> VarErasure {
    match mode {
        Mode::Spec => {
            if shadow_check && var_mode != Mode::Spec {
                VarErasure::Shadow
            } else {
                VarErasure::Erase
            }
        }
        Mode::Exec | Mode::Proof => VarErasure::Keep,
    }
}

/// Translate ResolvedCall (generated by the rust_verify HIR traversal) to CallErasure,
/// which is what the rustc_mir_build_verus fork expects.
/// REVIEW: it might simpler to skip the ResolvedCall call entirely and have the original
/// traversal generate CallErasure values.
fn resolved_call_to_call_erase(
    _span: Span,
    functions: &HashMap<Fun, Function>,
    _datatypes: &HashMap<Path, Datatype>,
    resolved_call: &ResolvedCall,
    ctor_mode: Option<Mode>,
    infer_spec_for_loop_iter_erase: &HashMap<AstId, bool>,
) -> Result<CallErasure, VirErr> {
    Ok(match resolved_call {
        ResolvedCall::SpecPure => CallErasure::EraseTree(TreeErase::IncludeBasicChecks),
        ResolvedCall::SpecAllowProofArgs => CallErasure::Call(NodeErase::Erase),
        ResolvedCall::Call(ufun, rfun, in_ghost, assume_external) => {
            // Note: in principle, the unresolved function ufun should always be present,
            // but we currently allow external declarations of resolved trait functions
            // without a corresponding external trait declaration.
            let Some(f) = functions.get(ufun).or_else(|| functions.get(rfun)) else {
                if *assume_external {
                    let erase = CallErasure::Call(NodeErase::Keep);
                    return Ok(erase);
                }
                dbg!(ufun, rfun);
                panic!("internal Verus error: could not find mode declarations for function")
            };
            if *in_ghost && f.x.mode == Mode::Exec {
                // This must be an autospec, so change exec -> spec
                CallErasure::Call(NodeErase::Erase)
            } else if f.x.mode == Mode::Spec {
                CallErasure::Call(NodeErase::Erase)
            } else {
                CallErasure::Call(NodeErase::Keep)
            }
        }
        ResolvedCall::Ctor(..) | ResolvedCall::BracesCtor(..) => match ctor_mode {
            Some(Mode::Spec) => CallErasure::Call(NodeErase::Erase),
            Some(_) | None => CallErasure::Call(NodeErase::Keep),
        },
        ResolvedCall::NonStaticExec => CallErasure::keep_all(),
        ResolvedCall::NonStaticProof(_modes) => CallErasure::Call(NodeErase::Keep),
        ResolvedCall::CompilableOperator(co) => match co {
            CompilableOperator::IntIntrinsic => CallErasure::Call(NodeErase::Erase),

            CompilableOperator::GhostExec => CallErasure::Call(NodeErase::Keep),

            CompilableOperator::Implies
            | CompilableOperator::RcNew
            | CompilableOperator::ArcNew
            | CompilableOperator::BoxNew
            | CompilableOperator::SmartPtrClone { .. }
            | CompilableOperator::TrackedNew
            | CompilableOperator::TrackedExec => CallErasure::keep_all(),

            CompilableOperator::ClosureToFnProof(_)
            | CompilableOperator::TrackedExecBorrow
            | CompilableOperator::TrackedGet
            | CompilableOperator::TrackedBorrow
            | CompilableOperator::TrackedBorrowMut
            | CompilableOperator::GhostBorrowMut
            | CompilableOperator::MutRefTracked
            | CompilableOperator::ShrRefStructWrap
            | CompilableOperator::UseTypeInvariant => CallErasure::keep_all(),
        },
        ResolvedCall::MiscEraseAbsolutely => CallErasure::EraseTree(TreeErase::EraseAbsolutely),
        // LoopSpecs get special handling, so they are marked EraseAbsolutely to avoid
        // double-handling.
        ResolvedCall::LoopSpec(..) => CallErasure::EraseTree(TreeErase::EraseAbsolutely),
        ResolvedCall::InferSpecForLoopIter(ast_id) => {
            if infer_spec_for_loop_iter_erase[ast_id] {
                CallErasure::EraseTree(TreeErase::EraseAbsolutely)
            } else {
                CallErasure::Call(NodeErase::Erase)
            }
        }
    })
}

fn get_binder_hir_id<'tcx>(
    tcx: rustc_middle::ty::TyCtxt<'tcx>,
    hir_id: HirId,
) -> Option<(Span, rustc_span::Ident, HirId)> {
    let rustc_hir::Node::Expr(expr) = tcx.hir_node(hir_id) else {
        return None;
    };
    let rustc_hir::ExprKind::Path(qpath) = &expr.kind else {
        return None;
    };
    let rustc_hir::QPath::Resolved(_, path) = &qpath else {
        return None;
    };
    let rustc_hir::def::Res::Local(id) = path.res else {
        return None;
    };
    Some((path.span, path.segments[0].ident, id))
}

pub(crate) fn setup_verus_ctxt_for_thir_erasure<'tcx>(
    tcx: rustc_middle::ty::TyCtxt<'tcx>,
    verus_items: &VerusItems,
    erasure_hints: &ErasureHints,
) -> Result<(), VirErr> {
    let mut id_to_hir: HashMap<AstId, Vec<HirId>> = HashMap::new();
    for (hir_id, vir_id) in &erasure_hints.hir_vir_ids {
        if !id_to_hir.contains_key(vir_id) {
            id_to_hir.insert(*vir_id, vec![]);
        }
        id_to_hir.get_mut(vir_id).unwrap().push(*hir_id);
    }

    let mut vars = HashMap::<HirId, VarErasure>::new();
    for (span, (var_mode, mode)) in erasure_hints.erasure_modes.var_modes.iter() {
        if crate::spans::from_raw_span(&span.raw_span).is_none() {
            continue;
        }
        if !id_to_hir.contains_key(&span.id) {
            dbg!(span);
            dbg!(mode);
            return Err(vir::messages::error(
                span,
                "Verus Internal Error: setup_verus_ctxt_for_thir_erasure failed, var lookup failed",
            ));
        }
        for hir_id in &id_to_hir[&span.id] {
            vars.insert(
                *hir_id,
                mode_to_var_erase(*var_mode, *mode, erasure_hints.shadow_check.contains(hir_id)),
            );
        }
    }
    for span in erasure_hints.extra_erase_ast_ids.iter() {
        if crate::spans::from_raw_span(&span.raw_span).is_none() {
            continue;
        }
        if !id_to_hir.contains_key(&span.id) {
            continue;
        }
        for hir_id in &id_to_hir[&span.id] {
            vars.insert(*hir_id, VarErasure::Erase);
        }
    }

    for (hir_id, mode) in vars.iter() {
        if let Some((span, name, binder_hir_id)) = get_binder_hir_id(tcx, *hir_id) {
            if let Some(binder_mode) = vars.get(&binder_hir_id) {
                if matches!(binder_mode, VarErasure::Erase) && !matches!(mode, VarErasure::Erase) {
                    return crate::util::err_span(
                        span,
                        format!(
                            "Verus Internal Error: inconsistent erasure modes: var `{:}` is {mode:?} but the binder is Erase",
                            name.as_str()
                        ),
                    );
                }
            }
        }
    }

    let mut ctor_modes = HashMap::<HirId, Mode>::new();
    for (span, mode) in erasure_hints.erasure_modes.ctor_modes.iter() {
        if crate::spans::from_raw_span(&span.raw_span).is_none() {
            continue;
        }
        if !id_to_hir.contains_key(&span.id) {
            dbg!(span);
            dbg!(mode);
            return Err(vir::messages::error(
                span,
                "Verus Internal Error: setup_verus_ctxt_for_thir_erasure failed, ctor lookup failed",
            ));
        }
        for hir_id in &id_to_hir[&span.id] {
            ctor_modes.insert(*hir_id, *mode);
        }
    }

    let mut functions = HashMap::<Fun, Function>::new();
    for f in &erasure_hints.vir_crate.functions {
        functions.insert(f.x.name.clone(), f.clone()).map(|_| panic!("{:?}", &f.x.name));
    }

    let mut datatypes = HashMap::<Path, Datatype>::new();
    for d in &erasure_hints.vir_crate.datatypes {
        if let Dt::Path(path) = &d.x.name {
            datatypes.insert(path.clone(), d.clone()).map(|_| panic!("{:?}", &path));
        }
    }

    let mut infer_spec_for_loop_iter_erase = HashMap::<AstId, bool>::new();
    for (span, erase) in erasure_hints.erasure_modes.infer_spec_for_loop_iter_erase.iter() {
        let found = infer_spec_for_loop_iter_erase.insert(span.id, *erase);
        assert!(found.is_none());
    }

    let mut calls = HashMap::<HirId, CallErasure>::new();
    let mut loop_erasure = HashMap::<HirId, LoopErasure>::new();
    for (hir_id, span_data, resolved_call) in &erasure_hints.resolved_calls {
        let span = span_data.span();
        let ctor_mode = ctor_modes.get(hir_id).cloned();
        let _found = calls.insert(
            *hir_id,
            resolved_call_to_call_erase(
                span,
                &functions,
                &datatypes,
                resolved_call,
                ctor_mode,
                &infer_spec_for_loop_iter_erase,
            )?,
        );
        // REVIEW: we should check that that there aren't conflicting entries, but right now,
        // there are some redundant traversals
        //assert!(found.is_none());

        if let ResolvedCall::LoopSpec(loop_hir_id, loop_spec_kind) = resolved_call {
            let l =
                loop_erasure.entry(*loop_hir_id).or_insert_with(|| LoopErasure { specs: vec![] });
            l.specs.push((*hir_id, loop_spec_kind.loop_spec_evaluation_location()));
        }
    }

    let mut bodies = HashMap::<LocalDefId, BodyErasure>::new();
    for (hir_id, c) in &erasure_hints.bodies {
        bodies.insert(*hir_id, *c);
    }

    let mut adjusted_node_erasure = HashSet::new();
    for hir_id in erasure_hints.extra_erase_hir_ids_including_adjustments.iter() {
        adjusted_node_erasure.insert(*hir_id);
    }

    let verus_erasure_ctxt = VerusErasureCtxt {
        vars,
        calls,
        bodies,
        adjusted_node_erasure,
        loop_erasure,

        erased_ghost_value_fn_def_id: *verus_items
            .name_to_id
            .get(&VerusItem::ErasedGhostValue)
            .unwrap(),
        shadow_ghost_value_fn_def_id: *verus_items
            .name_to_id
            .get(&VerusItem::ShadowGhostValue)
            .unwrap(),
        dummy_capture_struct_def_id: *verus_items
            .name_to_id
            .get(&VerusItem::DummyCapture(DummyCaptureItem::Struct))
            .unwrap(),
        mutable_reference_tie_fn_def_id: *verus_items
            .name_to_id
            .get(&VerusItem::MutableReferenceTie)
            .unwrap(),
        two_phase_mutable_reference_tie_fn_def_id: *verus_items
            .name_to_id
            .get(&VerusItem::TwoPhaseMutableReferenceTie)
            .unwrap(),
        get_first_fn_def_id: *verus_items.name_to_id.get(&VerusItem::GetFirst).unwrap(),
    };
    set_verus_erasure_ctxt(Arc::new(verus_erasure_ctxt));

    Ok(())
}

/// Set all IDs in this tree to VarErasure::Erase. Useful if a VIR node gets dropped
/// before it reaches mode-checking.
pub(crate) fn mark_tree_for_erasure<'tcx>(
    context: &crate::context::Context<'tcx>,
    expr: &vir::ast::Expr,
) {
    vir::ast_visitor::ast_visitor_check::<(), _, _, _, _, _, _>(
        expr,
        &mut (),
        &mut |_, _scope_map, expr: &vir::ast::Expr| {
            context.erasure_info.borrow_mut().extra_erase_ast_ids.push(expr.span.clone());
            Ok(())
        },
        &mut |_, _scope_map, stmt| {
            context.erasure_info.borrow_mut().extra_erase_ast_ids.push(stmt.span.clone());
            Ok(())
        },
        &mut |_, _scope_map, pattern: &vir::ast::Pattern| {
            context.erasure_info.borrow_mut().extra_erase_ast_ids.push(pattern.span.clone());
            Ok(())
        },
        &mut |_, _scope_map, _typ, _span| Ok(()),
        &mut |_, _scope_map, place| {
            context.erasure_info.borrow_mut().extra_erase_ast_ids.push(place.span.clone());
            Ok(())
        },
    )
    .unwrap();
}

pub(crate) fn mark_adjusted_node_for_erasure<'tcx>(
    context: &crate::context::Context<'tcx>,
    expr: &rustc_hir::Expr<'tcx>,
) {
    context.erasure_info.borrow_mut().extra_erase_hir_ids_including_adjustments.push(expr.hir_id);
}

pub(crate) fn setup_verus_aware_ids(crate_items: &crate::external::CrateItems) {
    // Requirements:
    //  - If a function requires Verus-erasure, then it MUST be in the set
    //  - If a function has special properties (e.g., being const), that may cause Rust
    //    to run mir_borrowck on it before Verus mode-checking, then it MUST NOT be in the set.
    // For anything else: it doesn't matter.
    //
    // Since most consts are marked external, we can just use the VerusAware set for this.
    // We carve out exceptions for some special directives.

    let mut s = HashSet::<LocalDefId>::new();
    for item in crate_items.items.iter() {
        match item.verif {
            crate::external::VerifOrExternal::VerusAware {
                const_directive,
                external_body,
                external_fn_specification,
                ..
            } => {
                if !const_directive && !external_body && !external_fn_specification {
                    s.insert(item.id.owner_id().def_id);
                }
            }
            crate::external::VerifOrExternal::External { .. } => {}
        }
    }
    set_verus_aware_def_ids(Arc::new(s));
}
