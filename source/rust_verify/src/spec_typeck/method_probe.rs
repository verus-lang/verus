use rustc_data_structures::fx::FxHashSet;
use rustc_errors::Applicability;
use rustc_hir as hir;
use rustc_hir::def::DefKind;
use rustc_hir::HirId;
use rustc_infer::infer::canonical::OriginalQueryValues;
use rustc_infer::infer::canonical::{Canonical, QueryResponse};
use rustc_infer::infer::DefineOpaqueTypes;
use rustc_infer::infer::{self, InferOk};
use rustc_middle::middle::stability;
use rustc_middle::ty::fast_reject::{simplify_type, TreatParams};
use rustc_middle::ty::AssocItem;
use rustc_middle::ty::GenericParamDefKind;
use rustc_middle::ty::ToPredicate;
use rustc_middle::ty::{self, ParamEnvAnd, Ty, TyCtxt, TypeVisitableExt};
use rustc_middle::ty::{GenericArgs, GenericArgsRef};
use rustc_session::lint;
use rustc_span::def_id::DefId;
use rustc_span::def_id::LocalDefId;
use rustc_span::edit_distance::{
    edit_distance_with_substrings, find_best_match_for_name_with_substrings,
};
use rustc_span::symbol::sym;
use rustc_span::{symbol::Ident, Span, Symbol, DUMMY_SP};
use rustc_trait_selection::traits::query::evaluate_obligation::InferCtxtExt;
use rustc_trait_selection::traits::query::method_autoderef::{
    CandidateStep, MethodAutoderefStepsResult,
};
use rustc_trait_selection::traits::ObligationCtxt;
use rustc_trait_selection::traits::{self, ObligationCause};
use std::cell::RefCell;
use std::cmp::max;
use std::iter;
use rustc_infer::infer::InferResult;
use rustc_infer::traits::ObligationCauseCode;
use rustc_hir::def::Namespace;
use rustc_hir::def::CtorOf;

use smallvec::{smallvec, SmallVec};

use rustc_infer::infer::InferCtxt;
use rustc_middle::ty::ParamEnv;

use self::CandidateKind::*;
pub use self::PickKind::*;

pub(crate) fn lookup_method<'tcx>(
    tcx: TyCtxt<'tcx>,
    self_ty: Ty<'tcx>,
    segment: &'tcx hir::PathSegment<'tcx>,
    span: Span,
    call_expr: &'tcx hir::Expr<'tcx>,
    param_env: ParamEnv<'tcx>,
    body_local_def_id: LocalDefId,
    infcx: InferCtxt<'tcx>,
) -> Result<DefId, vir::ast::VirErr> {
    let oc = OuterContext {
        tcx: tcx,
        infcx,
        param_env: param_env,
        body_id: body_local_def_id,
    };
    let e = oc.lookup_method(self_ty, segment, span, call_expr);
    match e {
        Ok(o) => Ok(o),
        Err(e) => {
            println!("{:#?}", self_ty);
            println!("{:#?}", e);
            return crate::util::err_span(
                span,
                "[Verus] lookup_method",
            );
        }
    }
}

pub(crate) fn resolve_fully_qualified_call<'tcx>(
    tcx: TyCtxt<'tcx>,
    span: Span,
    method_name: Ident,
    self_ty: Ty<'tcx>,
    self_ty_span: Span,
    expr_id: hir::HirId,
    param_env: ParamEnv<'tcx>,
    body_local_def_id: LocalDefId,
    infcx: InferCtxt<'tcx>,
) -> Result<(DefKind, DefId), vir::ast::VirErr> {
    let oc = OuterContext {
        tcx: tcx,
        infcx: infcx, 
        param_env: param_env,
        body_id: body_local_def_id,
    };
    let e = oc.resolve_fully_qualified_call(span, method_name, self_ty, self_ty_span, expr_id);
    match e {
        Ok(o) => Ok(o),
        Err(e) => {
            println!("{:#?}", e);
            return crate::util::err_span(
                span,
                "[Verus] resolve_fully_qualified_call",
            );
        }
    }
}

/// Boolean flag used to indicate if this search is for a suggestion
/// or not. If true, we can allow ambiguity and so forth.
#[derive(Clone, Copy, Debug)]
pub struct IsSuggestion(pub bool);

pub(crate) struct OuterContext<'tcx> {
    tcx: TyCtxt<'tcx>,
    infcx: InferCtxt<'tcx>,
    param_env: ParamEnv<'tcx>,
    body_id: LocalDefId,
}

pub(crate) struct ProbeContext<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    outer_ctx: &'a OuterContext<'tcx>,

    span: Span,
    mode: Mode,
    method_name: Option<Ident>,
    return_type: Option<Ty<'tcx>>,

    /// This is the OriginalQueryValues for the steps queries
    /// that are answered in steps.
    orig_steps_var_values: &'a OriginalQueryValues<'tcx>,
    steps: &'tcx [CandidateStep<'tcx>],

    inherent_candidates: Vec<Candidate<'tcx>>,
    extension_candidates: Vec<Candidate<'tcx>>,
    impl_dups: FxHashSet<DefId>,

    /// When probing for names, include names that are close to the
    /// requested name (by edit distance)
    allow_similar_names: bool,

    /// Some(candidate) if there is a private candidate
    private_candidate: Option<(DefKind, DefId)>,

    /// Collects near misses when the candidate functions are missing a `self` keyword and is only
    /// used for error reporting
    static_candidates: RefCell<Vec<CandidateSource>>,

    /// Collects near misses when trait bounds for type parameters are unsatisfied and is only used
    /// for error reporting
    unsatisfied_predicates: RefCell<
        Vec<(ty::Predicate<'tcx>, Option<ty::Predicate<'tcx>>, Option<ObligationCause<'tcx>>)>,
    >,

    scope_expr_id: HirId,

    /// Is this probe being done for a diagnostic? This will skip some error reporting
    /// machinery, since we don't particularly care about, for example, similarly named
    /// candidates if we're *reporting* similarly named candidates.
    is_suggestion: IsSuggestion,
}

#[derive(Debug)]
pub enum CandidateSource {
    Impl(DefId),
    Trait(DefId),
}

#[derive(Debug, Clone)]
pub(crate) struct Candidate<'tcx> {
    pub(crate) item: ty::AssocItem,
    pub(crate) kind: CandidateKind<'tcx>,
    pub(crate) import_ids: SmallVec<[LocalDefId; 1]>,
}

#[derive(Debug, Clone)]
pub(crate) enum CandidateKind<'tcx> {
    InherentImplCandidate(DefId),
    ObjectCandidate(ty::PolyTraitRef<'tcx>),
    TraitCandidate(ty::PolyTraitRef<'tcx>),
    WhereClauseCandidate(ty::PolyTraitRef<'tcx>),
}

#[derive(Debug, PartialEq, Eq, Copy, Clone)]
enum ProbeResult {
    NoMatch,
    BadReturnType,
    Match,
}

/// When adjusting a receiver we often want to do one of
///
/// - Add a `&` (or `&mut`), converting the receiver from `T` to `&T` (or `&mut T`)
/// - If the receiver has type `*mut T`, convert it to `*const T`
///
/// This type tells us which one to do.
///
/// Note that in principle we could do both at the same time. For example, when the receiver has
/// type `T`, we could autoref it to `&T`, then convert to `*const T`. Or, when it has type `*mut
/// T`, we could convert it to `*const T`, then autoref to `&*const T`. However, currently we do
/// (at most) one of these. Either the receiver has type `T` and we convert it to `&T` (or with
/// `mut`), or it has type `*mut T` and we convert it to `*const T`.
#[derive(Debug, PartialEq, Copy, Clone)]
pub enum AutorefOrPtrAdjustment {
    /// Receiver has type `T`, add `&` or `&mut` (it `T` is `mut`), and maybe also "unsize" it.
    /// Unsizing is used to convert a `[T; N]` to `[T]`, which only makes sense when autorefing.
    Autoref {
        mutbl: hir::Mutability,

        /// Indicates that the source expression should be "unsized" to a target type.
        /// This is special-cased for just arrays unsizing to slices.
        unsize: bool,
    },
    /// Receiver has type `*mut T`, convert to `*const T`
    ToConstPtr,
}

impl AutorefOrPtrAdjustment {
    fn get_unsize(&self) -> bool {
        match self {
            AutorefOrPtrAdjustment::Autoref { mutbl: _, unsize } => *unsize,
            AutorefOrPtrAdjustment::ToConstPtr => false,
        }
    }
}

#[derive(Debug, Clone)]
pub struct Pick<'tcx> {
    pub item: ty::AssocItem,
    pub kind: PickKind<'tcx>,
    pub import_ids: SmallVec<[LocalDefId; 1]>,

    /// Indicates that the source expression should be autoderef'd N times
    /// ```ignore (not-rust)
    /// A = expr | *expr | **expr | ...
    /// ```
    pub autoderefs: usize,

    /// Indicates that we want to add an autoref (and maybe also unsize it), or if the receiver is
    /// `*mut T`, convert it to `*const T`.
    pub autoref_or_ptr_adjustment: Option<AutorefOrPtrAdjustment>,
    pub self_ty: Ty<'tcx>,

    /// Unstable candidates alongside the stable ones.
    unstable_candidates: Vec<(Candidate<'tcx>, Symbol)>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum PickKind<'tcx> {
    InherentImplPick,
    ObjectPick,
    TraitPick,
    WhereClausePick(
        // Trait
        ty::PolyTraitRef<'tcx>,
    ),
}

pub type PickResult<'tcx> = Result<Pick<'tcx>, MethodError<'tcx>>;

#[derive(Debug)]
pub enum MethodError<'tcx> {
    NoMatch(NoMatchData<'tcx>),
    Ambiguity(Vec<CandidateSource>),
    PrivateMatch(DefKind, DefId, Vec<DefId>),
    BadReturnType,
}

#[derive(Debug)]
pub struct NoMatchData<'tcx> {
    pub static_candidates: Vec<CandidateSource>,
    pub unsatisfied_predicates: Vec<(ty::Predicate<'tcx>, Option<ty::Predicate<'tcx>>, Option<ObligationCause<'tcx>>)>,
    pub out_of_scope_traits: Vec<DefId>,
    pub similar_candidate: Option<AssocItem>,
    pub mode: Mode,
}


#[derive(PartialEq, Eq, Copy, Clone, Debug)]
pub enum Mode {
    // An expression of the form `receiver.method_name(...)`.
    // Autoderefs are performed on `receiver`, lookup is done based on the
    // `self` argument of the method, and static methods aren't considered.
    MethodCall,
    // An expression of the form `Type::item` or `<T>::item`.
    // No autoderefs are performed, lookup is done based on the type each
    // implementation is for, and static methods are included.
    Path,
}

#[derive(PartialEq, Eq, Copy, Clone, Debug)]
pub enum ProbeScope {
    // Assemble candidates coming only from traits in scope.
    TraitsInScope,

    // Assemble candidates coming from all traits.
    AllTraits,
}

impl<'tcx> OuterContext<'tcx> {
    pub fn lookup_method(
        &self,
        self_ty: Ty<'tcx>,
        segment: &'tcx hir::PathSegment<'tcx>,
        _span: Span,
        call_expr: &'tcx hir::Expr<'tcx>,
        //self_expr: &'tcx hir::Expr<'tcx>,
        //args: &'tcx [hir::Expr<'tcx>],
    ) -> Result<DefId, MethodError<'tcx>> {
        let pick =
            self.lookup_probe(segment.ident, self_ty, call_expr, ProbeScope::TraitsInScope)?;

        //self.lint_dot_call_from_2018(self_ty, segment, span, call_expr, self_expr, &pick, args);

        //for &import_id in &pick.import_ids {
        //    debug!("used_trait_import: {:?}", import_id);
        //    self.typeck_results.borrow_mut().used_trait_imports.insert(import_id);
        //}

        //self.tcx.check_stability(pick.item.def_id, Some(call_expr.hir_id), span, None);

        //Ok(result.callee)

        Ok(pick.item.def_id)
    }

    pub fn resolve_fully_qualified_call(
        &self,
        span: Span,
        method_name: Ident,
        self_ty: Ty<'tcx>,
        _self_ty_span: Span,
        expr_id: hir::HirId,
    ) -> Result<(DefKind, DefId), MethodError<'tcx>> {
        let tcx = self.tcx;

        // Check if we have an enum variant.
        let mut struct_variant = None;
        if let ty::Adt(adt_def, _) = self_ty.kind() {
            if adt_def.is_enum() {
                let variant_def = adt_def
                    .variants()
                    .iter()
                    .find(|vd| tcx.hygienic_eq(method_name, vd.ident(tcx), adt_def.did()));
                if let Some(variant_def) = variant_def {
                    if let Some((ctor_kind, ctor_def_id)) = variant_def.ctor {
                        tcx.check_stability(
                            ctor_def_id,
                            Some(expr_id),
                            span,
                            Some(method_name.span),
                        );
                        return Ok((DefKind::Ctor(CtorOf::Variant, ctor_kind), ctor_def_id));
                    } else {
                        struct_variant = Some((DefKind::Variant, variant_def.def_id));
                    }
                }
            }
        }

        let pick = self.probe_for_name(
            Mode::Path,
            method_name,
            None,
            IsSuggestion(false),
            self_ty,
            expr_id,
            ProbeScope::TraitsInScope,
        );
        let pick = match (pick, struct_variant) {
            // Fall back to a resolution that will produce an error later.
            (Err(_), Some(res)) => return Ok(res),
            (pick, _) => pick?,
        };

        pick.maybe_emit_unstable_name_collision_hint(self.tcx, span, expr_id);

        /*self.lint_fully_qualified_call_from_2018(
            span,
            method_name,
            self_ty,
            self_ty_span,
            expr_id,
            &pick,
        );*/

        //debug!(?pick);
        /*{
            let mut typeck_results = self.typeck_results.borrow_mut();
            for import_id in pick.import_ids {
                //debug!(used_trait_import=?import_id);
                typeck_results.used_trait_imports.insert(import_id);
            }
        }*/

        let def_kind = pick.item.kind.as_def_kind();
        tcx.check_stability(pick.item.def_id, Some(expr_id), span, Some(method_name.span));
        Ok((def_kind, pick.item.def_id))
    }

    pub fn lookup_probe(
        &self,
        method_name: Ident,
        self_ty: Ty<'tcx>,
        call_expr: &hir::Expr<'_>,
        scope: ProbeScope,
    ) -> PickResult<'tcx> {
        let pick = self.probe_for_name(
            Mode::MethodCall,
            method_name,
            None,
            IsSuggestion(false),
            self_ty,
            call_expr.hir_id,
            scope,
        )?;
        pick.maybe_emit_unstable_name_collision_hint(self.tcx, method_name.span, call_expr.hir_id);
        Ok(pick)
    }

    /// This is used to offer suggestions to users. It returns methods
    /// that could have been called which have the desired return
    /// type. Some effort is made to rule out methods that, if called,
    /// would result in an error (basically, the same criteria we
    /// would use to decide if a method is a plausible fit for
    /// ambiguity purposes).
    pub fn probe_for_return_type_for_diagnostic(
        &self,
        span: Span,
        mode: Mode,
        return_type: Ty<'tcx>,
        self_ty: Ty<'tcx>,
        scope_expr_id: HirId,
        candidate_filter: impl Fn(&ty::AssocItem) -> bool,
    ) -> Vec<ty::AssocItem> {
        let method_names = self
            .probe_op(
                span,
                mode,
                None,
                Some(return_type),
                IsSuggestion(true),
                self_ty,
                scope_expr_id,
                ProbeScope::AllTraits,
                |probe_cx| Ok(probe_cx.candidate_method_names(candidate_filter)),
            )
            .unwrap_or_default();
        method_names
            .iter()
            .flat_map(|&method_name| {
                self.probe_op(
                    span,
                    mode,
                    Some(method_name),
                    Some(return_type),
                    IsSuggestion(true),
                    self_ty,
                    scope_expr_id,
                    ProbeScope::AllTraits,
                    |probe_cx| probe_cx.pick(),
                )
                .ok()
                .map(|pick| pick.item)
            })
            .collect()
    }

    pub fn probe_for_name(
        &self,
        mode: Mode,
        item_name: Ident,
        return_type: Option<Ty<'tcx>>,
        is_suggestion: IsSuggestion,
        self_ty: Ty<'tcx>,
        scope_expr_id: HirId,
        scope: ProbeScope,
    ) -> PickResult<'tcx> {
        self.probe_op(
            item_name.span,
            mode,
            Some(item_name),
            return_type,
            is_suggestion,
            self_ty,
            scope_expr_id,
            scope,
            |probe_cx| probe_cx.pick(),
        )
    }

    pub(crate) fn probe_for_name_many(
        &self,
        mode: Mode,
        item_name: Ident,
        return_type: Option<Ty<'tcx>>,
        is_suggestion: IsSuggestion,
        self_ty: Ty<'tcx>,
        scope_expr_id: HirId,
        scope: ProbeScope,
    ) -> Vec<Candidate<'tcx>> {
        self.probe_op(
            item_name.span,
            mode,
            Some(item_name),
            return_type,
            is_suggestion,
            self_ty,
            scope_expr_id,
            scope,
            |probe_cx| {
                Ok(probe_cx
                    .inherent_candidates
                    .into_iter()
                    .chain(probe_cx.extension_candidates)
                    .collect())
            },
        )
        .unwrap()
    }

    pub(crate) fn probe_op<OP, R>(
        &self,
        span: Span,
        mode: Mode,
        method_name: Option<Ident>,
        return_type: Option<Ty<'tcx>>,
        is_suggestion: IsSuggestion,
        self_ty: Ty<'tcx>,
        scope_expr_id: HirId,
        scope: ProbeScope,
        op: OP,
    ) -> Result<R, MethodError<'tcx>>
    where
        OP: FnOnce(ProbeContext<'_, 'tcx>) -> Result<R, MethodError<'tcx>>,
    {
        let mut orig_values = OriginalQueryValues::default();
        let param_env_and_self_ty = self.infcx.canonicalize_query(
            ParamEnvAnd { param_env: self.param_env, value: self_ty },
            &mut orig_values,
        );

        let steps = match mode {
            Mode::MethodCall => //todo!(),
             self.tcx.method_autoderef_steps(param_env_and_self_ty),
            Mode::Path => self.infcx.probe(|_| {
                // Mode::Path - the deref steps is "trivial". This turns
                // our CanonicalQuery into a "trivial" QueryResponse. This
                // is a bit inefficient, but I don't think that writing
                // special handling for this "trivial case" is a good idea.

                let infcx = &self.infcx;
                let (ParamEnvAnd { param_env: _, value: self_ty }, canonical_inference_vars) =
                    infcx.instantiate_canonical(span, &param_env_and_self_ty);
                //debug!(
                //    "probe_op: Mode::Path, param_env_and_self_ty={:?} self_ty={:?}",
                //    param_env_and_self_ty, self_ty
                //);
                MethodAutoderefStepsResult {
                    steps: infcx.tcx.arena.alloc_from_iter([CandidateStep {
                        self_ty: self.infcx.make_query_response_ignoring_pending_obligations(
                            canonical_inference_vars,
                            self_ty,
                        ),
                        autoderefs: 0,
                        from_unsafe_deref: false,
                        unsize: false,
                    }]),
                    opt_bad_ty: None,
                    reached_recursion_limit: false,
                }
            }),
        };

        /*
        // If our autoderef loop had reached the recursion limit,
        // report an overflow error, but continue going on with
        // the truncated autoderef list.
        if steps.reached_recursion_limit {
            self.infcx.probe(|_| {
                let ty = &steps
                    .steps
                    .last()
                    .unwrap_or_else(|| panic!("reached the recursion limit in 0 steps?"))
                    .self_ty;
                let ty = self
                    .probe_instantiate_query_response(span, &orig_values, ty)
                    .unwrap_or_else(|_| panic!("instantiating {:?} failed?", ty));
                autoderef::report_autoderef_recursion_limit_error(self.tcx, span, ty.value);
            });
        }

        // If we encountered an `_` type or an error type during autoderef, this is
        // ambiguous.
        if let Some(bad_ty) = &steps.opt_bad_ty {
            if is_suggestion.0 {
                // Ambiguity was encountered during a suggestion. Just keep going.
                //debug!("ProbeContext: encountered ambiguity in suggestion");
            } else if bad_ty.reached_raw_pointer
                && !self.tcx.features().arbitrary_self_types
                && !self.tcx.sess.at_least_rust_2018()
            {
                // this case used to be allowed by the compiler,
                // so we do a future-compat lint here for the 2015 edition
                // (see https://github.com/rust-lang/rust/issues/46906)
                self.tcx.node_span_lint(
                    lint::builtin::TYVAR_BEHIND_RAW_POINTER,
                    scope_expr_id,
                    span,
                    "type annotations needed",
                    |_| {},
                );
            } else {
                // Ended up encountering a type variable when doing autoderef,
                // but it may not be a type variable after processing obligations
                // in our local `FnCtxt`, so don't call `structurally_resolve_type`.
                let ty = &bad_ty.ty;
                let ty = self
                    .probe_instantiate_query_response(span, &orig_values, ty)
                    .unwrap_or_else(|_| panic!("instantiating {:?} failed?", ty));
                let ty = self.resolve_vars_if_possible(ty.value);
                let guar = match *ty.kind() {
                    ty::Infer(ty::TyVar(_)) => {
                        let raw_ptr_call =
                            bad_ty.reached_raw_pointer && !self.tcx.features().arbitrary_self_types;
                        let mut err = self.err_ctxt().emit_inference_failure_err(
                            self.body_id,
                            span,
                            ty.into(),
                            E0282,
                            !raw_ptr_call,
                        );
                        if raw_ptr_call {
                            err.span_label(span, "cannot call a method on a raw pointer with an unknown pointee type");
                        }
                        err.emit()
                    }
                    ty::Error(guar) => guar,
                    _ => panic!("unexpected bad final type in method autoderef"),
                };
                self.demand_eqtype(span, ty, Ty::new_error(self.tcx, guar));
                return Err(MethodError::NoMatch(NoMatchData {
                    static_candidates: Vec::new(),
                    unsatisfied_predicates: Vec::new(),
                    out_of_scope_traits: Vec::new(),
                    similar_candidate: None,
                    mode,
                }));
            }
        }
        */

        //debug!("ProbeContext: steps for self_ty={:?} are {:?}", self_ty, steps);

        // this creates one big transaction so that all type variables etc
        // that we create during the probe process are removed later
        self.infcx.probe(|_| {
            let mut probe_cx = ProbeContext::new(
                self,
                span,
                mode,
                method_name,
                return_type,
                &orig_values,
                steps.steps,
                scope_expr_id,
                is_suggestion,
            );

            probe_cx.assemble_inherent_candidates();
            match scope {
                ProbeScope::TraitsInScope => {
                    probe_cx.assemble_extension_candidates_for_traits_in_scope()
                }
                ProbeScope::AllTraits => probe_cx.assemble_extension_candidates_for_all_traits(),
            };
            op(probe_cx)
        })
    }

    pub(crate) fn probe_instantiate_query_response(
        &self,
        span: Span,
        original_values: &OriginalQueryValues<'tcx>,
        query_result: &Canonical<'tcx, QueryResponse<'tcx, Ty<'tcx>>>,
    ) -> InferResult<'tcx, Ty<'tcx>> {
        self.infcx.instantiate_query_response_and_region_obligations(
            &traits::ObligationCause::misc(span, self.body_id),
            self.param_env,
            original_values,
            query_result,
        )
    }

    pub fn cause(&self, span: Span, code: ObligationCauseCode<'tcx>) -> ObligationCause<'tcx> {
        ObligationCause::new(span, self.body_id, code)
    }

    pub fn misc(&self, span: Span) -> ObligationCause<'tcx> {
        self.cause(span, ObligationCauseCode::MiscObligation)
    }
}

impl<'a, 'tcx> ProbeContext<'a, 'tcx> {
    fn new(
        outer_ctx: &'a OuterContext<'tcx>,
        span: Span,
        mode: Mode,
        method_name: Option<Ident>,
        return_type: Option<Ty<'tcx>>,
        orig_steps_var_values: &'a OriginalQueryValues<'tcx>,
        steps: &'tcx [CandidateStep<'tcx>],
        scope_expr_id: HirId,
        is_suggestion: IsSuggestion,
    ) -> ProbeContext<'a, 'tcx> {
        ProbeContext {
            tcx: outer_ctx.tcx,
            outer_ctx,
            span,
            mode,
            method_name,
            return_type,
            inherent_candidates: Vec::new(),
            extension_candidates: Vec::new(),
            impl_dups: FxHashSet::default(),
            orig_steps_var_values,
            steps,
            allow_similar_names: false,
            private_candidate: None,
            static_candidates: RefCell::new(Vec::new()),
            unsatisfied_predicates: RefCell::new(Vec::new()),
            scope_expr_id,
            is_suggestion,
        }
    }

    fn reset(&mut self) {
        self.inherent_candidates.clear();
        self.extension_candidates.clear();
        self.impl_dups.clear();
        self.private_candidate = None;
        self.static_candidates.borrow_mut().clear();
        self.unsatisfied_predicates.borrow_mut().clear();
    }

    ///////////////////////////////////////////////////////////////////////////
    // CANDIDATE ASSEMBLY

    fn push_candidate(&mut self, candidate: Candidate<'tcx>, is_inherent: bool) {
        let is_accessible = if let Some(name) = self.method_name {
            let item = candidate.item;
            let hir_id = self.tcx.local_def_id_to_hir_id(self.outer_ctx.body_id);
            let def_scope =
                self.tcx.adjust_ident_and_get_scope(name, item.container_id(self.tcx), hir_id).1;
            item.visibility(self.tcx).is_accessible_from(def_scope, self.tcx)
        } else {
            true
        };
        if is_accessible {
            if is_inherent {
                self.inherent_candidates.push(candidate);
            } else {
                self.extension_candidates.push(candidate);
            }
        } else if self.private_candidate.is_none() {
            self.private_candidate =
                Some((candidate.item.kind.as_def_kind(), candidate.item.def_id));
        }
    }

    fn assemble_inherent_candidates(&mut self) {
        for step in self.steps.iter() {
            self.assemble_probe(&step.self_ty);
        }
    }

    fn assemble_probe(&mut self, self_ty: &Canonical<'tcx, QueryResponse<'tcx, Ty<'tcx>>>) {
        //debug!("assemble_probe: self_ty={:?}", self_ty);
        let raw_self_ty = self_ty.value.value;
        match *raw_self_ty.kind() {
            ty::Dynamic(data, ..) if let Some(p) = data.principal() => {
                // Subtle: we can't use `instantiate_query_response` here: using it will
                // commit to all of the type equalities assumed by inference going through
                // autoderef (see the `method-probe-no-guessing` test).
                //
                // However, in this code, it is OK if we end up with an object type that is
                // "more general" than the object type that we are evaluating. For *every*
                // object type `MY_OBJECT`, a function call that goes through a trait-ref
                // of the form `<MY_OBJECT as SuperTraitOf(MY_OBJECT)>::func` is a valid
                // `ObjectCandidate`, and it should be discoverable "exactly" through one
                // of the iterations in the autoderef loop, so there is no problem with it
                // being discoverable in another one of these iterations.
                //
                // Using `instantiate_canonical` on our
                // `Canonical<QueryResponse<Ty<'tcx>>>` and then *throwing away* the
                // `CanonicalVarValues` will exactly give us such a generalization - it
                // will still match the original object type, but it won't pollute our
                // type variables in any form, so just do that!
                let (QueryResponse { value: generalized_self_ty, .. }, _ignored_var_values) =
                    self.outer_ctx.infcx.instantiate_canonical(self.span, self_ty);

                self.assemble_inherent_candidates_from_object(generalized_self_ty);
                self.assemble_inherent_impl_candidates_for_type(p.def_id());
                if self.tcx.has_attr(p.def_id(), sym::rustc_has_incoherent_inherent_impls) {
                    self.assemble_inherent_candidates_for_incoherent_ty(raw_self_ty);
                }
            }
            ty::Adt(def, _) => {
                let def_id = def.did();
                self.assemble_inherent_impl_candidates_for_type(def_id);
                if self.tcx.has_attr(def_id, sym::rustc_has_incoherent_inherent_impls) {
                    self.assemble_inherent_candidates_for_incoherent_ty(raw_self_ty);
                }
            }
            ty::Foreign(did) => {
                self.assemble_inherent_impl_candidates_for_type(did);
                if self.tcx.has_attr(did, sym::rustc_has_incoherent_inherent_impls) {
                    self.assemble_inherent_candidates_for_incoherent_ty(raw_self_ty);
                }
            }
            ty::Param(p) => {
                self.assemble_inherent_candidates_from_param(p);
            }
            ty::Bool
            | ty::Char
            | ty::Int(_)
            | ty::Uint(_)
            | ty::Float(_)
            | ty::Str
            | ty::Array(..)
            | ty::Slice(_)
            | ty::RawPtr(_, _)
            | ty::Ref(..)
            | ty::Never
            | ty::Tuple(..) => self.assemble_inherent_candidates_for_incoherent_ty(raw_self_ty),
            _ => {}
        }
    }

    fn assemble_inherent_candidates_for_incoherent_ty(&mut self, self_ty: Ty<'tcx>) {
        let Some(simp) = simplify_type(self.tcx, self_ty, TreatParams::AsCandidateKey) else {
            panic!("unexpected incoherent type: {:?}", self_ty)
        };
        for &impl_def_id in self.tcx.incoherent_impls(simp).into_iter().flatten() {
            self.assemble_inherent_impl_probe(impl_def_id);
        }
    }

    fn assemble_inherent_impl_candidates_for_type(&mut self, def_id: DefId) {
        let impl_def_ids = self.tcx.at(self.span).inherent_impls(def_id).into_iter().flatten();
        for &impl_def_id in impl_def_ids {
            self.assemble_inherent_impl_probe(impl_def_id);
        }
    }

    fn assemble_inherent_impl_probe(&mut self, impl_def_id: DefId) {
        if !self.impl_dups.insert(impl_def_id) {
            return; // already visited
        }

        //debug!("assemble_inherent_impl_probe {:?}", impl_def_id);

        for item in self.impl_or_trait_item(impl_def_id) {
            if !self.has_applicable_self(&item) {
                // No receiver declared. Not a candidate.
                self.record_static_candidate(CandidateSource::Impl(impl_def_id));
                continue;
            }
            self.push_candidate(
                Candidate {
                    item,
                    kind: InherentImplCandidate(impl_def_id),
                    import_ids: smallvec![],
                },
                true,
            );
        }
    }

    fn assemble_inherent_candidates_from_object(&mut self, self_ty: Ty<'tcx>) {
        //debug!("assemble_inherent_candidates_from_object(self_ty={:?})", self_ty);

        let principal = match self_ty.kind() {
            ty::Dynamic(ref data, ..) => Some(data),
            _ => None,
        }
        .and_then(|data| data.principal())
        .unwrap_or_else(|| {
            panic!(
                "non-object {:?} in assemble_inherent_candidates_from_object",
                self_ty
            )
        });

        // It is illegal to invoke a method on a trait instance that refers to
        // the `Self` type. An [`ObjectSafetyViolation::SupertraitSelf`] error
        // will be reported by `object_safety.rs` if the method refers to the
        // `Self` type anywhere other than the receiver. Here, we use a
        // instantiation that replaces `Self` with the object type itself. Hence,
        // a `&self` method will wind up with an argument type like `&dyn Trait`.
        let trait_ref = principal.with_self_ty(self.tcx, self_ty);
        self.elaborate_bounds(iter::once(trait_ref), |this, new_trait_ref, item| {
            this.push_candidate(
                Candidate { item, kind: ObjectCandidate(new_trait_ref), import_ids: smallvec![] },
                true,
            );
        });
    }

    fn assemble_inherent_candidates_from_param(&mut self, param_ty: ty::ParamTy) {
        // FIXME: do we want to commit to this behavior for param bounds?
        //debug!("assemble_inherent_candidates_from_param(param_ty={:?})", param_ty);

        let bounds = self.outer_ctx.param_env.caller_bounds().iter().filter_map(|predicate| {
            let bound_predicate = predicate.kind();
            match bound_predicate.skip_binder() {
                ty::ClauseKind::Trait(trait_predicate) => {
                    match *trait_predicate.trait_ref.self_ty().kind() {
                        ty::Param(p) if p == param_ty => {
                            Some(bound_predicate.rebind(trait_predicate.trait_ref))
                        }
                        _ => None,
                    }
                }
                ty::ClauseKind::RegionOutlives(_)
                | ty::ClauseKind::TypeOutlives(_)
                | ty::ClauseKind::Projection(_)
                | ty::ClauseKind::ConstArgHasType(_, _)
                | ty::ClauseKind::WellFormed(_)
                | ty::ClauseKind::ConstEvaluatable(_) => None,
            }
        });

        self.elaborate_bounds(bounds, |this, poly_trait_ref, item| {
            this.push_candidate(
                Candidate {
                    item,
                    kind: WhereClauseCandidate(poly_trait_ref),
                    import_ids: smallvec![],
                },
                true,
            );
        });
    }

    // Do a search through a list of bounds, using a callback to actually
    // create the candidates.
    fn elaborate_bounds<F>(
        &mut self,
        bounds: impl Iterator<Item = ty::PolyTraitRef<'tcx>>,
        mut mk_cand: F,
    ) where
        F: for<'b> FnMut(&mut ProbeContext<'b, 'tcx>, ty::PolyTraitRef<'tcx>, ty::AssocItem),
    {
        let tcx = self.tcx;
        for bound_trait_ref in traits::transitive_bounds(tcx, bounds) {
            //debug!("elaborate_bounds(bound_trait_ref={:?})", bound_trait_ref);
            for item in self.impl_or_trait_item(bound_trait_ref.def_id()) {
                if !self.has_applicable_self(&item) {
                    self.record_static_candidate(CandidateSource::Trait(bound_trait_ref.def_id()));
                } else {
                    mk_cand(self, bound_trait_ref, item);
                }
            }
        }
    }

    fn assemble_extension_candidates_for_traits_in_scope(&mut self) {
        let mut duplicates = FxHashSet::default();
        let opt_applicable_traits = self.tcx.in_scope_traits(self.scope_expr_id);
        if let Some(applicable_traits) = opt_applicable_traits {
            for trait_candidate in applicable_traits.iter() {
                let trait_did = trait_candidate.def_id;
                if duplicates.insert(trait_did) {
                    self.assemble_extension_candidates_for_trait(
                        &trait_candidate.import_ids,
                        trait_did,
                    );
                }
            }
        }
    }

    fn assemble_extension_candidates_for_all_traits(&mut self) {
        let mut duplicates = FxHashSet::default();
        for trait_info in all_traits(self.tcx) {
            if duplicates.insert(trait_info.def_id) {
                self.assemble_extension_candidates_for_trait(&smallvec![], trait_info.def_id);
            }
        }
    }

    fn matches_return_type(&self, method: ty::AssocItem, expected: Ty<'tcx>) -> bool {
        match method.kind {
            ty::AssocKind::Fn => self.outer_ctx.infcx.probe(|_| {
                let args = self.outer_ctx.infcx.fresh_args_for_item(self.span, method.def_id);
                let fty = self.tcx.fn_sig(method.def_id).instantiate(self.tcx, args);
                let fty = self.outer_ctx.infcx.instantiate_binder_with_fresh_vars(self.span, infer::FnCall, fty);
                self.outer_ctx.infcx.can_sub(self.outer_ctx.param_env, fty.output(), expected)
            }),
            _ => false,
        }
    }

    fn assemble_extension_candidates_for_trait(
        &mut self,
        import_ids: &SmallVec<[LocalDefId; 1]>,
        trait_def_id: DefId,
    ) {
        //debug!("assemble_extension_candidates_for_trait(trait_def_id={:?})", trait_def_id);
        let trait_args = self.outer_ctx.infcx.fresh_args_for_item(self.span, trait_def_id);
        let trait_ref = ty::TraitRef::new(self.tcx, trait_def_id, trait_args);

        if self.tcx.is_trait_alias(trait_def_id) {
            // For trait aliases, recursively assume all explicitly named traits are relevant
            for expansion in traits::expand_trait_aliases(
                self.tcx,
                iter::once((ty::Binder::dummy(trait_ref), self.span)),
            ) {
                let bound_trait_ref = expansion.trait_ref();
                for item in self.impl_or_trait_item(bound_trait_ref.def_id()) {
                    if !self.has_applicable_self(&item) {
                        self.record_static_candidate(CandidateSource::Trait(
                            bound_trait_ref.def_id(),
                        ));
                    } else {
                        self.push_candidate(
                            Candidate {
                                item,
                                import_ids: import_ids.clone(),
                                kind: TraitCandidate(bound_trait_ref),
                            },
                            false,
                        );
                    }
                }
            }
        } else {
            debug_assert!(self.tcx.is_trait(trait_def_id));
            if self.tcx.trait_is_auto(trait_def_id) {
                return;
            }
            for item in self.impl_or_trait_item(trait_def_id) {
                // Check whether `trait_def_id` defines a method with suitable name.
                if !self.has_applicable_self(&item) {
                    //debug!("method has inapplicable self");
                    self.record_static_candidate(CandidateSource::Trait(trait_def_id));
                    continue;
                }
                self.push_candidate(
                    Candidate {
                        item,
                        import_ids: import_ids.clone(),
                        kind: TraitCandidate(ty::Binder::dummy(trait_ref)),
                    },
                    false,
                );
            }
        }
    }

    fn candidate_method_names(
        &self,
        candidate_filter: impl Fn(&ty::AssocItem) -> bool,
    ) -> Vec<Ident> {
        let mut set = FxHashSet::default();
        let mut names: Vec<_> = self
            .inherent_candidates
            .iter()
            .chain(&self.extension_candidates)
            .filter(|candidate| candidate_filter(&candidate.item))
            .filter(|candidate| {
                if let Some(return_ty) = self.return_type {
                    self.matches_return_type(candidate.item, return_ty)
                } else {
                    true
                }
            })
            // ensure that we don't suggest unstable methods
            .filter(|candidate| {
                // note that `DUMMY_SP` is ok here because it is only used for
                // suggestions and macro stuff which isn't applicable here.
                !matches!(
                    self.tcx.eval_stability(candidate.item.def_id, None, DUMMY_SP, None),
                    stability::EvalResult::Deny { .. }
                )
            })
            .map(|candidate| candidate.item.ident(self.tcx))
            .filter(|&name| set.insert(name))
            .collect();

        // Sort them by the name so we have a stable result.
        names.sort_by(|a, b| a.as_str().cmp(b.as_str()));
        names
    }

    ///////////////////////////////////////////////////////////////////////////
    // THE ACTUAL SEARCH

    fn pick(mut self) -> PickResult<'tcx> {
        assert!(self.method_name.is_some());

        if let Some(r) = self.pick_core() {
            return r;
        }

        // If it's a `lookup_probe_for_diagnostic`, then quit early. No need to
        // probe for other candidates.
        if self.is_suggestion.0 {
            return Err(MethodError::NoMatch(NoMatchData {
                static_candidates: vec![],
                unsatisfied_predicates: vec![],
                out_of_scope_traits: vec![],
                similar_candidate: None,
                mode: self.mode,
            }));
        }

        //debug!("pick: actual search failed, assemble diagnostics");

        let static_candidates = std::mem::take(self.static_candidates.get_mut());
        let private_candidate = self.private_candidate.take();
        let unsatisfied_predicates = std::mem::take(self.unsatisfied_predicates.get_mut());

        // things failed, so lets look at all traits, for diagnostic purposes now:
        self.reset();

        //let span = self.span;
        let tcx = self.tcx;

        self.assemble_extension_candidates_for_all_traits();

        let out_of_scope_traits = match self.pick_core() {
            Some(Ok(p)) => vec![p.item.container_id(self.tcx)],
            Some(Err(MethodError::Ambiguity(v))) => v
                .into_iter()
                .map(|source| match source {
                    CandidateSource::Trait(id) => id,
                    CandidateSource::Impl(impl_id) => match tcx.trait_id_of_impl(impl_id) {
                        Some(id) => id,
                        None => panic!("found inherent method when looking at traits"),
                    },
                })
                .collect(),
            Some(Err(MethodError::NoMatch(NoMatchData {
                out_of_scope_traits: others, ..
            }))) => {
                assert!(others.is_empty());
                vec![]
            }
            _ => vec![],
        };

        if let Some((kind, def_id)) = private_candidate {
            return Err(MethodError::PrivateMatch(kind, def_id, out_of_scope_traits));
        }
        let similar_candidate = self.probe_for_similar_candidate()?;

        Err(MethodError::NoMatch(NoMatchData {
            static_candidates,
            unsatisfied_predicates,
            out_of_scope_traits,
            similar_candidate,
            mode: self.mode,
        }))
    }

    fn pick_core(&self) -> Option<PickResult<'tcx>> {
        // Pick stable methods only first, and consider unstable candidates if not found.
        self.pick_all_method(Some(&mut vec![])).or_else(|| self.pick_all_method(None))
    }

    fn pick_all_method(
        &self,
        mut unstable_candidates: Option<&mut Vec<(Candidate<'tcx>, Symbol)>>,
    ) -> Option<PickResult<'tcx>> {
        self.steps
            .iter()
            .filter(|step| {
                //debug!("pick_all_method: step={:?}", step);
                // skip types that are from a type error or that would require dereferencing
                // a raw pointer
                !step.self_ty.references_error() && !step.from_unsafe_deref
            })
            .find_map(|step| {
                let InferOk { value: self_ty, obligations: _ } = self
                    .outer_ctx
                    .probe_instantiate_query_response(
                        self.span,
                        self.orig_steps_var_values,
                        &step.self_ty,
                    )
                    .unwrap_or_else(|_| {
                        panic!("{:?} was applicable but now isn't?", step.self_ty)
                    });
                self.pick_by_value_method(step, self_ty, unstable_candidates.as_deref_mut())
                    .or_else(|| {
                        self.pick_autorefd_method(
                            step,
                            self_ty,
                            hir::Mutability::Not,
                            unstable_candidates.as_deref_mut(),
                        )
                        .or_else(|| {
                            self.pick_autorefd_method(
                                step,
                                self_ty,
                                hir::Mutability::Mut,
                                unstable_candidates.as_deref_mut(),
                            )
                        })
                        .or_else(|| {
                            self.pick_const_ptr_method(
                                step,
                                self_ty,
                                unstable_candidates.as_deref_mut(),
                            )
                        })
                    })
            })
    }

    /// For each type `T` in the step list, this attempts to find a method where
    /// the (transformed) self type is exactly `T`. We do however do one
    /// transformation on the adjustment: if we are passing a region pointer in,
    /// we will potentially *reborrow* it to a shorter lifetime. This allows us
    /// to transparently pass `&mut` pointers, in particular, without consuming
    /// them for their entire lifetime.
    fn pick_by_value_method(
        &self,
        step: &CandidateStep<'tcx>,
        self_ty: Ty<'tcx>,
        unstable_candidates: Option<&mut Vec<(Candidate<'tcx>, Symbol)>>,
    ) -> Option<PickResult<'tcx>> {
        if step.unsize {
            return None;
        }

        self.pick_method(self_ty, unstable_candidates).map(|r| {
            r.map(|mut pick| {
                pick.autoderefs = step.autoderefs;

                // Insert a `&*` or `&mut *` if this is a reference type:
                if let ty::Ref(_, _, mutbl) = *step.self_ty.value.value.kind() {
                    pick.autoderefs += 1;
                    pick.autoref_or_ptr_adjustment = Some(AutorefOrPtrAdjustment::Autoref {
                        mutbl,
                        unsize: pick.autoref_or_ptr_adjustment.is_some_and(|a| a.get_unsize()),
                    })
                }

                pick
            })
        })
    }

    fn pick_autorefd_method(
        &self,
        step: &CandidateStep<'tcx>,
        self_ty: Ty<'tcx>,
        mutbl: hir::Mutability,
        unstable_candidates: Option<&mut Vec<(Candidate<'tcx>, Symbol)>>,
    ) -> Option<PickResult<'tcx>> {
        let tcx = self.tcx;

        // In general, during probing we erase regions.
        let region = tcx.lifetimes.re_erased;

        let autoref_ty = Ty::new_ref(tcx, region, self_ty, mutbl);
        self.pick_method(autoref_ty, unstable_candidates).map(|r| {
            r.map(|mut pick| {
                pick.autoderefs = step.autoderefs;
                pick.autoref_or_ptr_adjustment =
                    Some(AutorefOrPtrAdjustment::Autoref { mutbl, unsize: step.unsize });
                pick
            })
        })
    }

    /// If `self_ty` is `*mut T` then this picks `*const T` methods. The reason why we have a
    /// special case for this is because going from `*mut T` to `*const T` with autoderefs and
    /// autorefs would require dereferencing the pointer, which is not safe.
    fn pick_const_ptr_method(
        &self,
        step: &CandidateStep<'tcx>,
        self_ty: Ty<'tcx>,
        unstable_candidates: Option<&mut Vec<(Candidate<'tcx>, Symbol)>>,
    ) -> Option<PickResult<'tcx>> {
        // Don't convert an unsized reference to ptr
        if step.unsize {
            return None;
        }

        let &ty::RawPtr(ty, hir::Mutability::Mut) = self_ty.kind() else {
            return None;
        };

        let const_ptr_ty = Ty::new_imm_ptr(self.tcx, ty);
        self.pick_method(const_ptr_ty, unstable_candidates).map(|r| {
            r.map(|mut pick| {
                pick.autoderefs = step.autoderefs;
                pick.autoref_or_ptr_adjustment = Some(AutorefOrPtrAdjustment::ToConstPtr);
                pick
            })
        })
    }

    fn pick_method(
        &self,
        self_ty: Ty<'tcx>,
        mut unstable_candidates: Option<&mut Vec<(Candidate<'tcx>, Symbol)>>,
    ) -> Option<PickResult<'tcx>> {
        //debug!("pick_method(self_ty={})", self.ty_to_string(self_ty));

        let mut possibly_unsatisfied_predicates = Vec::new();

        for (_kind, candidates) in
            &[("inherent", &self.inherent_candidates), ("extension", &self.extension_candidates)]
        {
            //debug!("searching {} candidates", kind);
            let res = self.consider_candidates(
                self_ty,
                candidates,
                &mut possibly_unsatisfied_predicates,
                unstable_candidates.as_deref_mut(),
            );
            if let Some(pick) = res {
                return Some(pick);
            }
        }

        // `pick_method` may be called twice for the same self_ty if no stable methods
        // match. Only extend once.
        if unstable_candidates.is_some() {
            self.unsatisfied_predicates.borrow_mut().extend(possibly_unsatisfied_predicates);
        }
        None
    }

    fn consider_candidates(
        &self,
        self_ty: Ty<'tcx>,
        candidates: &[Candidate<'tcx>],
        possibly_unsatisfied_predicates: &mut Vec<(
            ty::Predicate<'tcx>,
            Option<ty::Predicate<'tcx>>,
            Option<ObligationCause<'tcx>>,
        )>,
        mut unstable_candidates: Option<&mut Vec<(Candidate<'tcx>, Symbol)>>,
    ) -> Option<PickResult<'tcx>> {
        let mut applicable_candidates: Vec<_> = candidates
            .iter()
            .map(|probe| {
                (probe, self.consider_probe(self_ty, probe, possibly_unsatisfied_predicates))
            })
            .filter(|&(_, status)| status != ProbeResult::NoMatch)
            .collect();

        //debug!("applicable_candidates: {:?}", applicable_candidates);

        if applicable_candidates.len() > 1 {
            if let Some(pick) =
                self.collapse_candidates_to_trait_pick(self_ty, &applicable_candidates)
            {
                return Some(Ok(pick));
            }
        }

        if let Some(uc) = &mut unstable_candidates {
            applicable_candidates.retain(|&(candidate, _)| {
                if let stability::EvalResult::Deny { feature, .. } =
                    self.tcx.eval_stability(candidate.item.def_id, None, self.span, None)
                {
                    uc.push((candidate.clone(), feature));
                    return false;
                }
                true
            });
        }

        if applicable_candidates.len() > 1 {
            let sources = candidates.iter().map(|p| self.candidate_source(p, self_ty)).collect();
            return Some(Err(MethodError::Ambiguity(sources)));
        }

        applicable_candidates.pop().map(|(probe, status)| match status {
            ProbeResult::Match => {
                Ok(probe
                    .to_unadjusted_pick(self_ty, unstable_candidates.cloned().unwrap_or_default()))
            }
            ProbeResult::NoMatch | ProbeResult::BadReturnType => Err(MethodError::BadReturnType),
        })
    }
}

impl<'tcx> Pick<'tcx> {
    /// In case there were unstable name collisions, emit them as a lint.
    /// Checks whether two picks do not refer to the same trait item for the same `Self` type.
    /// Only useful for comparisons of picks in order to improve diagnostics.
    /// Do not use for type checking.
    pub fn differs_from(&self, other: &Self) -> bool {
        let Self {
            item:
                AssocItem {
                    def_id,
                    name: _,
                    kind: _,
                    container: _,
                    trait_item_def_id: _,
                    fn_has_self_parameter: _,
                    opt_rpitit_info: _,
                },
            kind: _,
            import_ids: _,
            autoderefs: _,
            autoref_or_ptr_adjustment: _,
            self_ty,
            unstable_candidates: _,
        } = *self;
        self_ty != other.self_ty || def_id != other.item.def_id
    }

    /// In case there were unstable name collisions, emit them as a lint.
    pub fn maybe_emit_unstable_name_collision_hint(
        &self,
        tcx: TyCtxt<'tcx>,
        span: Span,
        scope_expr_id: HirId,
    ) {
        if self.unstable_candidates.is_empty() {
            return;
        }
        let def_kind = self.item.kind.as_def_kind();
        tcx.node_span_lint(
            lint::builtin::UNSTABLE_NAME_COLLISIONS,
            scope_expr_id,
            span,
            format!(
                "{} {} with this name may be added to the standard library in the future",
                tcx.def_kind_descr_article(def_kind, self.item.def_id),
                tcx.def_kind_descr(def_kind, self.item.def_id),
            ),
            |lint| {
                match (self.item.kind, self.item.container) {
                    (ty::AssocKind::Fn, _) => {
                        // FIXME: This should be a `span_suggestion` instead of `help`
                        // However `self.span` only
                        // highlights the method name, so we can't use it. Also consider reusing
                        // the code from `report_method_error()`.
                        lint.help(format!(
                            "call with fully qualified syntax `{}(...)` to keep using the current \
                             method",
                            tcx.def_path_str(self.item.def_id),
                        ));
                    }
                    (ty::AssocKind::Const, ty::AssocItemContainer::TraitContainer) => {
                        let def_id = self.item.container_id(tcx);
                        lint.span_suggestion(
                            span,
                            "use the fully qualified path to the associated const",
                            format!(
                                "<{} as {}>::{}",
                                self.self_ty,
                                tcx.def_path_str(def_id),
                                self.item.name
                            ),
                            Applicability::MachineApplicable,
                        );
                    }
                    _ => {}
                }
                tcx.disabled_nightly_features(
                    lint,
                    Some(scope_expr_id),
                    self.unstable_candidates.iter().map(|(candidate, feature)| {
                        (format!(" `{}`", tcx.def_path_str(candidate.item.def_id)), *feature)
                    }),
                );
            },
        );
    }
}

impl<'a, 'tcx> ProbeContext<'a, 'tcx> {
    fn select_trait_candidate(
        &self,
        trait_ref: ty::TraitRef<'tcx>,
    ) -> traits::SelectionResult<'tcx, traits::Selection<'tcx>> {
        let cause = traits::ObligationCause::misc(self.span, self.outer_ctx.body_id);
        let obligation = traits::Obligation::new(self.tcx, cause, self.outer_ctx.param_env, trait_ref);
        traits::SelectionContext::new(&self.outer_ctx.infcx).select(&obligation)
    }

    fn candidate_source(&self, candidate: &Candidate<'tcx>, self_ty: Ty<'tcx>) -> CandidateSource {
        match candidate.kind {
            InherentImplCandidate(_) => {
                CandidateSource::Impl(candidate.item.container_id(self.tcx))
            }
            ObjectCandidate(_) | WhereClauseCandidate(_) => {
                CandidateSource::Trait(candidate.item.container_id(self.tcx))
            }
            TraitCandidate(trait_ref) => self.outer_ctx.infcx.probe(|_| {
                let trait_ref =
                    self.outer_ctx.infcx.instantiate_binder_with_fresh_vars(self.span, infer::FnCall, trait_ref);
                let (xform_self_ty, _) =
                    self.xform_self_ty(candidate.item, trait_ref.self_ty(), trait_ref.args);
                let _ = self.outer_ctx.infcx.at(&ObligationCause::dummy(), self.outer_ctx.param_env).sup(
                    DefineOpaqueTypes::No,
                    xform_self_ty,
                    self_ty,
                );
                match self.select_trait_candidate(trait_ref) {
                    Ok(Some(traits::ImplSource::UserDefined(ref impl_data))) => {
                        // If only a single impl matches, make the error message point
                        // to that impl.
                        CandidateSource::Impl(impl_data.impl_def_id)
                    }
                    _ => CandidateSource::Trait(candidate.item.container_id(self.tcx)),
                }
            }),
        }
    }

    fn consider_probe(
        &self,
        self_ty: Ty<'tcx>,
        probe: &Candidate<'tcx>,
        possibly_unsatisfied_predicates: &mut Vec<(
            ty::Predicate<'tcx>,
            Option<ty::Predicate<'tcx>>,
            Option<ObligationCause<'tcx>>,
        )>,
    ) -> ProbeResult {
        //debug!("consider_probe: self_ty={:?} probe={:?}", self_ty, probe);

        self.outer_ctx.infcx.probe(|snapshot| {
            let outer_universe = self.outer_ctx.infcx.universe();

            let mut result = ProbeResult::Match;
            let cause = &self.outer_ctx.misc(self.span);
            let ocx = ObligationCtxt::new(&self.outer_ctx.infcx);

            let mut trait_predicate = None;
            let (mut xform_self_ty, mut xform_ret_ty);

            match probe.kind {
                InherentImplCandidate(impl_def_id) => {
                    let impl_args = self.outer_ctx.infcx.fresh_args_for_item(self.span, impl_def_id);
                    let impl_ty = self.tcx.type_of(impl_def_id).instantiate(self.tcx, impl_args);
                    (xform_self_ty, xform_ret_ty) =
                        self.xform_self_ty(probe.item, impl_ty, impl_args);
                    xform_self_ty = ocx.normalize(cause, self.outer_ctx.param_env, xform_self_ty);
                    // FIXME: Make this `ocx.sup` once we define opaques more eagerly.
                    match self.outer_ctx.infcx.at(cause, self.outer_ctx.param_env).sup(
                        DefineOpaqueTypes::No,
                        xform_self_ty,
                        self_ty,
                    ) {
                        Ok(infer_ok) => {
                            ocx.register_infer_ok_obligations(infer_ok);
                        }
                        Err(_err) => {
                            //debug!("--> cannot relate self-types {:?}", err);
                            return ProbeResult::NoMatch;
                        }
                    }
                    // FIXME: Weirdly, we normalize the ret ty in this candidate, but no other candidates.
                    xform_ret_ty = ocx.normalize(cause, self.outer_ctx.param_env, xform_ret_ty);
                    // Check whether the impl imposes obligations we have to worry about.
                    let impl_def_id = probe.item.container_id(self.tcx);
                    let impl_bounds =
                        self.tcx.predicates_of(impl_def_id).instantiate(self.tcx, impl_args);
                    let impl_bounds = ocx.normalize(cause, self.outer_ctx.param_env, impl_bounds);
                    // Convert the bounds into obligations.
                    ocx.register_obligations(traits::predicates_for_generics(
                        |idx, span| {
                            let code = if span.is_dummy() {
                                traits::ExprItemObligation(impl_def_id, self.scope_expr_id, idx)
                            } else {
                                traits::ExprBindingObligation(
                                    impl_def_id,
                                    span,
                                    self.scope_expr_id,
                                    idx,
                                )
                            };
                            ObligationCause::new(self.span, self.outer_ctx.body_id, code)
                        },
                        self.outer_ctx.param_env,
                        impl_bounds,
                    ));
                }
                TraitCandidate(poly_trait_ref) => {
                    // Some trait methods are excluded for arrays before 2021.
                    // (`array.into_iter()` wants a slice iterator for compatibility.)
                    if let Some(method_name) = self.method_name {
                        if self_ty.is_array() && !method_name.span.at_least_rust_2021() {
                            let trait_def = self.tcx.trait_def(poly_trait_ref.def_id());
                            if trait_def.skip_array_during_method_dispatch {
                                return ProbeResult::NoMatch;
                            }
                        }
                    }

                    let trait_ref = self.outer_ctx.infcx.instantiate_binder_with_fresh_vars(
                        self.span,
                        infer::FnCall,
                        poly_trait_ref,
                    );
                    let trait_ref = ocx.normalize(cause, self.outer_ctx.param_env, trait_ref);
                    (xform_self_ty, xform_ret_ty) =
                        self.xform_self_ty(probe.item, trait_ref.self_ty(), trait_ref.args);
                    xform_self_ty = ocx.normalize(cause, self.outer_ctx.param_env, xform_self_ty);
                    // FIXME: Make this `ocx.sup` once we define opaques more eagerly.
                    match self.outer_ctx.infcx.at(cause, self.outer_ctx.param_env).sup(
                        DefineOpaqueTypes::No,
                        xform_self_ty,
                        self_ty,
                    ) {
                        Ok(infer_ok) => {
                            ocx.register_infer_ok_obligations(infer_ok);
                        }
                        Err(_err) => {
                            //debug!("--> cannot relate self-types {:?}", err);
                            return ProbeResult::NoMatch;
                        }
                    }
                    let obligation = traits::Obligation::new(
                        self.tcx,
                        cause.clone(),
                        self.outer_ctx.param_env,
                        ty::Binder::dummy(trait_ref),
                    );

                    // FIXME(-Znext-solver): We only need this hack to deal with fatal
                    // overflow in the old solver.
                    if self.outer_ctx.infcx.next_trait_solver() || self.outer_ctx.infcx.predicate_may_hold(&obligation)
                    {
                        ocx.register_obligation(obligation);
                    } else {
                        result = ProbeResult::NoMatch;
                        if let Ok(Some(candidate)) = self.select_trait_candidate(trait_ref) {
                            for nested_obligation in candidate.nested_obligations() {
                                if !self.outer_ctx.infcx.predicate_may_hold(&nested_obligation) {
                                    possibly_unsatisfied_predicates.push((
                                        self.outer_ctx.infcx.resolve_vars_if_possible(nested_obligation.predicate),
                                        Some(self.outer_ctx.infcx.resolve_vars_if_possible(obligation.predicate)),
                                        Some(nested_obligation.cause),
                                    ));
                                }
                            }
                        }
                    }

                    trait_predicate = Some(ty::Binder::dummy(trait_ref).to_predicate(self.tcx));
                }
                ObjectCandidate(poly_trait_ref) | WhereClauseCandidate(poly_trait_ref) => {
                    let trait_ref = self.outer_ctx.infcx.instantiate_binder_with_fresh_vars(
                        self.span,
                        infer::FnCall,
                        poly_trait_ref,
                    );
                    (xform_self_ty, xform_ret_ty) =
                        self.xform_self_ty(probe.item, trait_ref.self_ty(), trait_ref.args);
                    xform_self_ty = ocx.normalize(cause, self.outer_ctx.param_env, xform_self_ty);
                    // FIXME: Make this `ocx.sup` once we define opaques more eagerly.
                    match self.outer_ctx.infcx.at(cause, self.outer_ctx.param_env).sup(
                        DefineOpaqueTypes::No,
                        xform_self_ty,
                        self_ty,
                    ) {
                        Ok(infer_ok) => {
                            ocx.register_infer_ok_obligations(infer_ok);
                        }
                        Err(_err) => {
                            //debug!("--> cannot relate self-types {:?}", err);
                            return ProbeResult::NoMatch;
                        }
                    }
                }
            }

            // Evaluate those obligations to see if they might possibly hold.
            for error in ocx.select_where_possible() {
                result = ProbeResult::NoMatch;
                let nested_predicate = self.outer_ctx.infcx.resolve_vars_if_possible(error.obligation.predicate);
                if let Some(trait_predicate) = trait_predicate
                    && nested_predicate == self.outer_ctx.infcx.resolve_vars_if_possible(trait_predicate)
                {
                    // Don't report possibly unsatisfied predicates if the root
                    // trait obligation from a `TraitCandidate` is unsatisfied.
                    // That just means the candidate doesn't hold.
                } else {
                    possibly_unsatisfied_predicates.push((
                        nested_predicate,
                        Some(self.outer_ctx.infcx.resolve_vars_if_possible(error.root_obligation.predicate))
                            .filter(|root_predicate| *root_predicate != nested_predicate),
                        Some(error.obligation.cause),
                    ));
                }
            }

            if let ProbeResult::Match = result
                && let Some(return_ty) = self.return_type
                && let Some(mut xform_ret_ty) = xform_ret_ty
            {
                // `xform_ret_ty` has only been normalized for `InherentImplCandidate`.
                // We don't normalize the other candidates for perf/backwards-compat reasons...
                // but `self.return_type` is only set on the diagnostic-path, so we
                // should be okay doing it here.
                if !matches!(probe.kind, InherentImplCandidate(_)) {
                    xform_ret_ty = ocx.normalize(&cause, self.outer_ctx.param_env, xform_ret_ty);
                }

                //debug!("comparing return_ty {:?} with xform ret ty {:?}", return_ty, xform_ret_ty);
                match ocx.sup(cause, self.outer_ctx.param_env, return_ty, xform_ret_ty) {
                    Ok(()) => {}
                    Err(_) => {
                        result = ProbeResult::BadReturnType;
                    }
                }

                // Evaluate those obligations to see if they might possibly hold.
                for error in ocx.select_where_possible() {
                    result = ProbeResult::NoMatch;
                    possibly_unsatisfied_predicates.push((
                        error.obligation.predicate,
                        Some(error.root_obligation.predicate)
                            .filter(|predicate| *predicate != error.obligation.predicate),
                        Some(error.root_obligation.cause),
                    ));
                }
            }

            // Previously, method probe used `evaluate_predicate` to determine if a predicate
            // was impossible to satisfy. This did a leak check, so we must also do a leak
            // check here to prevent backwards-incompatible ambiguity being introduced. See
            // `tests/ui/methods/leak-check-disquality.rs` for a simple example of when this
            // may happen.
            if let Err(_) = self.outer_ctx.infcx.leak_check(outer_universe, Some(snapshot)) {
                result = ProbeResult::NoMatch;
            }

            result
        })
    }

    /// Sometimes we get in a situation where we have multiple probes that are all impls of the
    /// same trait, but we don't know which impl to use. In this case, since in all cases the
    /// external interface of the method can be determined from the trait, it's ok not to decide.
    /// We can basically just collapse all of the probes for various impls into one where-clause
    /// probe. This will result in a pending obligation so when more type-info is available we can
    /// make the final decision.
    ///
    /// Example (`tests/ui/method-two-trait-defer-resolution-1.rs`):
    ///
    /// ```ignore (illustrative)
    /// trait Foo { ... }
    /// impl Foo for Vec<i32> { ... }
    /// impl Foo for Vec<usize> { ... }
    /// ```
    ///
    /// Now imagine the receiver is `Vec<_>`. It doesn't really matter at this time which impl we
    /// use, so it's ok to just commit to "using the method from the trait Foo".
    fn collapse_candidates_to_trait_pick(
        &self,
        self_ty: Ty<'tcx>,
        probes: &[(&Candidate<'tcx>, ProbeResult)],
    ) -> Option<Pick<'tcx>> {
        // Do all probes correspond to the same trait?
        let container = probes[0].0.item.trait_container(self.tcx)?;
        for (p, _) in &probes[1..] {
            let p_container = p.item.trait_container(self.tcx)?;
            if p_container != container {
                return None;
            }
        }

        // FIXME: check the return type here somehow.
        // If so, just use this trait and call it a day.
        Some(Pick {
            item: probes[0].0.item,
            kind: TraitPick,
            import_ids: probes[0].0.import_ids.clone(),
            autoderefs: 0,
            autoref_or_ptr_adjustment: None,
            self_ty,
            unstable_candidates: vec![],
        })
    }

    /// Similarly to `probe_for_return_type`, this method attempts to find the best matching
    /// candidate method where the method name may have been misspelled. Similarly to other
    /// edit distance based suggestions, we provide at most one such suggestion.
    pub(crate) fn probe_for_similar_candidate(
        &mut self,
    ) -> Result<Option<ty::AssocItem>, MethodError<'tcx>> {
        //debug!("probing for method names similar to {:?}", self.method_name);

        self.outer_ctx.infcx.probe(|_| {
            let mut pcx = ProbeContext::new(
                self.outer_ctx,
                self.span,
                self.mode,
                self.method_name,
                self.return_type,
                self.orig_steps_var_values,
                self.steps,
                self.scope_expr_id,
                IsSuggestion(true),
            );
            pcx.allow_similar_names = true;
            pcx.assemble_inherent_candidates();
            pcx.assemble_extension_candidates_for_all_traits();

            let method_names = pcx.candidate_method_names(|_| true);
            pcx.allow_similar_names = false;
            let applicable_close_candidates: Vec<ty::AssocItem> = method_names
                .iter()
                .filter_map(|&method_name| {
                    pcx.reset();
                    pcx.method_name = Some(method_name);
                    pcx.assemble_inherent_candidates();
                    pcx.assemble_extension_candidates_for_all_traits();
                    pcx.pick_core().and_then(|pick| pick.ok()).map(|pick| pick.item)
                })
                .collect();

            if applicable_close_candidates.is_empty() {
                Ok(None)
            } else {
                let best_name = {
                    let names = applicable_close_candidates
                        .iter()
                        .map(|cand| cand.name)
                        .collect::<Vec<Symbol>>();
                    find_best_match_for_name_with_substrings(
                        &names,
                        self.method_name.unwrap().name,
                        None,
                    )
                }
                .or_else(|| {
                    applicable_close_candidates
                        .iter()
                        .find(|cand| self.matches_by_doc_alias(cand.def_id))
                        .map(|cand| cand.name)
                });
                Ok(best_name.and_then(|best_name| {
                    applicable_close_candidates.into_iter().find(|method| method.name == best_name)
                }))
            }
        })
    }

    ///////////////////////////////////////////////////////////////////////////
    // MISCELLANY
    fn has_applicable_self(&self, item: &ty::AssocItem) -> bool {
        // "Fast track" -- check for usage of sugar when in method call
        // mode.
        //
        // In Path mode (i.e., resolving a value like `T::next`), consider any
        // associated value (i.e., methods, constants) but not types.
        match self.mode {
            Mode::MethodCall => item.fn_has_self_parameter,
            Mode::Path => match item.kind {
                ty::AssocKind::Type => false,
                ty::AssocKind::Fn | ty::AssocKind::Const => true,
            },
        }
        // FIXME -- check for types that deref to `Self`,
        // like `Rc<Self>` and so on.
        //
        // Note also that the current code will break if this type
        // includes any of the type parameters defined on the method
        // -- but this could be overcome.
    }

    fn record_static_candidate(&self, source: CandidateSource) {
        self.static_candidates.borrow_mut().push(source);
    }

    fn xform_self_ty(
        &self,
        item: ty::AssocItem,
        impl_ty: Ty<'tcx>,
        args: GenericArgsRef<'tcx>,
    ) -> (Ty<'tcx>, Option<Ty<'tcx>>) {
        if item.kind == ty::AssocKind::Fn && self.mode == Mode::MethodCall {
            let sig = self.xform_method_sig(item.def_id, args);
            (sig.inputs()[0], Some(sig.output()))
        } else {
            (impl_ty, None)
        }
    }

    fn xform_method_sig(&self, method: DefId, args: GenericArgsRef<'tcx>) -> ty::FnSig<'tcx> {
        let fn_sig = self.tcx.fn_sig(method);
        //debug!(?fn_sig);

        assert!(!args.has_escaping_bound_vars());

        // It is possible for type parameters or early-bound lifetimes
        // to appear in the signature of `self`. The generic parameters
        // we are given do not include type/lifetime parameters for the
        // method yet. So create fresh variables here for those too,
        // if there are any.
        let generics = self.tcx.generics_of(method);
        assert_eq!(args.len(), generics.parent_count);

        let xform_fn_sig = if generics.params.is_empty() {
            fn_sig.instantiate(self.tcx, args)
        } else {
            let args = GenericArgs::for_item(self.tcx, method, |param, _| {
                let i = param.index as usize;
                if i < args.len() {
                    args[i]
                } else {
                    match param.kind {
                        GenericParamDefKind::Lifetime => {
                            // In general, during probe we erase regions.
                            self.tcx.lifetimes.re_erased.into()
                        }
                        GenericParamDefKind::Type { .. } | GenericParamDefKind::Const { .. } => {
                            self.outer_ctx.infcx.var_for_def(self.span, param)
                        }
                    }
                }
            });
            fn_sig.instantiate(self.tcx, args)
        };

        self.tcx.instantiate_bound_regions_with_erased(xform_fn_sig)
    }

    /// Determine if the given associated item type is relevant in the current context.
    fn is_relevant_kind_for_mode(&self, kind: ty::AssocKind) -> bool {
        match (self.mode, kind) {
            (Mode::MethodCall, ty::AssocKind::Fn) => true,
            (Mode::Path, ty::AssocKind::Const | ty::AssocKind::Fn) => true,
            _ => false,
        }
    }

    /// Determine if the associated item with the given DefId matches
    /// the desired name via a doc alias.
    fn matches_by_doc_alias(&self, def_id: DefId) -> bool {
        let Some(name) = self.method_name else {
            return false;
        };
        let Some(local_def_id) = def_id.as_local() else {
            return false;
        };
        let hir_id = self.tcx.local_def_id_to_hir_id(local_def_id);
        let attrs = self.tcx.hir().attrs(hir_id);
        for attr in attrs {
            if sym::doc == attr.name_or_empty() {
            } else if sym::rustc_confusables == attr.name_or_empty() {
                let Some(confusables) = attr.meta_item_list() else {
                    continue;
                };
                // #[rustc_confusables("foo", "bar"))]
                for n in confusables {
                    if let Some(lit) = n.lit()
                        && name.as_str() == lit.symbol.as_str()
                    {
                        return true;
                    }
                }
                continue;
            } else {
                continue;
            };
            let Some(values) = attr.meta_item_list() else {
                continue;
            };
            for v in values {
                if v.name_or_empty() != sym::alias {
                    continue;
                }
                if let Some(nested) = v.meta_item_list() {
                    // #[doc(alias("foo", "bar"))]
                    for n in nested {
                        if let Some(lit) = n.lit()
                            && name.as_str() == lit.symbol.as_str()
                        {
                            return true;
                        }
                    }
                } else if let Some(meta) = v.meta_item()
                    && let Some(lit) = meta.name_value_literal()
                    && name.as_str() == lit.symbol.as_str()
                {
                    // #[doc(alias = "foo")]
                    return true;
                }
            }
        }
        false
    }

    /// Finds the method with the appropriate name (or return type, as the case may be). If
    /// `allow_similar_names` is set, find methods with close-matching names.
    // The length of the returned iterator is nearly always 0 or 1 and this
    // method is fairly hot.
    fn impl_or_trait_item(&self, def_id: DefId) -> SmallVec<[ty::AssocItem; 1]> {
        if let Some(name) = self.method_name {
            if self.allow_similar_names {
                let max_dist = max(name.as_str().len(), 3) / 3;
                self.tcx
                    .associated_items(def_id)
                    .in_definition_order()
                    .filter(|x| {
                        if !self.is_relevant_kind_for_mode(x.kind) {
                            return false;
                        }
                        if self.matches_by_doc_alias(x.def_id) {
                            return true;
                        }
                        match edit_distance_with_substrings(
                            name.as_str(),
                            x.name.as_str(),
                            max_dist,
                        ) {
                            Some(d) => d > 0,
                            None => false,
                        }
                    })
                    .copied()
                    .collect()
            } else {
                self
                    .associated_value(def_id, name)
                    .filter(|x| self.is_relevant_kind_for_mode(x.kind))
                    .map_or_else(SmallVec::new, |x| SmallVec::from_buf([x]))
            }
        } else {
            self.tcx
                .associated_items(def_id)
                .in_definition_order()
                .filter(|x| self.is_relevant_kind_for_mode(x.kind))
                .copied()
                .collect()
        }
    }

    pub fn associated_value(&self, def_id: DefId, item_name: Ident) -> Option<ty::AssocItem> {
        self.tcx
            .associated_items(def_id)
            .find_by_name_and_namespace(self.tcx, item_name, Namespace::ValueNS, def_id)
            .copied()
    }
}

impl<'tcx> Candidate<'tcx> {
    fn to_unadjusted_pick(
        &self,
        self_ty: Ty<'tcx>,
        unstable_candidates: Vec<(Candidate<'tcx>, Symbol)>,
    ) -> Pick<'tcx> {
        Pick {
            item: self.item,
            kind: match self.kind {
                InherentImplCandidate(_) => InherentImplPick,
                ObjectCandidate(_) => ObjectPick,
                TraitCandidate(_) => TraitPick,
                WhereClauseCandidate(trait_ref) => {
                    // Only trait derived from where-clauses should
                    // appear here, so they should not contain any
                    // inference variables or other artifacts. This
                    // means they are safe to put into the
                    // `WhereClausePick`.
                    assert!(
                        !trait_ref.skip_binder().args.has_infer()
                            && !trait_ref.skip_binder().args.has_placeholders()
                    );

                    WhereClausePick(trait_ref)
                }
            },
            import_ids: self.import_ids.clone(),
            autoderefs: 0,
            autoref_or_ptr_adjustment: None,
            self_ty,
            unstable_candidates,
        }
    }
}

#[derive(Copy, Clone, PartialEq, Eq)]
pub struct TraitInfo {
    pub def_id: DefId,
}

/// Retrieves all traits in this crate and any dependent crates,
/// and wraps them into `TraitInfo` for custom sorting.
pub fn all_traits(tcx: TyCtxt<'_>) -> Vec<TraitInfo> {
    tcx.all_traits().map(|def_id| TraitInfo { def_id }).collect()
}
