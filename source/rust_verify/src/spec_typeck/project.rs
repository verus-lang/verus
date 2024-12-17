//! Code for projecting associated types out of trait references.

use std::ops::ControlFlow;

use rustc_trait_selection::traits::specialization_graph;
use rustc_trait_selection::traits::translate_args;
use rustc_trait_selection::traits::MismatchedProjectionTypes;
use rustc_trait_selection::traits::Obligation;
use rustc_trait_selection::traits::ObligationCause;
use rustc_trait_selection::traits::PredicateObligation;
use rustc_trait_selection::traits::Selection;
use rustc_trait_selection::traits::SelectionContext;
use rustc_trait_selection::traits::SelectionError;
use rustc_trait_selection::traits::{Normalized, NormalizedTy, ProjectionCacheEntry, ProjectionCacheKey};
use rustc_middle::traits::BuiltinImplSource;
use rustc_middle::traits::ImplSource;
use rustc_middle::traits::ImplSourceUserDefinedData;

use rustc_trait_selection::errors::InherentProjectionNormalizationOverflow;
use rustc_trait_selection::infer::type_variable::TypeVariableOrigin;
use rustc_trait_selection::infer::{BoundRegionConversionTime, InferOk};
//use rustc_trait_selection::traits::normalize::normalize_with_depth;
use rustc_trait_selection::traits::query::evaluate_obligation::InferCtxtExt as _;
use rustc_data_structures::sso::SsoHashSet;
use rustc_data_structures::stack::ensure_sufficient_stack;
use rustc_errors::ErrorGuaranteed;
use rustc_hir::def::DefKind;
use rustc_hir::lang_items::LangItem;
use rustc_infer::infer::resolve::OpportunisticRegionResolver;
use rustc_infer::infer::DefineOpaqueTypes;
use rustc_middle::traits::select::OverflowError;
use rustc_middle::ty::fold::TypeFoldable;
use rustc_middle::ty::visit::{MaxUniverse, TypeVisitable, TypeVisitableExt};
use rustc_middle::ty::{self, Term, ToPredicate, Ty, TyCtxt};
use rustc_span::symbol::sym;
use rustc_middle::bug;
use rustc_middle::span_bug;

pub use rustc_middle::traits::Reveal;

pub type PolyProjectionObligation<'tcx> = Obligation<'tcx, ty::PolyProjectionPredicate<'tcx>>;

pub type ProjectionObligation<'tcx> = Obligation<'tcx, ty::ProjectionPredicate<'tcx>>;

pub type ProjectionTyObligation<'tcx> = Obligation<'tcx, ty::AliasTy<'tcx>>;

pub(super) struct InProgress;

/// When attempting to resolve `<T as TraitRef>::Name` ...
#[derive(Debug)]
pub enum ProjectionError<'tcx> {
    /// ...we found multiple sources of information and couldn't resolve the ambiguity.
    TooManyCandidates,

    /// ...an error occurred matching `T : TraitRef`
    TraitSelectionError(SelectionError<'tcx>),
}

#[derive(PartialEq, Eq, Debug)]
enum ProjectionCandidate<'tcx> {
    /// From a where-clause in the env or object type
    ParamEnv(ty::PolyProjectionPredicate<'tcx>),

    /// From the definition of `Trait` when you have something like
    /// `<<A as Trait>::B as Trait2>::C`.
    TraitDef(ty::PolyProjectionPredicate<'tcx>),

    /// Bounds specified on an object type
    Object(ty::PolyProjectionPredicate<'tcx>),

    /// From an "impl" (or a "pseudo-impl" returned by select)
    Select(Selection<'tcx>),
}

enum ProjectionCandidateSet<'tcx> {
    None,
    Single(ProjectionCandidate<'tcx>),
    Ambiguous,
    Error(SelectionError<'tcx>),
}

impl<'tcx> ProjectionCandidateSet<'tcx> {
    fn mark_ambiguous(&mut self) {
        *self = ProjectionCandidateSet::Ambiguous;
    }

    fn mark_error(&mut self, err: SelectionError<'tcx>) {
        *self = ProjectionCandidateSet::Error(err);
    }

    // Returns true if the push was successful, or false if the candidate
    // was discarded -- this could be because of ambiguity, or because
    // a higher-priority candidate is already there.
    fn push_candidate(&mut self, candidate: ProjectionCandidate<'tcx>) -> bool {
        use self::ProjectionCandidate::*;
        use self::ProjectionCandidateSet::*;

        // This wacky variable is just used to try and
        // make code readable and avoid confusing paths.
        // It is assigned a "value" of `()` only on those
        // paths in which we wish to convert `*self` to
        // ambiguous (and return false, because the candidate
        // was not used). On other paths, it is not assigned,
        // and hence if those paths *could* reach the code that
        // comes after the match, this fn would not compile.
        let convert_to_ambiguous;

        match self {
            None => {
                *self = Single(candidate);
                return true;
            }

            Single(current) => {
                // Duplicates can happen inside ParamEnv. In the case, we
                // perform a lazy deduplication.
                if current == &candidate {
                    return false;
                }

                // Prefer where-clauses. As in select, if there are multiple
                // candidates, we prefer where-clause candidates over impls. This
                // may seem a bit surprising, since impls are the source of
                // "truth" in some sense, but in fact some of the impls that SEEM
                // applicable are not, because of nested obligations. Where
                // clauses are the safer choice. See the comment on
                // `select::SelectionCandidate` and #21974 for more details.
                match (current, candidate) {
                    (ParamEnv(..), ParamEnv(..)) => convert_to_ambiguous = (),
                    (ParamEnv(..), _) => return false,
                    (_, ParamEnv(..)) => bug!(
                        "should never prefer non-param-env candidates over param-env candidates"
                    ),
                    (_, _) => convert_to_ambiguous = (),
                }
            }

            Ambiguous | Error(..) => {
                return false;
            }
        }

        // We only ever get here when we moved from a single candidate
        // to ambiguous.
        let () = convert_to_ambiguous;
        *self = Ambiguous;
        false
    }
}

/// States returned from `poly_project_and_unify_type`. Takes the place
/// of the old return type, which was:
/// ```ignore (not-rust)
/// Result<
///     Result<Option<Vec<PredicateObligation<'tcx>>>, InProgress>,
///     MismatchedProjectionTypes<'tcx>,
/// >
/// ```
pub(super) enum ProjectAndUnifyResult<'tcx> {
    /// The projection bound holds subject to the given obligations. If the
    /// projection cannot be normalized because the required trait bound does
    /// not hold, this is returned, with `obligations` being a predicate that
    /// cannot be proven.
    Holds(Vec<PredicateObligation<'tcx>>),
    /// The projection cannot be normalized due to ambiguity. Resolving some
    /// inference variables in the projection may fix this.
    FailedNormalization,
    /// The project cannot be normalized because `poly_project_and_unify_type`
    /// is called recursively while normalizing the same projection.
    Recursive,
    // the projection can be normalized, but is not equal to the expected type.
    // Returns the type error that arose from the mismatch.
    MismatchedProjectionTypes(MismatchedProjectionTypes<'tcx>),
}

/*
/// Evaluates constraints of the form:
/// ```ignore (not-rust)
/// for<...> <T as Trait>::U == V
/// ```
/// If successful, this may result in additional obligations. Also returns
/// the projection cache key used to track these additional obligations.
//#[instrument(level = "debug", skip(selcx))]
pub(super) fn poly_project_and_unify_type<'cx, 'tcx>(
    selcx: &mut SelectionContext<'cx, 'tcx>,
    obligation: &PolyProjectionObligation<'tcx>,
) -> ProjectAndUnifyResult<'tcx> {
    let infcx = selcx.infcx;
    let r = infcx.commit_if_ok(|_snapshot| {
        let old_universe = infcx.universe();
        let placeholder_predicate = infcx.enter_forall_and_leak_universe(obligation.predicate);
        let new_universe = infcx.universe();

        let placeholder_obligation = obligation.with(infcx.tcx, placeholder_predicate);
        match project_and_unify_type(selcx, &placeholder_obligation) {
            ProjectAndUnifyResult::MismatchedProjectionTypes(e) => Err(e),
            ProjectAndUnifyResult::Holds(obligations)
                if old_universe != new_universe
                    && selcx.tcx().features().generic_associated_types_extended =>
            {
                // If the `generic_associated_types_extended` feature is active, then we ignore any
                // obligations references lifetimes from any universe greater than or equal to the
                // universe just created. Otherwise, we can end up with something like `for<'a> I: 'a`,
                // which isn't quite what we want. Ideally, we want either an implied
                // `for<'a where I: 'a> I: 'a` or we want to "lazily" check these hold when we
                // instantiate concrete regions. There is design work to be done here; until then,
                // however, this allows experimenting potential GAT features without running into
                // well-formedness issues.
                let new_obligations = obligations
                    .into_iter()
                    .filter(|obligation| {
                        let mut visitor = MaxUniverse::new();
                        obligation.predicate.visit_with(&mut visitor);
                        visitor.max_universe() < new_universe
                    })
                    .collect();
                Ok(ProjectAndUnifyResult::Holds(new_obligations))
            }
            other => Ok(other),
        }
    });

    match r {
        Ok(inner) => inner,
        Err(err) => ProjectAndUnifyResult::MismatchedProjectionTypes(err),
    }
}
*/

/*
/// Evaluates constraints of the form:
/// ```ignore (not-rust)
/// <T as Trait>::U == V
/// ```
/// If successful, this may result in additional obligations.
///
/// See [poly_project_and_unify_type] for an explanation of the return value.
//#[instrument(level = "debug", skip(selcx))]
fn project_and_unify_type<'cx, 'tcx>(
    selcx: &mut SelectionContext<'cx, 'tcx>,
    obligation: &ProjectionObligation<'tcx>,
) -> ProjectAndUnifyResult<'tcx> {
    let mut obligations = vec![];

    let infcx = selcx.infcx;
    let normalized = match opt_normalize_projection_type(
        selcx,
        obligation.param_env,
        obligation.predicate.projection_ty,
        obligation.cause.clone(),
        obligation.recursion_depth,
        &mut obligations,
    ) {
        Ok(Some(n)) => n,
        Ok(None) => return ProjectAndUnifyResult::FailedNormalization,
        Err(InProgress) => return ProjectAndUnifyResult::Recursive,
    };
    //debug!(?normalized, ?obligations, "project_and_unify_type result");
    let actual = obligation.predicate.term;
    // For an example where this is necessary see tests/ui/impl-trait/nested-return-type2.rs
    // This allows users to omit re-mentioning all bounds on an associated type and just use an
    // `impl Trait` for the assoc type to add more bounds.
    let InferOk { value: actual, obligations: new } =
        selcx.infcx.replace_opaque_types_with_inference_vars(
            actual,
            obligation.cause.body_id,
            obligation.cause.span,
            obligation.param_env,
        );
    obligations.extend(new);

    // Need to define opaque types to support nested opaque types like `impl Fn() -> impl Trait`
    match infcx.at(&obligation.cause, obligation.param_env).eq(
        DefineOpaqueTypes::Yes,
        normalized,
        actual,
    ) {
        Ok(InferOk { obligations: inferred_obligations, value: () }) => {
            obligations.extend(inferred_obligations);
            ProjectAndUnifyResult::Holds(obligations)
        }
        Err(err) => {
            //debug!("equating types encountered error {:?}", err);
            ProjectAndUnifyResult::MismatchedProjectionTypes(MismatchedProjectionTypes { err })
        }
    }
}
*/

/*
/// The guts of `normalize`: normalize a specific projection like `<T
/// as Trait>::Item`. The result is always a type (and possibly
/// additional obligations). If ambiguity arises, which implies that
/// there are unresolved type variables in the projection, we will
/// instantiate it with a fresh type variable `$X` and generate a new
/// obligation `<T as Trait>::Item == $X` for later.
pub fn normalize_projection_type<'a, 'b, 'tcx>(
    selcx: &'a mut SelectionContext<'b, 'tcx>,
    param_env: ty::ParamEnv<'tcx>,
    projection_ty: ty::AliasTy<'tcx>,
    cause: ObligationCause<'tcx>,
    depth: usize,
    obligations: &mut Vec<PredicateObligation<'tcx>>,
) -> Term<'tcx> {
    opt_normalize_projection_type(
        selcx,
        param_env,
        projection_ty,
        cause.clone(),
        depth,
        obligations,
    )
    .ok()
    .flatten()
    .unwrap_or_else(move || {
        // if we bottom out in ambiguity, create a type variable
        // and a deferred predicate to resolve this when more type
        // information is available.

        selcx.infcx.infer_projection(param_env, projection_ty, cause, depth + 1, obligations).into()
    })
}
*/

/*
/// The guts of `normalize`: normalize a specific projection like `<T
/// as Trait>::Item`. The result is always a type (and possibly
/// additional obligations). Returns `None` in the case of ambiguity,
/// which indicates that there are unbound type variables.
///
/// This function used to return `Option<NormalizedTy<'tcx>>`, which contains a
/// `Ty<'tcx>` and an obligations vector. But that obligation vector was very
/// often immediately appended to another obligations vector. So now this
/// function takes an obligations vector and appends to it directly, which is
/// slightly uglier but avoids the need for an extra short-lived allocation.
//#[instrument(level = "debug", skip(selcx, param_env, cause, obligations))]
pub(super) fn opt_normalize_projection_type<'a, 'b, 'tcx>(
    selcx: &'a mut SelectionContext<'b, 'tcx>,
    param_env: ty::ParamEnv<'tcx>,
    projection_ty: ty::AliasTy<'tcx>,
    cause: ObligationCause<'tcx>,
    depth: usize,
    obligations: &mut Vec<PredicateObligation<'tcx>>,
) -> Result<Option<Term<'tcx>>, InProgress> {
    let infcx = selcx.infcx;
    debug_assert!(!selcx.infcx.next_trait_solver());
    // Don't use the projection cache in intercrate mode -
    // the `infcx` may be re-used between intercrate in non-intercrate
    // mode, which could lead to using incorrect cache results.
    let use_cache = !selcx.is_intercrate();

    let projection_ty = infcx.resolve_vars_if_possible(projection_ty);
    let cache_key = ProjectionCacheKey::new(projection_ty, param_env);

    // FIXME(#20304) For now, I am caching here, which is good, but it
    // means we don't capture the type variables that are created in
    // the case of ambiguity. Which means we may create a large stream
    // of such variables. OTOH, if we move the caching up a level, we
    // would not benefit from caching when proving `T: Trait<U=Foo>`
    // bounds. It might be the case that we want two distinct caches,
    // or else another kind of cache entry.

    let cache_result = if use_cache {
        infcx.inner.borrow_mut().projection_cache().try_start(cache_key)
    } else {
        Ok(())
    };
    match cache_result {
        Ok(()) => { } //debug!("no cache"),
        Err(ProjectionCacheEntry::Ambiguous) => {
            // If we found ambiguity the last time, that means we will continue
            // to do so until some type in the key changes (and we know it
            // hasn't, because we just fully resolved it).
            //debug!("found cache entry: ambiguous");
            return Ok(None);
        }
        Err(ProjectionCacheEntry::InProgress) => {
            // Under lazy normalization, this can arise when
            // bootstrapping. That is, imagine an environment with a
            // where-clause like `A::B == u32`. Now, if we are asked
            // to normalize `A::B`, we will want to check the
            // where-clauses in scope. So we will try to unify `A::B`
            // with `A::B`, which can trigger a recursive
            // normalization.

            //debug!("found cache entry: in-progress");

            // Cache that normalizing this projection resulted in a cycle. This
            // should ensure that, unless this happens within a snapshot that's
            // rolled back, fulfillment or evaluation will notice the cycle.

            if use_cache {
                infcx.inner.borrow_mut().projection_cache().recur(cache_key);
            }
            return Err(InProgress);
        }
        Err(ProjectionCacheEntry::Recur) => {
            //debug!("recur cache");
            return Err(InProgress);
        }
        Err(ProjectionCacheEntry::NormalizedTy { ty, complete: _ }) => {
            // This is the hottest path in this function.
            //
            // If we find the value in the cache, then return it along
            // with the obligations that went along with it. Note
            // that, when using a fulfillment context, these
            // obligations could in principle be ignored: they have
            // already been registered when the cache entry was
            // created (and hence the new ones will quickly be
            // discarded as duplicated). But when doing trait
            // evaluation this is not the case, and dropping the trait
            // evaluations can causes ICEs (e.g., #43132).
            //debug!(?ty, "found normalized ty");
            obligations.extend(ty.obligations);
            return Ok(Some(ty.value));
        }
        Err(ProjectionCacheEntry::Error) => {
            //debug!("opt_normalize_projection_type: found error");
            let result = normalize_to_error(selcx, param_env, projection_ty, cause, depth);
            obligations.extend(result.obligations);
            return Ok(Some(result.value.into()));
        }
    }

    let obligation =
        Obligation::with_depth(selcx.tcx(), cause.clone(), depth, param_env, projection_ty);

    match project(selcx, &obligation) {
        Ok(Projected::Progress(Progress {
            term: projected_term,
            obligations: mut projected_obligations,
        })) => {
            // if projection succeeded, then what we get out of this
            // is also non-normalized (consider: it was derived from
            // an impl, where-clause etc) and hence we must
            // re-normalize it

            let projected_term = selcx.infcx.resolve_vars_if_possible(projected_term);

            let mut result = if projected_term.has_aliases() {
                let normalized_ty = normalize_with_depth_to(
                    selcx,
                    param_env,
                    cause,
                    depth + 1,
                    projected_term,
                    &mut projected_obligations,
                );

                Normalized { value: normalized_ty, obligations: projected_obligations }
            } else {
                Normalized { value: projected_term, obligations: projected_obligations }
            };

            let mut deduped = SsoHashSet::with_capacity(result.obligations.len());
            result.obligations.retain(|obligation| deduped.insert(obligation.clone()));

            if use_cache {
                infcx.inner.borrow_mut().projection_cache().insert_term(cache_key, result.clone());
            }
            obligations.extend(result.obligations);
            Ok(Some(result.value))
        }
        Ok(Projected::NoProgress(projected_ty)) => {
            let result = Normalized { value: projected_ty, obligations: vec![] };
            if use_cache {
                infcx.inner.borrow_mut().projection_cache().insert_term(cache_key, result.clone());
            }
            // No need to extend `obligations`.
            Ok(Some(result.value))
        }
        Err(ProjectionError::TooManyCandidates) => {
            //debug!("opt_normalize_projection_type: too many candidates");
            if use_cache {
                infcx.inner.borrow_mut().projection_cache().ambiguous(cache_key);
            }
            Ok(None)
        }
        Err(ProjectionError::TraitSelectionError(_)) => {
            //debug!("opt_normalize_projection_type: ERROR");
            // if we got an error processing the `T as Trait` part,
            // just return `ty::err` but add the obligation `T :
            // Trait`, which when processed will cause the error to be
            // reported later

            if use_cache {
                infcx.inner.borrow_mut().projection_cache().error(cache_key);
            }
            let result = normalize_to_error(selcx, param_env, projection_ty, cause, depth);
            obligations.extend(result.obligations);
            Ok(Some(result.value.into()))
        }
    }
}
*/

/// If we are projecting `<T as Trait>::Item`, but `T: Trait` does not
/// hold. In various error cases, we cannot generate a valid
/// normalized projection. Therefore, we create an inference variable
/// return an associated obligation that, when fulfilled, will lead to
/// an error.
///
/// Note that we used to return `Error` here, but that was quite
/// dubious -- the premise was that an error would *eventually* be
/// reported, when the obligation was processed. But in general once
/// you see an `Error` you are supposed to be able to assume that an
/// error *has been* reported, so that you can take whatever heuristic
/// paths you want to take. To make things worse, it was possible for
/// cycles to arise, where you basically had a setup like `<MyType<$0>
/// as Trait>::Foo == $0`. Here, normalizing `<MyType<$0> as
/// Trait>::Foo>` to `[type error]` would lead to an obligation of
/// `<MyType<[type error]> as Trait>::Foo`. We are supposed to report
/// an error for this obligation, but we legitimately should not,
/// because it contains `[type error]`. Yuck! (See issue #29857 for
/// one case where this arose.)
fn normalize_to_error<'a, 'tcx>(
    selcx: &SelectionContext<'a, 'tcx>,
    param_env: ty::ParamEnv<'tcx>,
    projection_ty: ty::AliasTy<'tcx>,
    cause: ObligationCause<'tcx>,
    depth: usize,
) -> NormalizedTy<'tcx> {
    let trait_ref = ty::Binder::dummy(projection_ty.trait_ref(selcx.tcx()));
    let trait_obligation = Obligation {
        cause,
        recursion_depth: depth,
        param_env,
        predicate: trait_ref.to_predicate(selcx.tcx()),
    };
    let tcx = selcx.infcx.tcx;
    let new_value = selcx.infcx.next_ty_var(TypeVariableOrigin {
        param_def_id: None,
        span: tcx.def_span(projection_ty.def_id),
    });
    Normalized { value: new_value, obligations: vec![trait_obligation] }
}

/*
/// Confirm and normalize the given inherent projection.
//#[instrument(level = "debug", skip(selcx, param_env, cause, obligations))]
pub fn normalize_inherent_projection<'a, 'b, 'tcx>(
    selcx: &'a mut SelectionContext<'b, 'tcx>,
    param_env: ty::ParamEnv<'tcx>,
    alias_ty: ty::AliasTy<'tcx>,
    cause: ObligationCause<'tcx>,
    depth: usize,
    obligations: &mut Vec<PredicateObligation<'tcx>>,
) -> Ty<'tcx> {
    let tcx = selcx.tcx();

    if !tcx.recursion_limit().value_within_limit(depth) {
        // Halt compilation because it is important that overflows never be masked.
        tcx.dcx().emit_fatal(InherentProjectionNormalizationOverflow {
            span: cause.span,
            ty: alias_ty.to_string(),
        });
    }

    let args = compute_inherent_assoc_ty_args(
        selcx,
        param_env,
        alias_ty,
        cause.clone(),
        depth,
        obligations,
    );

    // Register the obligations arising from the impl and from the associated type itself.
    let predicates = tcx.predicates_of(alias_ty.def_id).instantiate(tcx, args);
    for (predicate, span) in predicates {
        let predicate = normalize_with_depth_to(
            selcx,
            param_env,
            cause.clone(),
            depth + 1,
            predicate,
            obligations,
        );

        let nested_cause = ObligationCause::new(
            cause.span,
            cause.body_id,
            // FIXME(inherent_associated_types): Since we can't pass along the self type to the
            // cause code, inherent projections will be printed with identity instantiation in
            // diagnostics which is not ideal.
            // Consider creating separate cause codes for this specific situation.
            if span.is_dummy() {
                rustc_trait_selection::traits::ItemObligation(alias_ty.def_id)
            } else {
                rustc_trait_selection::traits::BindingObligation(alias_ty.def_id, span)
            },
        );

        obligations.push(Obligation::with_depth(
            tcx,
            nested_cause,
            depth + 1,
            param_env,
            predicate,
        ));
    }

    let ty = tcx.type_of(alias_ty.def_id).instantiate(tcx, args);

    let mut ty = selcx.infcx.resolve_vars_if_possible(ty);
    if ty.has_aliases() {
        ty = normalize_with_depth_to(selcx, param_env, cause.clone(), depth + 1, ty, obligations);
    }

    ty
}
*/

/*
pub fn compute_inherent_assoc_ty_args<'a, 'b, 'tcx>(
    selcx: &'a mut SelectionContext<'b, 'tcx>,
    param_env: ty::ParamEnv<'tcx>,
    alias_ty: ty::AliasTy<'tcx>,
    cause: ObligationCause<'tcx>,
    depth: usize,
    obligations: &mut Vec<PredicateObligation<'tcx>>,
) -> ty::GenericArgsRef<'tcx> {
    let tcx = selcx.tcx();

    let impl_def_id = tcx.parent(alias_ty.def_id);
    let impl_args = selcx.infcx.fresh_args_for_item(cause.span, impl_def_id);

    let mut impl_ty = tcx.type_of(impl_def_id).instantiate(tcx, impl_args);
    if !selcx.infcx.next_trait_solver() {
        impl_ty = normalize_with_depth_to(
            selcx,
            param_env,
            cause.clone(),
            depth + 1,
            impl_ty,
            obligations,
        );
    }

    // Infer the generic parameters of the impl by unifying the
    // impl type with the self type of the projection.
    let mut self_ty = alias_ty.self_ty();
    if !selcx.infcx.next_trait_solver() {
        self_ty = normalize_with_depth_to(
            selcx,
            param_env,
            cause.clone(),
            depth + 1,
            self_ty,
            obligations,
        );
    }

    match selcx.infcx.at(&cause, param_env).eq(DefineOpaqueTypes::Yes, impl_ty, self_ty) {
        Ok(mut ok) => obligations.append(&mut ok.obligations),
        Err(_) => {
            tcx.dcx().span_bug(
                cause.span,
                format!("{self_ty:?} was equal to {impl_ty:?} during selection but now it is not"),
            );
        }
    }

    alias_ty.rebase_inherent_args_onto_impl(impl_args, tcx)
}
*/

pub enum Projected<'tcx> {
    Progress(Progress<'tcx>),
    NoProgress(ty::Term<'tcx>),
}

pub struct Progress<'tcx> {
    term: ty::Term<'tcx>,
    obligations: Vec<PredicateObligation<'tcx>>,
}

impl<'tcx> Progress<'tcx> {
    fn error(tcx: TyCtxt<'tcx>, guar: ErrorGuaranteed) -> Self {
        Progress { term: Ty::new_error(tcx, guar).into(), obligations: vec![] }
    }

    fn with_addl_obligations(mut self, mut obligations: Vec<PredicateObligation<'tcx>>) -> Self {
        self.obligations.append(&mut obligations);
        self
    }
}

/// Computes the result of a projection type (if we can).
///
/// IMPORTANT:
/// - `obligation` must be fully normalized
//#[instrument(level = "info", skip(selcx))]
pub fn project<'cx, 'tcx>(
    selcx: &mut SelectionContext<'cx, 'tcx>,
    obligation: &ProjectionTyObligation<'tcx>,
) -> ProjectionCandidateSet<'tcx> {
    /*
    if !selcx.tcx().recursion_limit().value_within_limit(obligation.recursion_depth) {
        // This should really be an immediate error, but some existing code
        // relies on being able to recover from this.
        return Err(ProjectionError::TraitSelectionError(SelectionError::Overflow(
            OverflowError::Canonical,
        )));
    }

    if let Err(guar) = obligation.predicate.error_reported() {
        return Ok(Projected::Progress(Progress::error(selcx.tcx(), guar)));
    }
    */

    let mut candidates = ProjectionCandidateSet::None;

    // Make sure that the following procedures are kept in order. ParamEnv
    // needs to be first because it has highest priority, and Select checks
    // the return value of push_candidate which assumes it's ran at last.
    assemble_candidates_from_param_env(selcx, obligation, &mut candidates);

    assemble_candidates_from_trait_def(selcx, obligation, &mut candidates);

    assemble_candidates_from_object_ty(selcx, obligation, &mut candidates);

    if let ProjectionCandidateSet::Single(ProjectionCandidate::Object(_)) = candidates {
        // Avoid normalization cycle from selection (see
        // `assemble_candidates_from_object_ty`).
        // FIXME(lazy_normalization): Lazy normalization should save us from
        // having to special case this.
    } else {
        assemble_candidates_from_impls(selcx, obligation, &mut candidates);
    };

    candidates

    /*
    match candidates {
        ProjectionCandidateSet::Single(candidate) => {
            Ok(Projected::Progress(confirm_candidate(selcx, obligation, candidate)))
        }
        ProjectionCandidateSet::None => {
            let tcx = selcx.tcx();
            let term = match tcx.def_kind(obligation.predicate.def_id) {
                DefKind::AssocTy => {
                    Ty::new_projection(tcx, obligation.predicate.def_id, obligation.predicate.args)
                        .into()
                }
                DefKind::AssocConst => ty::Const::new_unevaluated(
                    tcx,
                    ty::UnevaluatedConst::new(
                        obligation.predicate.def_id,
                        obligation.predicate.args,
                    ),
                    tcx.type_of(obligation.predicate.def_id)
                        .instantiate(tcx, obligation.predicate.args),
                )
                .into(),
                kind => {
                    bug!("unknown projection def-id: {}", kind.descr(obligation.predicate.def_id))
                }
            };

            Ok(Projected::NoProgress(term))
        }
        // Error occurred while trying to processing impls.
        ProjectionCandidateSet::Error(e) => Err(ProjectionError::TraitSelectionError(e)),
        // Inherent ambiguity that prevents us from even enumerating the
        // candidates.
        ProjectionCandidateSet::Ambiguous => Err(ProjectionError::TooManyCandidates),
    }
    */
}

/// The first thing we have to do is scan through the parameter
/// environment to see whether there are any projection predicates
/// there that can answer this question.
fn assemble_candidates_from_param_env<'cx, 'tcx>(
    selcx: &mut SelectionContext<'cx, 'tcx>,
    obligation: &ProjectionTyObligation<'tcx>,
    candidate_set: &mut ProjectionCandidateSet<'tcx>,
) {
    assemble_candidates_from_predicates(
        selcx,
        obligation,
        candidate_set,
        ProjectionCandidate::ParamEnv,
        obligation.param_env.caller_bounds().iter(),
        false,
    );
}

/// In the case of a nested projection like `<<A as Foo>::FooT as Bar>::BarT`, we may find
/// that the definition of `Foo` has some clues:
///
/// ```ignore (illustrative)
/// trait Foo {
///     type FooT : Bar<BarT=i32>
/// }
/// ```
///
/// Here, for example, we could conclude that the result is `i32`.
fn assemble_candidates_from_trait_def<'cx, 'tcx>(
    selcx: &mut SelectionContext<'cx, 'tcx>,
    obligation: &ProjectionTyObligation<'tcx>,
    candidate_set: &mut ProjectionCandidateSet<'tcx>,
) {
    //debug!("assemble_candidates_from_trait_def(..)");
    let mut ambiguous = false;
    selcx.for_each_item_bound(
        obligation.predicate.self_ty(),
        |selcx, clause, _| {
            let Some(clause) = clause.as_projection_clause() else {
                return ControlFlow::Continue(());
            };
            if clause.projection_def_id() != obligation.predicate.def_id {
                return ControlFlow::Continue(());
            }

            let is_match =
                selcx.infcx.probe(|_| selcx.match_projection_projections(obligation, clause, true));

            match is_match {
                ProjectionMatchesProjection::Yes => {
                    candidate_set.push_candidate(ProjectionCandidate::TraitDef(clause));

                    if !obligation.predicate.has_non_region_infer() {
                        // HACK: Pick the first trait def candidate for a fully
                        // inferred predicate. This is to allow duplicates that
                        // differ only in normalization.
                        return ControlFlow::Break(());
                    }
                }
                ProjectionMatchesProjection::Ambiguous => {
                    candidate_set.mark_ambiguous();
                }
                ProjectionMatchesProjection::No => {}
            }

            ControlFlow::Continue(())
        },
        // `ProjectionCandidateSet` is borrowed in the above closure,
        // so just mark ambiguous outside of the closure.
        || ambiguous = true,
    );

    if ambiguous {
        candidate_set.mark_ambiguous();
    }
}

/// In the case of a trait object like
/// `<dyn Iterator<Item = ()> as Iterator>::Item` we can use the existential
/// predicate in the trait object.
///
/// We don't go through the select candidate for these bounds to avoid cycles:
/// In the above case, `dyn Iterator<Item = ()>: Iterator` would create a
/// nested obligation of `<dyn Iterator<Item = ()> as Iterator>::Item: Sized`,
/// this then has to be normalized without having to prove
/// `dyn Iterator<Item = ()>: Iterator` again.
fn assemble_candidates_from_object_ty<'cx, 'tcx>(
    selcx: &mut SelectionContext<'cx, 'tcx>,
    obligation: &ProjectionTyObligation<'tcx>,
    candidate_set: &mut ProjectionCandidateSet<'tcx>,
) {
    //debug!("assemble_candidates_from_object_ty(..)");

    let tcx = selcx.tcx();

    if !tcx.trait_def(obligation.predicate.trait_def_id(tcx)).implement_via_object {
        return;
    }

    let self_ty = obligation.predicate.self_ty();
    let object_ty = selcx.infcx.shallow_resolve(self_ty);
    let data = match object_ty.kind() {
        ty::Dynamic(data, ..) => data,
        ty::Infer(ty::TyVar(_)) => {
            // If the self-type is an inference variable, then it MAY wind up
            // being an object type, so induce an ambiguity.
            candidate_set.mark_ambiguous();
            return;
        }
        _ => return,
    };
    let env_predicates = data
        .projection_bounds()
        .filter(|bound| bound.item_def_id() == obligation.predicate.def_id)
        .map(|p| p.with_self_ty(tcx, object_ty).to_predicate(tcx));

    assemble_candidates_from_predicates(
        selcx,
        obligation,
        candidate_set,
        ProjectionCandidate::Object,
        env_predicates,
        false,
    );
}

//#[instrument(
//    level = "debug",
//    skip(selcx, candidate_set, ctor, env_predicates, potentially_unnormalized_candidates)
//)]
fn assemble_candidates_from_predicates<'cx, 'tcx>(
    selcx: &mut SelectionContext<'cx, 'tcx>,
    obligation: &ProjectionTyObligation<'tcx>,
    candidate_set: &mut ProjectionCandidateSet<'tcx>,
    ctor: fn(ty::PolyProjectionPredicate<'tcx>) -> ProjectionCandidate<'tcx>,
    env_predicates: impl Iterator<Item = ty::Clause<'tcx>>,
    potentially_unnormalized_candidates: bool,
) {
    let infcx = selcx.infcx;
    for predicate in env_predicates {
        let bound_predicate = predicate.kind();
        if let ty::ClauseKind::Projection(data) = predicate.kind().skip_binder() {
            let data = bound_predicate.rebind(data);
            if data.projection_def_id() != obligation.predicate.def_id {
                continue;
            }

            let is_match = infcx.probe(|_| {
                selcx.match_projection_projections(
                    obligation,
                    data,
                    potentially_unnormalized_candidates,
                )
            });

            match is_match {
                ProjectionMatchesProjection::Yes => {
                    candidate_set.push_candidate(ctor(data));

                    if potentially_unnormalized_candidates
                        && !obligation.predicate.has_non_region_infer()
                    {
                        // HACK: Pick the first trait def candidate for a fully
                        // inferred predicate. This is to allow duplicates that
                        // differ only in normalization.
                        return;
                    }
                }
                ProjectionMatchesProjection::Ambiguous => {
                    candidate_set.mark_ambiguous();
                }
                ProjectionMatchesProjection::No => {}
            }
        }
    }
}

//#[instrument(level = "debug", skip(selcx, obligation, candidate_set))]
fn assemble_candidates_from_impls<'cx, 'tcx>(
    selcx: &mut SelectionContext<'cx, 'tcx>,
    obligation: &ProjectionTyObligation<'tcx>,
    candidate_set: &mut ProjectionCandidateSet<'tcx>,
) {
    // If we are resolving `<T as TraitRef<...>>::Item == Type`,
    // start out by selecting the predicate `T as TraitRef<...>`:
    let trait_ref = obligation.predicate.trait_ref(selcx.tcx());
    let trait_obligation = obligation.with(selcx.tcx(), trait_ref);
    let _ = selcx.infcx.commit_if_ok(|_| {
        let impl_source = match selcx.select(&trait_obligation) {
            Ok(Some(impl_source)) => impl_source,
            Ok(None) => {
                candidate_set.mark_ambiguous();
                return Err(());
            }
            Err(e) => {
                //debug!(error = ?e, "selection error");
                candidate_set.mark_error(e);
                return Err(());
            }
        };

        let eligible = match &impl_source {
            ImplSource::UserDefined(impl_data) => {
                true
            /*
                // We have to be careful when projecting out of an
                // impl because of specialization. If we are not in
                // codegen (i.e., projection mode is not "any"), and the
                // impl's type is declared as default, then we disable
                // projection (even if the trait ref is fully
                // monomorphic). In the case where trait ref is not
                // fully monomorphic (i.e., includes type parameters),
                // this is because those type parameters may
                // ultimately be bound to types from other crates that
                // may have specialized impls we can't see. In the
                // case where the trait ref IS fully monomorphic, this
                // is a policy decision that we made in the RFC in
                // order to preserve flexibility for the crate that
                // defined the specializable impl to specialize later
                // for existing types.
                //
                // In either case, we handle this by not adding a
                // candidate for an impl if it contains a `default`
                // type.
                //
                // NOTE: This should be kept in sync with the similar code in
                // `rustc_ty_utils::instance::resolve_associated_item()`.
                let node_item =
                    specialization_graph::assoc_def(selcx.tcx(), impl_data.impl_def_id, obligation.predicate.def_id)
                        .map_err(|ErrorGuaranteed { .. }| ())?;

                if node_item.is_final() {
                    // Non-specializable items are always projectable.
                    true
                } else {
                    // Only reveal a specializable default if we're past type-checking
                    // and the obligation is monomorphic, otherwise passes such as
                    // transmute checking and polymorphic MIR optimizations could
                    // get a result which isn't correct for all monomorphizations.
                    if obligation.param_env.reveal() == Reveal::All {
                        // NOTE(eddyb) inference variables can resolve to parameters, so
                        // assume `poly_trait_ref` isn't monomorphic, if it contains any.
                        let poly_trait_ref = selcx.infcx.resolve_vars_if_possible(trait_ref);
                        !poly_trait_ref.still_further_specializable()
                    } else {
                        //debug!(
                        //    assoc_ty = ?selcx.tcx().def_path_str(node_item.item.def_id),
                        //    ?obligation.predicate,
                        //    "assemble_candidates_from_impls: not eligible due to default",
                        //);
                        false
                    }
                }
                */
            }
            ImplSource::Builtin(BuiltinImplSource::Misc, _) => {
                // While a builtin impl may be known to exist, the associated type may not yet
                // be known. Any type with multiple potential associated types is therefore
                // not eligible.
                let self_ty = selcx.infcx.shallow_resolve(obligation.predicate.self_ty());

                let lang_items = selcx.tcx().lang_items();
                if [
                    lang_items.coroutine_trait(),
                    lang_items.future_trait(),
                    lang_items.iterator_trait(),
                    lang_items.async_iterator_trait(),
                    lang_items.fn_trait(),
                    lang_items.fn_mut_trait(),
                    lang_items.fn_once_trait(),
                    lang_items.async_fn_trait(),
                    lang_items.async_fn_mut_trait(),
                    lang_items.async_fn_once_trait(),
                ].contains(&Some(trait_ref.def_id))
                {
                    true
                } else if lang_items.async_fn_kind_helper() == Some(trait_ref.def_id) {
                    // FIXME(async_closures): Validity constraints here could be cleaned up.
                    if obligation.predicate.args.type_at(0).is_ty_var()
                        || obligation.predicate.args.type_at(4).is_ty_var()
                        || obligation.predicate.args.type_at(5).is_ty_var()
                    {
                        candidate_set.mark_ambiguous();
                        true
                    } else {
                        obligation.predicate.args.type_at(0).to_opt_closure_kind().is_some()
                        && obligation.predicate.args.type_at(1).to_opt_closure_kind().is_some()
                    }
                } else if lang_items.discriminant_kind_trait() == Some(trait_ref.def_id) {
                    match self_ty.kind() {
                        ty::Bool
                        | ty::Char
                        | ty::Int(_)
                        | ty::Uint(_)
                        | ty::Float(_)
                        | ty::Adt(..)
                        | ty::Foreign(_)
                        | ty::Str
                        | ty::Array(..)
                        | ty::Pat(..)
                        | ty::Slice(_)
                        | ty::RawPtr(..)
                        | ty::Ref(..)
                        | ty::FnDef(..)
                        | ty::FnPtr(..)
                        | ty::Dynamic(..)
                        | ty::Closure(..)
                        | ty::CoroutineClosure(..)
                        | ty::Coroutine(..)
                        | ty::CoroutineWitness(..)
                        | ty::Never
                        | ty::Tuple(..)
                        // Integers and floats always have `u8` as their discriminant.
                        | ty::Infer(ty::InferTy::IntVar(_) | ty::InferTy::FloatVar(..)) => true,

                        // type parameters, opaques, and unnormalized projections don't have
                        // a known discriminant and may need to be normalized further or rely
                        // on param env for discriminant projections
                        ty::Param(_)
                        | ty::Alias(..)
                        | ty::Bound(..)
                        | ty::Placeholder(..)
                        | ty::Infer(..)
                        | ty::Error(_) => false,
                    }
                } else if lang_items.async_destruct_trait() == Some(trait_ref.def_id) {
                    match self_ty.kind() {
                        ty::Bool
                        | ty::Char
                        | ty::Int(_)
                        | ty::Uint(_)
                        | ty::Float(_)
                        | ty::Adt(..)
                        | ty::Str
                        | ty::Array(..)
                        | ty::Slice(_)
                        | ty::RawPtr(..)
                        | ty::Ref(..)
                        | ty::FnDef(..)
                        | ty::FnPtr(..)
                        | ty::Dynamic(..)
                        | ty::Closure(..)
                        | ty::CoroutineClosure(..)
                        | ty::Coroutine(..)
                        | ty::CoroutineWitness(..)
                        | ty::Pat(..)
                        | ty::Never
                        | ty::Tuple(..)
                        | ty::Infer(ty::InferTy::IntVar(_) | ty::InferTy::FloatVar(..)) => true,

                        // type parameters, opaques, and unnormalized projections don't have
                        // a known async destructor and may need to be normalized further or rely
                        // on param env for async destructor projections
                        ty::Param(_)
                        | ty::Foreign(_)
                        | ty::Alias(..)
                        | ty::Bound(..)
                        | ty::Placeholder(..)
                        | ty::Infer(_)
                        | ty::Error(_) => false,
                    }
                } else if lang_items.pointee_trait() == Some(trait_ref.def_id) {
                    let tail = selcx.tcx().struct_tail_with_normalize(
                        self_ty,
                        |ty| {
                            // We throw away any obligations we get from this, since we normalize
                            // and confirm these obligations once again during confirmation
                            normalize_with_depth(
                                selcx,
                                obligation.param_env,
                                obligation.cause.clone(),
                                obligation.recursion_depth + 1,
                                ty,
                            )
                            .value
                        },
                        || {},
                    );

                    match tail.kind() {
                        ty::Bool
                        | ty::Char
                        | ty::Int(_)
                        | ty::Uint(_)
                        | ty::Float(_)
                        | ty::Str
                        | ty::Array(..)
                        | ty::Pat(..)
                        | ty::Slice(_)
                        | ty::RawPtr(..)
                        | ty::Ref(..)
                        | ty::FnDef(..)
                        | ty::FnPtr(..)
                        | ty::Dynamic(..)
                        | ty::Closure(..)
                        | ty::CoroutineClosure(..)
                        | ty::Coroutine(..)
                        | ty::CoroutineWitness(..)
                        | ty::Never
                        // Extern types have unit metadata, according to RFC 2850
                        | ty::Foreign(_)
                        // If returned by `struct_tail_without_normalization` this is a unit struct
                        // without any fields, or not a struct, and therefore is Sized.
                        | ty::Adt(..)
                        // If returned by `struct_tail_without_normalization` this is the empty tuple.
                        | ty::Tuple(..)
                        // Integers and floats are always Sized, and so have unit type metadata.
                        | ty::Infer(ty::InferTy::IntVar(_) | ty::InferTy::FloatVar(..)) => true,

                        // We normalize from `Wrapper<Tail>::Metadata` to `Tail::Metadata` if able.
                        // Otherwise, type parameters, opaques, and unnormalized projections have
                        // unit metadata if they're known (e.g. by the param_env) to be sized.
                        ty::Param(_) | ty::Alias(..)
                            if self_ty != tail || selcx.infcx.predicate_must_hold_modulo_regions(
                                &obligation.with(
                                    selcx.tcx(),
                                    ty::TraitRef::from_lang_item(selcx.tcx(), LangItem::Sized, obligation.cause.span(),[self_ty]),
                                ),
                            ) =>
                        {
                            true
                        }

                        // FIXME(compiler-errors): are Bound and Placeholder types ever known sized?
                        ty::Param(_)
                        | ty::Alias(..)
                        | ty::Bound(..)
                        | ty::Placeholder(..)
                        | ty::Infer(..)
                        | ty::Error(_) => {
                            if tail.has_infer_types() {
                                candidate_set.mark_ambiguous();
                            }
                            false
                        }
                    }
                } else {
                    bug!("unexpected builtin trait with associated type: {trait_ref:?}")
                }
            }
            ImplSource::Param(..) => {
                // This case tell us nothing about the value of an
                // associated type. Consider:
                //
                // ```
                // trait SomeTrait { type Foo; }
                // fn foo<T:SomeTrait>(...) { }
                // ```
                //
                // If the user writes `<T as SomeTrait>::Foo`, then the `T
                // : SomeTrait` binding does not help us decide what the
                // type `Foo` is (at least, not more specifically than
                // what we already knew).
                //
                // But wait, you say! What about an example like this:
                //
                // ```
                // fn bar<T:SomeTrait<Foo=usize>>(...) { ... }
                // ```
                //
                // Doesn't the `T : SomeTrait<Foo=usize>` predicate help
                // resolve `T::Foo`? And of course it does, but in fact
                // that single predicate is desugared into two predicates
                // in the compiler: a trait predicate (`T : SomeTrait`) and a
                // projection. And the projection where clause is handled
                // in `assemble_candidates_from_param_env`.
                false
            }
            ImplSource::Builtin(BuiltinImplSource::Object { .. }, _) => {
                // Handled by the `Object` projection candidate. See
                // `assemble_candidates_from_object_ty` for an explanation of
                // why we special case object types.
                false
            }
            ImplSource::Builtin(BuiltinImplSource::TraitUpcasting { .. }, _)
            | ImplSource::Builtin(BuiltinImplSource::TupleUnsizing, _) => {
                // These traits have no associated types.
                selcx.tcx().dcx().span_delayed_bug(
                    obligation.cause.span,
                    format!("Cannot project an associated type from `{impl_source:?}`"),
                );
                return Err(())
            }
        };

        if eligible {
            if candidate_set.push_candidate(ProjectionCandidate::Select(impl_source)) {
                Ok(())
            } else {
                Err(())
            }
        } else {
            Err(())
        }
    });
}
