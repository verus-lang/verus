// Based off of rust's rustc_hir_typeck/src/method/probe.rs
// Some code (such as the high level approach, and some individual functions)
// are taken directly from it
//
// Also see: https://rustc-dev-guide.rust-lang.org/method-lookup.html
//
// Ours is a bit simpler, we don't handle Deref traits for example
// but we still need to do complex trait lookups

use rustc_middle::ty;
use rustc_middle::ty::{Ty, TyCtxt, AssocItem};
use rustc_span::{sym, Span};
use rustc_hir::def::{DefKind, Namespace};
use rustc_hir::def_id::{LocalDefId, DefId};
use std::cell::RefCell;
use rustc_middle::ty::fast_reject::{simplify_type, TreatParams};
use rustc_span::{symbol::Ident};
use std::collections::HashSet;
use smallvec::SmallVec;
use std::cmp::max;
use rustc_span::edit_distance::edit_distance_with_substrings;
use rustc_span::Symbol;
use rustc_infer::traits::ObligationCause;
use rustc_middle::middle::stability;

pub(crate) struct ProbeContext<'tcx> {
    tcx: TyCtxt<'tcx>,
    span: Span,
    mode: Mode,
    method_name: Option<Ident>,

    local_def_id: LocalDefId,

    self_ty: Ty<'tcx>,

    inherent_candidates: Vec<Candidate<'tcx>>,
    extension_candidates: Vec<Candidate<'tcx>>,
    impl_dups: HashSet<DefId>,

    allow_similar_names: bool,

    private_candidate: Option<(DefKind, DefId)>,
    static_candidates: RefCell<Vec<CandidateSource>>,

    unsatisfied_predicates: RefCell<
        Vec<(ty::Predicate<'tcx>, Option<ty::Predicate<'tcx>>, Option<ObligationCause<'tcx>>)>,
    >,
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

#[derive(Debug, Clone)]
pub struct Pick<'tcx> {
    pub item: ty::AssocItem,
    pub kind: PickKind<'tcx>,
    pub import_ids: SmallVec<[LocalDefId; 1]>,

    // Indicates that the source expression should be autoderef'd N times
    // ```ignore (not-rust)
    // A = expr | *expr | **expr | ...
    // ```
    //pub autoderefs: usize,

    // Indicates that we want to add an autoref (and maybe also unsize it), or if the receiver is
    // `*mut T`, convert it to `*const T`.
    //pub autoref_or_ptr_adjustment: Option<AutorefOrPtrAdjustment>,
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

pub enum MethodError<'tcx> {
    NoMatch(NoMatchData<'tcx>),
    Ambiguity(Vec<CandidateSource>),
    PrivateMatch(DefKind, DefId, Vec<DefId>),
    BadReturnType,
}

pub struct NoMatchData<'tcx> {
    pub static_candidates: Vec<CandidateSource>,
    pub unsatisfied_predicates: Vec<(ty::Predicate<'tcx>, Option<ty::Predicate<'tcx>>, Option<ObligationCause<'tcx>>)>,
    pub out_of_scope_traits: Vec<DefId>,
    pub similar_candidate: Option<AssocItem>,
    pub mode: Mode,
}

pub enum CandidateSource {
    Impl(DefId),
    Trait(DefId),
}

#[derive(Debug, Clone)]
pub(crate) struct Candidate<'tcx> {
    pub(crate) item: ty::AssocItem,
    pub(crate) kind: CandidateKind<'tcx>,
    pub(crate) import_ids: Vec<LocalDefId>,
}

#[derive(Debug, Clone)]
pub(crate) enum CandidateKind<'tcx> {
    InherentImplCandidate(DefId),
    ObjectCandidate(ty::PolyTraitRef<'tcx>),
    TraitCandidate(ty::PolyTraitRef<'tcx>),
    WhereClauseCandidate(ty::PolyTraitRef<'tcx>),
}

impl<'tcx> ProbeContext<'tcx> {
    fn push_candidate(&mut self, candidate: Candidate<'tcx>, is_inherent: bool) {
        let is_accessible = if let Some(name) = self.method_name {
            let item = candidate.item;
            let hir_id = self.tcx.local_def_id_to_hir_id(self.local_def_id);
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

    fn assemble_probe(&mut self, self_ty: &Ty<'tcx>) {
        match *self_ty.kind() {
            ty::Dynamic(data, ..)
              /*if let Some(p) = data.principal() =>*/
              if data.principal().is_some() =>
              {
                todo!()
                /*
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
                    self.fcx.instantiate_canonical(self.span, self_ty);

                self.assemble_inherent_candidates_from_object(generalized_self_ty);
                self.assemble_inherent_impl_candidates_for_type(p.def_id());
                if self.tcx.has_attr(p.def_id(), sym::rustc_has_incoherent_inherent_impls) {
                    self.assemble_inherent_candidates_for_incoherent_ty(raw_self_ty);
                }
                */
            }
            ty::Adt(def, _) => {
                let def_id = def.did();
                self.assemble_inherent_impl_candidates_for_type(def_id);
                if self.tcx.has_attr(def_id, sym::rustc_has_incoherent_inherent_impls) {
                    self.assemble_inherent_candidates_for_incoherent_ty(*self_ty);
                }
            }
            ty::Foreign(did) => {
                self.assemble_inherent_impl_candidates_for_type(did);
                if self.tcx.has_attr(did, sym::rustc_has_incoherent_inherent_impls) {
                    self.assemble_inherent_candidates_for_incoherent_ty(*self_ty);
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
            | ty::Tuple(..) => self.assemble_inherent_candidates_for_incoherent_ty(*self_ty),
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

        for item in self.impl_or_trait_item(impl_def_id) {
            if !self.has_applicable_self(&item) {
                // No receiver declared. Not a candidate.
                self.record_static_candidate(CandidateSource::Impl(impl_def_id));
                continue;
            }
            self.push_candidate(
                Candidate {
                    item,
                    kind: CandidateKind::InherentImplCandidate(impl_def_id),
                    import_ids: vec![],
                },
                true,
            );
        }
    }

    fn assemble_inherent_candidates_from_param(&mut self, _param_ty: ty::ParamTy) {
        todo!()
    }

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
                self.associated_value(def_id, name)
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
                    if let Some(lit) = n.lit() {
                        if name.as_str() == lit.symbol.as_str() {
                            return true;
                        }
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
                        if let Some(lit) = n.lit() {
                            if name.as_str() == lit.symbol.as_str() {
                                return true;
                            }
                        }
                    }
                } else if let Some(meta) = v.meta_item() {
                    if let Some(lit) = meta.name_value_literal() {
                        if name.as_str() == lit.symbol.as_str() {
                            // #[doc(alias = "foo")]
                            return true;
                        }
                    }
                }
            }
        }
        false
    }

    pub fn associated_value(&self, def_id: DefId, item_name: Ident) -> Option<ty::AssocItem> {
        self.tcx
            .associated_items(def_id)
            .find_by_name_and_namespace(self.tcx, item_name, Namespace::ValueNS, def_id)
            .copied()
    }

    ///////////////////////////////////////////////////////////////////////////
    // THE ACTUAL SEARCH

    fn pick(self) -> PickResult<'tcx> {
        assert!(self.method_name.is_some());

        if let Some(r) = self.pick_core() {
            return r;
        }

        return Err(MethodError::NoMatch(NoMatchData {
            static_candidates: vec![],
            unsatisfied_predicates: vec![],
            out_of_scope_traits: vec![],
            similar_candidate: None,
            mode: self.mode,
        }));

        /*

        let static_candidates = std::mem::take(self.static_candidates.get_mut());
        let private_candidate = self.private_candidate.take();
        let unsatisfied_predicates = std::mem::take(self.unsatisfied_predicates.get_mut());

        // things failed, so lets look at all traits, for diagnostic purposes now:
        self.reset();

        let span = self.span;
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
        */
    }

    fn pick_core(&self) -> Option<PickResult<'tcx>> {
        // Pick stable methods only first, and consider unstable candidates if not found.
        self.pick_all_method(Some(&mut vec![])).or_else(|| self.pick_all_method(None))
    }

    fn pick_all_method(
        &self,
        mut unstable_candidates: Option<&mut Vec<(Candidate<'tcx>, Symbol)>>,
    ) -> Option<PickResult<'tcx>> {
          /*let InferOk { value: self_ty, obligations: _ } = self
              .fcx
              .probe_instantiate_query_response(
                  self.span,
                  self.orig_steps_var_values,
                  &step.self_ty,
              )
              .unwrap_or_else(|_| {
                  panic!("{:?} was applicable but now isn't?", self_ty)
              });*/
          let self_ty = self.self_ty;
          self.pick_by_value_method(self_ty, unstable_candidates.as_deref_mut())
              /*.or_else(|| {
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
              })*/
    }

    fn pick_by_value_method(
        &self,
        self_ty: Ty<'tcx>,
        unstable_candidates: Option<&mut Vec<(Candidate<'tcx>, Symbol)>>,
    ) -> Option<PickResult<'tcx>> {
        /*if step.unsize {
            return None;
        }*/

        self.pick_method(self_ty, unstable_candidates).map(|r: PickResult| {
            r.map(|mut pick| {
                // Insert a `&*` or `&mut *` if this is a reference type:
                /*if let ty::Ref(_, _, mutbl) = *step.self_ty.value.value.kind() {
                    pick.autoderefs += 1;
                    pick.autoref_or_ptr_adjustment = Some(AutorefOrPtrAdjustment::Autoref {
                        mutbl,
                        unsize: pick.autoref_or_ptr_adjustment.is_some_and(|a| a.get_unsize()),
                    })
                }*/

                pick
            })
        })
    }

    fn pick_method(
        &self,
        self_ty: Ty<'tcx>,
        mut unstable_candidates: Option<&mut Vec<(Candidate<'tcx>, Symbol)>>,
    ) -> Option<PickResult<'tcx>> {

        let mut possibly_unsatisfied_predicates = Vec::new();

        for (kind, candidates) in
            &[("inherent", &self.inherent_candidates), ("extension", &self.extension_candidates)]
        {
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
