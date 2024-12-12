// Based off of rust's rustc_hir_typeck/src/method/probe.rs
// Some code (such as the high level approach, and some individual functions)
// are taken directly from it
// Ours is a bit simpler, we don't handle Deref traits for example
// but we still need to do complex trait lookups

use rustc_middle::ty;
use rustc_middle::ty::{Ty, TyCtxt};
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



pub(crate) struct ProbeContext<'tcx> {
    tcx: TyCtxt<'tcx>,
    span: Span,
    mode: Mode,
    method_name: Option<Ident>,

    local_def_id: LocalDefId,

    inherent_candidates: Vec<Candidate<'tcx>>,
    extension_candidates: Vec<Candidate<'tcx>>,
    impl_dups: HashSet<DefId>,

    allow_similar_names: bool,

    private_candidate: Option<(DefKind, DefId)>,
    static_candidates: RefCell<Vec<CandidateSource>>,
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
}
