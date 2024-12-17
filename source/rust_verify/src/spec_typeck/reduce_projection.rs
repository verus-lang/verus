use vir::ast::{Typ, TypX, VirErr, Typs};
use super::unifier::{Projection, ProjectionOrTyp};
use super::State;
use std::sync::Arc;
use crate::rust_to_vir_base::mid_ty_to_vir;
use crate::rust_to_vir_base::mid_ty_to_vir_ghost;
use rustc_hir::def_id::DefId;
use rustc_middle::ty::{GenericArgKind, AliasTy, AliasKind, TyKind, InferTy, PredicateKind, ClauseKind, TermKind, TraitPredicate, TraitRef, PredicatePolarity};
use rustc_infer::traits::ObligationCause;
use crate::rustc_trait_selection::traits::NormalizeExt;
use rustc_trait_selection::traits::TraitObligation;
use rustc_trait_selection::traits::{BuiltinImplSource, ImplSource};

#[derive(Clone, Debug)]
enum MiddleAliasOrTy<'tcx> {
    Alias(rustc_middle::ty::AliasTy<'tcx>),
    Ty(rustc_middle::ty::Ty<'tcx>),
}

#[derive(Clone, Debug)]
enum Candidate {
    Impl(DefId),
}

#[derive( Debug)]
pub struct UnificationsToBeDone {
    pub unifications: Vec<(Typ, Typ)>
}

impl State<'_, '_> {
    /// This normalizes the given projection as much as possible.
    ///
    /// If the projection depends on other projections, those are treated as opaque inference
    /// variables for the purposes of this operation.
    /// If a projection gets stuck, it can only get unstuck if any of the "dependencies"
    /// make progress.
    ///
    /// The caller is responsible for ordering and scheduling the projection
    /// reduction operations.
    ///
    /// This function can create new inference vars, but it does not perform any unification.
    /// Pending unifications are instead returned to the caller.

    pub(crate) fn reduce_projection_once(
        &mut self,
        projection: &Projection
    ) -> Result<Option<(ProjectionOrTyp, UnificationsToBeDone)>, VirErr> {
        // note: Rustc's "normalize" function does a lot of what we want and it's
        // easy to invoke. Therefore, I considered trying to just use that.
        // However, it does a lot of other complex
        // stuff, too, such as performing unification, so it's difficult to use
        // for our purposes while we have our own unification engine.

        // The actual function that is closed to what we want is `project`:
        // https://doc.rust-lang.org/1.79.0/nightly-rustc/rustc_trait_selection/traits/project/fn.project.html
        // Unfortunately, it's private. It's also kinda difficult to disentangle
        // from the significant crate that it's in (though I wonder if I should try harder)

        // TODO we also need to check the param_env
        // Use this as a reference:
        // (Unfortunately this function is private and difficult to untangle from its crate)

        let candidate = self.get_candidate(projection);
        match candidate {
            None => Ok(None),
            Some(Candidate::Impl(impl_def_id)) => {
                // Suppose we've selected the impl:
                //
                //    impl<Args...> Trait<TraitArgs...> for Self {
                //        type AssocTyp = ...;
                //    }
                //
                // We instantiate new inference vars for the Args.
                // We can then plug those in to get the assoc type.
                //
                // We also need to unify the trait args (Self, TraitArgs...) of this impl
                // with the trait args in the projection.

                // TODO add obligations that impl is satisfied

                let n_args = self.get_generic_defs(self.tcx.generics_of(impl_def_id)).len();
                let mut args = vec![];
                for _i in 0 .. n_args {
                    args.push(self.new_unknown_typ());
                }
                let args = Arc::new(args);

                let ts = self.impl_trait_ref_substitution(self.whole_span, impl_def_id, &args)?;

                assert!(ts.len() == projection.args.len());

                let unifs = UnificationsToBeDone {
                    unifications: projection.args.iter().cloned().zip(ts.iter().cloned()).collect(),
                };

                let assoc_id_on_impl = *self.tcx.impl_item_implementor_ids(impl_def_id).get(&projection.def_id).unwrap();

                let proj_or_ty = self.item_type_substitution_or_proj(
                    self.whole_span,
                    assoc_id_on_impl,
                    &args)?;

                Ok(Some((proj_or_ty, unifs)))
            }
        }
    }

    fn get_candidate(&self, projection: &Projection) -> Option<Candidate> {
        let assoc_ty_def_id = projection.def_id;
        let trait_def_id = self.tcx.trait_of_item(assoc_ty_def_id).unwrap();

        let (args, infcx, _unif_map) = self.vir_typs_to_middle_tys(self.whole_span, &projection.args);
        let mut selcx = rustc_trait_selection::traits::SelectionContext::new(&infcx);

        let trait_obligation = TraitObligation::new(
            self.tcx,
            ObligationCause::dummy(),
            self.tcx.param_env(self.bctx.fun_id),
            TraitPredicate {
                trait_ref: TraitRef::new(
                    self.tcx,
                    trait_def_id,
                    args,
                ),
                polarity: PredicatePolarity::Positive,
            },
        );

        dbg!(&trait_obligation);

        let impl_source = match selcx.select(&trait_obligation) {
            Ok(Some(impl_source)) => impl_source,
            Ok(None) => {
                return None;
                //candidate_set.mark_ambiguous();
                //return Err(());
            }
            Err(_e) => {
                todo!()
                //debug!(error = ?e, "selection error");
                //candidate_set.mark_error(e);
                //return Err(());
            }
        };

        match impl_source {
            ImplSource::UserDefined(impl_data) => {
                // note: this is more complicated when specialization is allowed
                Some(Candidate::Impl(impl_data.impl_def_id))
            }
            ImplSource::Builtin(..) => {
                todo!();
            }
            ImplSource::Param(..) => {
                None
            }
        }
    }
}
