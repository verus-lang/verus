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
    pub(crate) fn reduce_projection(
        &mut self,
        projection: &Projection
    ) -> Result<Option<(ProjectionOrTyp, UnificationsToBeDone)>, VirErr>
    {
        // TODO we also need to check the param_env
        // Use this as a reference:
        // https://doc.rust-lang.org/1.79.0/nightly-rustc/rustc_trait_selection/traits/project/fn.project.html
        // (Unfortunately this function is private and difficult to untangle from its crate)

        let candidate = self.get_candidate(projection);
        match candidate {
            None => Ok(None),
            Some(Candidate::Impl(impl_def_id)) => {
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
                    unifications: ts.iter().cloned().zip(projection.args.iter().cloned()).collect(),
                };

                dbg!(&unifs);

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
                //let mut typs = vec![];
                /*
                dbg!(&impl_data.args);
                for arg in impl_data.args.iter() {
                    match arg.unpack() {
                        GenericArgKind::Type(ty) => {
                            let typ = mid_ty_to_vir_ghost(self.tcx, &self.bctx.ctxt.verus_items, 
                                self.bctx.fun_id, self.whole_span, &ty, Some(&unif_map), false).unwrap().0;
                            typs.push(typ);
                        }
                        _ => todo!()
                    }
                }
                let typs = Arc::new(typs);
                */
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

/*
    /// This normalizes the given projection as much as possible.
    ///
    /// If the projection depends on other projections, those are treated as opaque inference
    /// variables for the purposes of this operation. Caller is responsible for ordering
    /// and scheduleing the projection operations.

    // To do this, we use rustc's `normalize` function. In the ideal case, the type will
    // normalize to some totally concrete type. This is not always possible, of course.
    //
    // Since the output of `normalize` is, well, normalized, it doesn't contain any
    // non-normalized projections. Instead, it creates inference variables for these
    // projections and creates obligations that relate to the new inference variables to
    // the projections. Thus, we need to dig through the obligations to find all the information
    // we need, and if rustc creates any new inference variables, we'll need to reproduce
    // those in our unification engine.
    //
    // Here are some examples:
    //
    // Example 1.  The input projection might normalize to a concrete type:
    //    InferOk(
    //        value:  Bool
    //        obligations:  None
    //    )
    //
    // Examples 2. It might normalize to a projection that uses a generic type param.
    //    InferOk(
    //        value:  T::AssocType
    //        obligations:  None
    //    )
    // This is considered normalized, so we turn it into TypX::Projection
    //
    // Example 3. Rust might not be able to make any progress at all.
    // Suppose we're trying to normalize SomethingType<?0>::AssocType.
    // We might end up with:
    //
    //   InferOk(
    //       value: ?1
    //       obligations: [ ClauseKind::Projection( SomethingType<?0>::AssocType --> ?1 ) ]
    //   )
    //
    // where ?1 is a new type inference variable. In this case, we have to look through the
    // obligations to find the projection type.

    pub(crate) fn reduce_projection(&self, projection: &Projection) -> ProjectionOrTyp {
        let (args, infcx, unif_map) = self.vir_typs_to_middle_tys(self.whole_span, &projection.args);
        let projection_ty = AliasTy::new(self.tcx, projection.def_id, args);
        let ty = self.tcx.mk_ty_from_kind(rustc_middle::ty::Alias(AliasKind::Projection, projection_ty));

        let param_env = self.tcx.param_env(self.bctx.fun_id);
        let cause = ObligationCause::dummy();
        let at = infcx.at(&cause, param_env);
        let ty = &crate::rust_to_vir_base::clean_all_escaping_bound_vars(self.tcx, ty, self.bctx.fun_id);
        let norm = at.normalize(*ty);

        dbg!(ty);
        dbg!(&norm);

        let mut obligations = norm.obligations;

        let m_projection_or_ty = if let TyKind::Infer(t) = norm.value.kind() {
            let InferTy::TyVar(tyvid) = t else { unreachable!() };
            if unif_map.contains_key(tyvid) {
                MiddleAliasOrTy::Ty(norm.value)
            } else {
                // Like in 'Example 3'
                MiddleAliasOrTy::Alias(
                    Self::get_projection_from_normalize_result(*tyvid, &mut obligations)
                )
            }
        } else {
            // Like in 'Example 1 or 2'
            MiddleAliasOrTy::Ty(norm.value)
        };

        dbg!(&m_projection_or_ty);
        if obligations.len() != 0 {
            todo!();
        }

        match m_projection_or_ty {
            MiddleAliasOrTy::Ty(ty) => {
                let typ = mid_ty_to_vir_ghost(self.tcx, &self.bctx.ctxt.verus_items, 
                    self.bctx.fun_id, self.whole_span, &ty, Some(&unif_map), false).unwrap().0;
                ProjectionOrTyp::Typ(typ)
            }
            MiddleAliasOrTy::Alias(projection) => {
                let mut typs = vec![];
                for arg in projection.args.iter() {
                    match arg.unpack() {
                        GenericArgKind::Type(ty) => {
                            let typ = mid_ty_to_vir_ghost(self.tcx, &self.bctx.ctxt.verus_items, 
                                self.bctx.fun_id, self.whole_span, &ty, Some(&unif_map), false).unwrap().0;
                            typs.push(typ);
                        }
                        _ => todo!()
                    }
                }
                ProjectionOrTyp::Projection(Projection { def_id: projection.def_id, args: Arc::new(typs) })
            }
        }


        //let selcx = rustc_trait_selection_verus_fork::traits::SelectionContext::new(

        //rustc_trait_selection_verus_fork::traits::project::project;
        //todo!();
        /*
        assert!(matches!(&**typ, TypX::Projection { .. }));

        use crate::rustc_trait_selection::traits::NormalizeExt;
        let (ty, infcx) = self.vir_ty_to_middle(self.whole_span, typ);

        let param_env = self.tcx.param_env(self.bctx.fun_id);
        let cause = rustc_infer::traits::ObligationCause::dummy();
        let at = infcx.at(&cause, param_env);
        let ty = &crate::rust_to_vir_base::clean_all_escaping_bound_vars(self.tcx, ty, self.bctx.fun_id);
        let norm = at.normalize(*ty); // TODO is normalize recursive?

        dbg!(&ty);
        dbg!(&norm.value);
        dbg!(&norm);
        let norm_typ = crate::rust_to_vir_base::mid_ty_to_vir(
            self.tcx,
            &self.bctx.ctxt.verus_items,
            self.bctx.fun_id,
            self.whole_span,
            &norm.value,
            false,
        ).unwrap();

        if !vir::ast_util::types_equal(typ, &norm_typ) {
            self.deferred_projection_obligations.push((typ.clone(), norm_typ.clone()));
        }

        norm_typ
        */
    }

    fn get_projection_from_normalize_result<'tcx>(
        tyvid: rustc_middle::ty::TyVid,
        obligations: &mut rustc_infer::traits::PredicateObligations<'tcx>)
        -> rustc_middle::ty::AliasTy<'tcx>
    {
        for i in 0 .. obligations.len() {
            let predicate = &obligations[i].predicate;
            if let PredicateKind::Clause(ClauseKind::Projection(projection_pred)) = predicate.kind().skip_binder() {
                if let TermKind::Ty(ty) = projection_pred.term.unpack() {
                    if let TyKind::Infer(infer_ty) = ty.kind() {
                        if *infer_ty == InferTy::TyVar(tyvid) {
                            let ma = projection_pred.projection_ty;
                            obligations.remove(i);
                            return ma;
                        }
                    }
                }
            }
        }
        panic!("get_projection_from_normalize_result failed");
    }
    */
}
