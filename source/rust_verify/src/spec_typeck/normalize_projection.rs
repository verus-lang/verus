use vir::ast::{Typ, TypX, VirErr, Typs};
use super::unifier::{Alias, AliasOrTyp};
use super::State;
use std::sync::Arc;
use crate::rust_to_vir_base::mid_ty_to_vir;
use crate::rust_to_vir_base::mid_ty_to_vir_ghost;
use rustc_middle::ty::{GenericArgKind, AliasTy, AliasKind, TyKind, InferTy, PredicateKind, ClauseKind, TermKind};
use rustc_infer::traits::ObligationCause;
use crate::rustc_trait_selection::traits::NormalizeExt;

#[derive(Clone, Debug)]
enum MiddleAliasOrTy<'tcx> {
    Alias(rustc_middle::ty::AliasTy<'tcx>),
    Ty(rustc_middle::ty::Ty<'tcx>),
}

impl State<'_, '_> {
    pub(crate) fn reduce_alias(&self, alias: &Alias) -> AliasOrTyp {
        let (args, infcx, unif_map) = self.vir_typs_to_middle_tys(self.whole_span, &alias.args);
        let alias_ty = AliasTy::new(self.tcx, alias.def_id, args);
        let ty = self.tcx.mk_ty_from_kind(rustc_middle::ty::Alias(AliasKind::Projection, alias_ty));

        let param_env = self.tcx.param_env(self.bctx.fun_id);
        let cause = ObligationCause::dummy();
        let at = infcx.at(&cause, param_env);
        let ty = &crate::rust_to_vir_base::clean_all_escaping_bound_vars(self.tcx, ty, self.bctx.fun_id);
        let norm = at.normalize(*ty);

        dbg!(ty);
        dbg!(&norm);

        let mut obligations = norm.obligations;

        let m_alias_or_ty = if let TyKind::Infer(t) = norm.value.kind() {
            let InferTy::TyVar(tyvid) = t else { unreachable!() };
            if unif_map.contains_key(tyvid) {
                MiddleAliasOrTy::Ty(norm.value)
            } else {
                MiddleAliasOrTy::Alias(
                    Self::get_alias_from_normalize_result(*tyvid, &mut obligations)
                )
            }
        } else {
            MiddleAliasOrTy::Ty(norm.value)
        };

        dbg!(&m_alias_or_ty);
        assert!(obligations.len() == 0);

        match m_alias_or_ty {
            MiddleAliasOrTy::Ty(ty) => {
                let typ = mid_ty_to_vir_ghost(self.tcx, &self.bctx.ctxt.verus_items, 
                    self.bctx.fun_id, self.whole_span, &ty, Some(&unif_map), false).unwrap().0;
                AliasOrTyp::Typ(typ)
            }
            MiddleAliasOrTy::Alias(alias) => {
                let mut typs = vec![];
                for arg in alias.args.iter() {
                    match arg.unpack() {
                        GenericArgKind::Type(ty) => {
                            let typ = mid_ty_to_vir_ghost(self.tcx, &self.bctx.ctxt.verus_items, 
                                self.bctx.fun_id, self.whole_span, &ty, Some(&unif_map), false).unwrap().0;
                            typs.push(typ);
                        }
                        _ => todo!()
                    }
                }
                AliasOrTyp::Alias(Alias { def_id: alias.def_id, args: Arc::new(typs) })
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

    fn get_alias_from_normalize_result<'tcx>(
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
        panic!("get_alias_from_normalize_result failed");
    }
}
