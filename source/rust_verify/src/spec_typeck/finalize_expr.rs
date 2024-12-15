use super::State;
use vir::ast::{Expr, VirErr, Stmt, Typ, TypX, ExprX, CallTarget, Typs};
use air::scope_map::ScopeMap;
use rustc_hir::def_id::DefId;

impl State<'_, '_> {
    pub fn finalize_expr(&mut self, expr: &Expr) -> Result<Expr, VirErr> {
        vir::ast_visitor::map_expr_visitor_env(expr, &mut ScopeMap::new(), self,
            &|state: &mut Self, _, e: &Expr| state.finalize_one_expr(e),
            &|_, _, s: &Stmt| Ok(vec![s.clone()]),
            &|state, t: &Typ| state.finalize_one_typ(t)
        )
    }

    fn finalize_one_typ(&mut self, t: &Typ) -> Result<Typ, VirErr> {
        Ok(match &**t {
            TypX::UnificationVar(_)  => self.get_finished_typ(t),
            | TypX::Projection { .. } => unreachable!(),
            _ => t.clone(),
        })
    }

    fn finalize_one_expr(&mut self, expr: &Expr) -> Result<Expr, VirErr> {
        match &expr.x {
            ExprX::Call(call_target, _args) => {
                match call_target {
                    CallTarget::Fun(_kind, fun, typs, _, _usage) => {
                        let def_id = crate::rust_to_vir_base::def_id_of_vir_path(&fun.path);
                        self.check_trait_obligations(&expr.span, def_id, typs);
                        Ok(expr.clone())
                    }
                    CallTarget::FnSpec(_) => Ok(expr.clone()),
                    _ => todo!(),
                }
            }
            _ => Ok(expr.clone())
        }
    }

    fn check_trait_obligations(&mut self, span: &vir::messages::Span, def_id: DefId, typs: &Typs) {
        let span = self.bctx.ctxt.spans.from_air_span(span, None).unwrap();

        //use crate::rustc_trait_selection::solve::InferCtxtEvalExt;
        use crate::rustc_infer::infer::TyCtxtInferExt;
        use crate::rustc_trait_selection::traits::TraitEngineExt;
        use crate::rustc_trait_selection::traits::error_reporting::TypeErrCtxtExt;

        let infcx = self.tcx.infer_ctxt().ignoring_regions().build();
        let mut fulfillment_cx = <dyn rustc_trait_selection::traits::TraitEngine<'_>>::new(&infcx);

        let args = self.finalized_vir_typs_to_generic_args(typs);
        let clauses = self.tcx.predicates_of(def_id).instantiate(self.tcx, args).predicates;
        for clause in clauses.into_iter() {
            let cause = rustc_trait_selection::traits::ObligationCause::new(
                span,
                self.bctx.fun_id.expect_local(),
                rustc_trait_selection::traits::ObligationCauseCode::ItemObligation(def_id),
            );
            let obligation = rustc_trait_selection::traits::Obligation::new(
                self.tcx,
                cause,
                self.tcx.param_env(self.bctx.fun_id),
                clause);
            fulfillment_cx.register_predicate_obligation(&infcx, obligation);
        }

        let mut errors = fulfillment_cx.select_where_possible(&infcx);
        errors.append(&mut fulfillment_cx.collect_remaining_errors(&infcx));

        if errors.len() > 0 {
            let err_ctxt = infcx.err_ctxt();
            err_ctxt.report_fulfillment_errors(errors);
        }
    }
}
