use std::convert::TryInto;
use std::sync::Arc;

use rustc_hir::{def::Res, Expr, ExprKind, QPath};
use vir::ast::{ExprX, FunX, HeaderExprX};

use crate::util::unsupported_err_span;
use crate::{
    rust_to_vir_base::def_id_to_vir_path, unsupported_err, unsupported_err_unless, util::err_span,
};

pub(crate) enum RevealHideResult {
    Expr(vir::ast::Expr),
    RevealItem(vir::ast::Fun),
}

pub(crate) fn handle_reveal_hide<'ctxt>(
    ctxt: &crate::context::Context<'ctxt>,
    expr: &Expr<'ctxt>,
    args_len: usize,
    args: &Vec<&Expr<'ctxt>>,
    tcx: rustc_middle::ty::TyCtxt<'ctxt>,
    mk_expr: Option<impl Fn(ExprX) -> Result<vir::ast::Expr, vir::ast::VirErr>>,
) -> Result<RevealHideResult, vir::ast::VirErr> {
    unsupported_err_unless!(args_len == 2, expr.span, "expected reveal", &args);
    let ExprKind::Block(block, None) = args[0].kind else {
        unsupported_err!(expr.span, "invalid reveal", &args);
    };
    if block.stmts.len() != 1 || !matches!(block.stmts[0].kind, rustc_hir::StmtKind::Item(_)) {
        unsupported_err!(expr.span, "invalid reveal", &args);
    }
    let Some(block_expr) = block.expr.as_ref() else {
        unsupported_err!(expr.span, "invalid reveal", &args);
    };
    let is_broadcast_use = {
        let expr_attrs = ctxt.tcx.hir().attrs(block_expr.hir_id);
        let expr_vattrs = ctxt.get_verifier_attrs(expr_attrs)?;
        expr_vattrs.broadcast_use_reveal
    };
    let ExprKind::Path(QPath::Resolved(None, path)) = &block_expr.kind else {
        unsupported_err!(expr.span, "invalid reveal", &args);
    };
    let id = {
        let Some(path_map) =
            &*crate::verifier::BODY_HIR_ID_TO_REVEAL_PATH_RES.read().expect("lock failed")
        else {
            unsupported_err!(expr.span, "invalid reveal", &args);
        };
        let (ty_res, res) = &path_map[&path.res.def_id()];
        if let Some(ty_res) = ty_res {
            match res {
                crate::hir_hide_reveal_rewrite::ResOrSymbol::Res(res) => {
                    // `res` has the def_id of the trait function
                    // `ty_res` has the def_id of the type, or is a primitive type
                    // we need to find the impl that contains the non-blanket
                    // implementation of the function for the type
                    let trait_ = tcx.trait_of_item(res.def_id()).expect("trait of function");
                    let ty_ = match ty_res {
                        Res::Def(_, def_id) => tcx.type_of(def_id).skip_binder(),
                        Res::PrimTy(prim_ty) => crate::util::hir_prim_ty_to_mir_ty(tcx, prim_ty),
                        _ => {
                            unsupported_err!(expr.span, "type {:?} not supported in reveal", ty_res)
                        }
                    };
                    *tcx.non_blanket_impls_for_ty(trait_, ty_)
                        .find_map(|impl_| {
                            let implementor_ids = &tcx.impl_item_implementor_ids(impl_);
                            implementor_ids.get(&res.def_id())
                        })
                        .expect("non-blanked impl for ty with def")
                }
                crate::hir_hide_reveal_rewrite::ResOrSymbol::Symbol(sym) => {
                    let matching_impls: Vec<_> = tcx
                        .inherent_impls(ty_res.def_id())
                        .iter()
                        .filter_map(|impl_def_id| {
                            let ident = rustc_span::symbol::Ident::from_str(sym.as_str());
                            let found =
                                tcx.associated_items(impl_def_id).find_by_name_and_namespace(
                                    tcx,
                                    ident,
                                    rustc_hir::def::Namespace::ValueNS,
                                    *impl_def_id,
                                );
                            found.map(|f| f.def_id)
                        })
                        .collect();
                    if matching_impls.len() > 1 {
                        return err_span(
                            expr.span,
                            format!(
                                "{} is ambiguous, use the universal function call syntax to disambiguate (`<Type as Trait>::function`)",
                                sym.as_str()
                            ),
                        );
                    } else if matching_impls.len() == 0 {
                        return err_span(expr.span, format!("`{}` not found", sym.as_str()));
                    } else {
                        matching_impls.into_iter().next().unwrap()
                    }
                }
            }
        } else {
            match res {
                crate::hir_hide_reveal_rewrite::ResOrSymbol::Res(res) => res.def_id(),
                crate::hir_hide_reveal_rewrite::ResOrSymbol::Symbol(_) => {
                    unsupported_err!(expr.span, "unexpected reveal", &args);
                }
            }
        }
    };
    let path = def_id_to_vir_path(ctxt.tcx, &ctxt.verus_items, id);

    let ExprKind::Lit(fuel_lit) = args[1].kind else {
        unsupported_err!(expr.span, "invalid reveal", &args);
    };
    let span = &ctxt.spans.to_air_span(expr.span);
    let rustc_ast::LitKind::Int(fuel_val, rustc_ast::LitIntType::Unsuffixed) = fuel_lit.node else {
        return Err(vir::messages::error(span, "Fuel must be a u32 value"));
    };
    let fuel_n: u32 =
        fuel_val.try_into().map_err(|_| vir::messages::error(span, "Fuel must be a u32 value"))?;

    let fun = Arc::new(FunX { path });
    if let Some(mk_expr) = mk_expr {
        (if fuel_n == 0 {
            let header = Arc::new(HeaderExprX::Hide(fun));
            mk_expr(ExprX::Header(header))
        } else {
            mk_expr(ExprX::Fuel(fun, fuel_n, is_broadcast_use))
        })
        .map(RevealHideResult::Expr)
    } else {
        assert_eq!(fuel_n, 1);

        Ok(RevealHideResult::RevealItem(fun))
    }
}
