use crate::attributes::Attr;
use crate::context::Context;
use crate::internal_err;
use crate::rust_to_vir_func::extract_desugared_async_body;
use crate::util::err_span;
use crate::verus_items::{ExprItem, SpecItem, VerusItem};
use rustc_hir::def::Res;
use rustc_hir::{Block, Body, Expr, ExprKind, Node, QPath, Stmt, StmtKind};
use rustc_middle::ty::TyCtxt;
use vir::ast::*;

/// Bits of the header that can be computed pre-typechecking.
/// We necessarily can't compute any `vir::ast::Expr` in the PreHeader.
///
/// Use `sanity_check_preheader` after the final Header has been computed
/// to ensure consistency.
#[derive(Debug, Clone)]
pub struct PreHeader {
    pub no_method_body: bool,
    pub returns: bool,
    pub default_ensures: bool,
    pub open_visibility_qualifier: Option<Visibility>,
    pub unwrap_parameters: Vec<UnwrapParameter>,
    pub ensure_id: Option<VarIdent>,
}

pub(crate) fn empty_preheader<'tcx>() -> PreHeader {
    PreHeader {
        no_method_body: false,
        returns: false,
        open_visibility_qualifier: None,
        unwrap_parameters: vec![],
        ensure_id: None,
        default_ensures: false,
    }
}

pub(crate) fn get_preheader<'tcx>(
    ctxt: &Context<'tcx>,
    vir_params: &[vir::ast::Param],
    body: &Body<'tcx>,
    is_async: bool,
) -> Result<PreHeader, VirErr> {
    let body_expr = if is_async { extract_desugared_async_body(ctxt, body)? } else { &body.value };
    let mut pre_header = empty_preheader();
    walk_expr(ctxt, vir_params, body.params, body_expr, &mut pre_header)?;
    Ok(pre_header)
}

fn walk_expr<'tcx>(
    ctxt: &Context<'tcx>,
    vir_params: &[vir::ast::Param],
    hir_params: &[rustc_hir::Param<'tcx>],
    expr: &Expr,
    pre_header: &mut PreHeader,
) -> Result<(), VirErr> {
    match expr.kind {
        ExprKind::Block(block, _) => {
            let mut done = false;
            let mut iter = block.stmts.iter();
            while let Some(stmt) = iter.next() {
                let attrs =
                    crate::attributes::parse_attrs_opt(ctxt.tcx.hir_attrs(stmt.hir_id), None);
                if let [Attr::UnwrapParameter] = attrs[..] {
                    if let Some(stmt2) = iter.next() {
                        let u =
                            unwrap_param_extract_idents(ctxt.tcx, vir_params, hir_params, stmt2)?;
                        pre_header.unwrap_parameters.push(u);
                    } else {
                        internal_err!(stmt.span, "ill-formed unwrap_parameter header");
                    }
                } else {
                    if check_stmt_for_header(ctxt, stmt, pre_header)? {
                        continue;
                    } else {
                        // done with header
                        done = true;
                        break;
                    }
                }
            }
            if !done && let Some(e) = block.expr {
                check_expr_for_header(ctxt, e, pre_header)?;
            }
        }
        _ => {}
    }
    Ok(())
}

fn unwrap_param_extract_idents<'tcx>(
    tcx: TyCtxt<'tcx>,
    vir_params: &[vir::ast::Param],
    hir_params: &[rustc_hir::Param<'tcx>],
    stmt: &Stmt,
) -> Result<UnwrapParameter, VirErr> {
    let StmtKind::Semi(e) = stmt.kind else {
        internal_err!(stmt.span, "ill-formed unwrap_parameter header");
    };
    let ExprKind::Block(Block { stmts: [], expr: Some(e), .. }, _) = e.kind else {
        internal_err!(stmt.span, "ill-formed unwrap_parameter header");
    };
    let ExprKind::Assign(lhs, rhs, _) = e.kind else {
        internal_err!(stmt.span, "ill-formed unwrap_parameter header");
    };

    let ExprKind::Path(lhs_qpath) = lhs.kind else {
        internal_err!(stmt.span, "ill-formed unwrap_parameter header");
    };
    let QPath::Resolved(None, lhs_path) = lhs_qpath else {
        internal_err!(stmt.span, "ill-formed unwrap_parameter header");
    };
    let Res::Local(lhs_hir_id) = lhs_path.res else {
        internal_err!(stmt.span, "ill-formed unwrap_parameter header");
    };
    let Node::Pat(lhs_pat) = tcx.hir_node(lhs_hir_id) else {
        internal_err!(stmt.span, "ill-formed unwrap_parameter header");
    };
    let lhs_name = crate::rust_to_vir_expr::pat_to_var(lhs_pat)?;

    let ExprKind::MethodCall(_, receiver, _, _) = rhs.kind else {
        internal_err!(stmt.span, "ill-formed unwrap_parameter header");
    };
    let ExprKind::Path(rhs_qpath) = receiver.kind else {
        internal_err!(stmt.span, "ill-formed unwrap_parameter header");
    };
    let QPath::Resolved(None, rhs_path) = rhs_qpath else {
        internal_err!(stmt.span, "ill-formed unwrap_parameter header");
    };
    let Res::Local(rhs_hir_id) = rhs_path.res else {
        internal_err!(stmt.span, "ill-formed unwrap_parameter header");
    };
    let Node::Pat(rhs_pat) = tcx.hir_node(rhs_hir_id) else {
        internal_err!(stmt.span, "ill-formed unwrap_parameter header");
    };
    let rhs_name = crate::rust_to_vir_expr::pat_to_var(rhs_pat)?;

    let idx = hir_params.iter().position(|param| param.pat.hir_id == rhs_pat.hir_id);
    let Some(idx) = idx else {
        internal_err!(stmt.span, "ill-formed unwrap_parameter header");
    };

    let mode = match &*vir_params[idx].x.typ {
        TypX::Decorate(TypDecoration::Tracked, _, _) => Mode::Proof,
        TypX::Decorate(TypDecoration::Ghost, _, _) => Mode::Spec,
        _ => {
            internal_err!(stmt.span, "ill-formed unwrap_parameter header");
        }
    };

    Ok(UnwrapParameter { mode, outer_name: rhs_name, inner_name: lhs_name })
}

fn is_header_verus_item(verus_item: &VerusItem) -> bool {
    match verus_item {
        VerusItem::Spec(spec_item) => match spec_item {
            SpecItem::Admit
            | SpecItem::Assume
            | SpecItem::AtomicCallLoop
            | SpecItem::InvMaskNone
            | SpecItem::InvMaskAny
            | SpecItem::InvMaskList
            | SpecItem::InvMaskListCompl
            | SpecItem::InvMaskSet
            | SpecItem::Atomically => false,

            SpecItem::NoMethodBody
            | SpecItem::Requires
            | SpecItem::Recommends
            | SpecItem::Ensures
            | SpecItem::Returns
            | SpecItem::InvariantExceptBreak
            | SpecItem::Invariant
            | SpecItem::AtomicSpec
            | SpecItem::Decreases
            | SpecItem::DecreasesWhen
            | SpecItem::DecreasesBy
            | SpecItem::RecommendsBy
            | SpecItem::OpensInvariantMask
            | SpecItem::NoUnwind
            | SpecItem::NoUnwindWhen => true,
        },
        VerusItem::Directive(dir_item) => match dir_item {
            crate::verus_items::DirectiveItem::ExtraDependency => true,
            _ => false,
        },
        _ => false,
    }
}

fn check_stmt_for_header<'tcx>(
    ctxt: &Context<'tcx>,
    stmt: &Stmt,
    pre_header: &mut PreHeader,
) -> Result<bool, VirErr> {
    match stmt.kind {
        StmtKind::Expr(e) | StmtKind::Semi(e) => check_expr_for_header(ctxt, e, pre_header),
        StmtKind::Item(item_id) => {
            let attrs = ctxt.tcx.hir_attrs(item_id.hir_id());
            let vattrs = ctxt.get_verifier_attrs(attrs)?;
            if vattrs.open_visibility_qualifier {
                let vis = crate::rust_to_vir_expr::get_open_visibility_qualifier(ctxt, item_id)?;
                if pre_header.open_visibility_qualifier.is_some() {
                    return err_span(
                        stmt.span,
                        "only one open_visibility_qualifier declaration allowed",
                    );
                }
                pre_header.open_visibility_qualifier = Some(vis);
                Ok(true)
            } else {
                Ok(false)
            }
        }
        _ => Ok(false),
    }
}

fn check_expr_for_header<'tcx>(
    ctxt: &Context<'tcx>,
    e: &Expr,
    pre_header: &mut PreHeader,
) -> Result<bool, VirErr> {
    let ExprKind::Call(fun, args) = e.kind else {
        return Ok(false);
    };
    let ExprKind::Path(fun_qpath) = fun.kind else {
        return Ok(false);
    };
    let QPath::Resolved(None, fun_path) = fun_qpath else {
        return Ok(false);
    };
    let rustc_hir::def::Res::Def(_, def_id) = fun_path.res else {
        return Ok(false);
    };

    let Some(verus_item) = ctxt.get_verus_item(def_id) else {
        return Ok(false);
    };
    match verus_item {
        VerusItem::Spec(SpecItem::NoMethodBody) => {
            pre_header.no_method_body = true;
        }
        VerusItem::Spec(SpecItem::Returns) => {
            pre_header.returns = true;
        }
        VerusItem::Spec(SpecItem::Ensures) => {
            let possible_closure_arg = match args[0].kind {
                ExprKind::Block(block, _) if block.expr.is_some() => block.expr.unwrap(),
                ExprKind::Call(fun, args) if is_closure_to_fn_spec(ctxt, fun) => &args[0],
                _ => &args[0],
            };

            match &possible_closure_arg.kind {
                ExprKind::Closure(closure) => {
                    let closure_body = ctxt.tcx.hir_body(closure.body);
                    if let [param] = closure_body.params {
                        let id = crate::rust_to_vir_expr::pat_to_var(param.pat)?;
                        pre_header.ensure_id = Some(id);
                    }
                    if any_arg_uses_default_ensures(ctxt, closure_body.value) {
                        pre_header.default_ensures = true;
                    }
                }
                _ => {
                    if any_arg_uses_default_ensures(ctxt, &args[0]) {
                        pre_header.default_ensures = true;
                    }
                }
            }
        }
        //VerusItem::Spec(SpecItem::DefaultEnsures) => { pre_header.default_ensures = true; }
        _ => {}
    }

    Ok(is_header_verus_item(verus_item))
}

fn is_closure_to_fn_spec<'tcx>(ctxt: &Context<'tcx>, fun: &Expr) -> bool {
    let ExprKind::Path(fun_qpath) = fun.kind else {
        return false;
    };
    let QPath::Resolved(None, fun_path) = fun_qpath else {
        return false;
    };
    let rustc_hir::def::Res::Def(_, def_id) = fun_path.res else {
        return false;
    };
    let Some(verus_item) = ctxt.get_verus_item(def_id) else {
        return false;
    };
    matches!(verus_item, VerusItem::Expr(ExprItem::ClosureToFnSpec))
}

fn any_arg_uses_default_ensures<'tcx>(ctxt: &Context<'tcx>, e: &Expr) -> bool {
    let args = crate::rust_to_vir_expr::extract_array(e);
    for arg in args.iter() {
        let ExprKind::Call(fun, _args) = arg.kind else {
            continue;
        };
        let ExprKind::Path(fun_qpath) = fun.kind else {
            continue;
        };
        let QPath::Resolved(None, fun_path) = fun_qpath else {
            continue;
        };
        let rustc_hir::def::Res::Def(_, def_id) = fun_path.res else {
            continue;
        };

        let Some(verus_item) = ctxt.get_verus_item(def_id) else {
            continue;
        };

        match verus_item {
            VerusItem::Expr(ExprItem::DefaultEnsures) => {
                return true;
            }
            _ => {}
        }
    }
    false
}

pub(crate) fn sanity_check_preheader(
    span: rustc_span::Span,
    header: &vir::headers::Header,
    pre_header: &PreHeader,
) -> Result<(), VirErr> {
    let PreHeader {
        no_method_body,
        returns,
        default_ensures,
        open_visibility_qualifier,
        unwrap_parameters,
        ensure_id,
    } = pre_header;

    if *no_method_body != header.no_method_body {
        internal_err!(span, "sanity_check_preheader failed: no_method_body");
    }
    if *returns != header.returns.is_some() {
        internal_err!(span, "sanity_check_preheader failed: returns");
    }
    if *default_ensures != (header.ensure.1.len() > 0) {
        internal_err!(span, "sanity_check_preheader failed: default_ensures");
    }
    if *open_visibility_qualifier != header.open_visibility_qualifier {
        internal_err!(span, "sanity_check_preheader failed: open_visibility_qualifier");
    }
    if *unwrap_parameters != header.unwrap_parameters {
        internal_err!(span, "sanity_check_preheader failed: unwrap_parameters");
    }
    if *ensure_id != header.ensure_id_typ.as_ref().map(|(id, _)| id.clone()) {
        internal_err!(span, "sanity_check_preheader failed: ensure_id");
    }
    Ok(())
}
