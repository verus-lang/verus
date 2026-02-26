use crate::context::Context;
use crate::verus_items::RustItem;
use rustc_hir::HirId;
use rustc_span::Span;
use std::sync::Arc;
use vir::ast::{
    BinaryOp, Expr, ExprX, FunctionX, Mode, Place, PlaceX, SpannedTyped, VirErr, VirErrAs,
};

/// Traits with special handling
#[derive(Clone, Copy, Debug)]
pub enum SpecialTrait {
    Clone,
    //PartialEq,
}

/// What to do for a given automatically-derived trait impl
#[derive(Debug)]
pub enum AutomaticDeriveAction {
    Special(SpecialTrait),
    VerifyAsIs,
    /// Ignore, optionally providing a warning
    Ignore,
}

pub fn get_action(rust_item: Option<RustItem>) -> AutomaticDeriveAction {
    match rust_item {
        Some(RustItem::PartialEq | RustItem::Eq) => AutomaticDeriveAction::Ignore,
        Some(RustItem::Clone) => AutomaticDeriveAction::Special(SpecialTrait::Clone),

        Some(RustItem::Copy) => AutomaticDeriveAction::VerifyAsIs,

        Some(RustItem::Hash)
        | Some(RustItem::Default)
        | Some(RustItem::Debug)
        | Some(RustItem::Ord)
        | Some(RustItem::PartialOrd) => AutomaticDeriveAction::Ignore,

        Some(_) | None => AutomaticDeriveAction::VerifyAsIs,
    }
}

pub fn is_automatically_derived(attrs: &[rustc_hir::Attribute]) -> bool {
    for attr in attrs.iter() {
        match attr {
            rustc_hir::Attribute::Unparsed(item) => match &item.path.segments[..] {
                [segment] => {
                    if segment.as_str() == "automatically_derived" {
                        return true;
                    }
                }
                _ => {}
            },
            rustc_hir::Attribute::Parsed(
                rustc_hir::attrs::AttributeKind::AutomaticallyDerived(_),
            ) => {
                return true;
            }
            _ => {}
        }
    }
    false
}

pub fn modify_derived_item<'tcx>(
    ctxt: &Context<'tcx>,
    span: Span,
    hir_id: HirId,
    action: &AutomaticDeriveAction,
    function: &mut FunctionX,
) -> Result<(), VirErr> {
    let AutomaticDeriveAction::Special(special) = action else {
        return Ok(());
    };
    match special {
        SpecialTrait::Clone => {
            if &*function.name.path.last_segment() == "clone" {
                return clone_add_post_condition(ctxt, span, hir_id, function);
            }
        }
    }
    Ok(())
}

fn clone_add_post_condition<'tcx>(
    ctxt: &Context<'tcx>,
    span: Span,
    hir_id: HirId,
    functionx: &mut FunctionX,
) -> Result<(), VirErr> {
    let warn = |msg: &str| {
        ctxt.diagnostics
            .borrow_mut()
            .push(VirErrAs::Warning(crate::util::err_span_bare(span, msg.to_string())));
    };
    let warn_unexpected = || {
        warn(
            "autoderive Clone impl does not take the form Verus expects; continuing, but without adding a specification for the derived Clone impl",
        )
    };
    let warn_unsupported = || {
        warn(
            "Verus does not (yet) support autoderive Clone impl when the clone is not a copy; continuing, but without adding a specification for the derived Clone impl",
        )
    };

    let Some(body) = &functionx.body else {
        return Ok(());
    };

    let uses_copy;
    let self_var;

    match &body.x {
        ExprX::Block(_stmts, Some(last_expr)) => match &last_expr.x {
            ExprX::ReadPlace(pl, _) => match &pl.x {
                PlaceX::Local(id) if &*id.0 == "self" => {
                    uses_copy = true;
                    self_var = Some(last_expr.clone());
                }
                _ => {
                    warn_unexpected();
                    return Ok(());
                }
            },
            ExprX::Ctor { .. } => {
                uses_copy = false;
                self_var = None;
            }
            _ => {
                warn_unexpected();
                return Ok(());
            }
        },
        _ => {
            warn_unexpected();
            return Ok(());
        }
    }

    if functionx.ensure.0.len() != 0 {
        warn_unexpected();
        return Ok(());
    }

    if uses_copy {
        // Add `ensures ret == self`
        let self_var = self_var.unwrap();
        let ret_var = SpannedTyped::new(
            &self_var.span,
            &self_var.typ,
            ExprX::Var(functionx.ret.x.name.clone()),
        );
        let eq_expr = SpannedTyped::new(
            &self_var.span,
            &vir::ast_util::bool_typ(),
            ExprX::Binary(BinaryOp::Eq(Mode::Spec), ret_var.clone(), self_var.clone()),
        );

        let eq_expr = cleanup_span_ids(ctxt, span, hir_id, &eq_expr);
        functionx.ensure.0 = Arc::new(vec![eq_expr]);
    } else {
        warn_unsupported();
    }

    Ok(())
}

// TODO better place for this
fn cleanup_span_ids<'tcx>(ctxt: &Context<'tcx>, span: Span, hir_id: HirId, expr: &Expr) -> Expr {
    vir::ast_visitor::map_expr_place_visitor(
        expr,
        &|e: &Expr| {
            let e = ctxt.spans.spanned_typed_new(span, &e.typ, e.x.clone());
            let mut erasure_info = ctxt.erasure_info.borrow_mut();
            erasure_info.hir_vir_ids.push((hir_id, e.span.id));
            Ok(e)
        },
        &|p: &Place| {
            let p = ctxt.spans.spanned_typed_new(span, &p.typ, p.x.clone());
            let mut erasure_info = ctxt.erasure_info.borrow_mut();
            erasure_info.hir_vir_ids.push((hir_id, p.span.id));
            Ok(p)
        },
    )
    .unwrap()
}
