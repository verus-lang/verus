use std::sync::Arc;

use rustc_hir::{Item, ItemKind};
use vir::ast::{IntRange, VirErr};

use crate::{attributes::get_verifier_attrs, context::Context, verus_items::VerusItem};

pub(crate) fn process_const_early<'tcx>(
    ctxt: &mut Context<'tcx>,
    item: &Item<'tcx>,
) -> Result<(), VirErr> {
    let attrs = ctxt.tcx.hir().attrs(item.hir_id());
    let vattrs = get_verifier_attrs(attrs, Some(&mut *ctxt.diagnostics.borrow_mut()))?;
    let err = crate::util::err_span(item.span, "invalid global size_of");
    if vattrs.size_of_global {
        let ItemKind::Const(_ty, body_id) = item.kind else { return err; };
        let def_id = body_id.hir_id.owner.to_def_id();

        let body = crate::rust_to_vir_func::find_body(ctxt, &body_id);

        let types = crate::rust_to_vir_func::body_id_to_types(ctxt.tcx, &body_id);

        let rustc_hir::ExprKind::Block(block, _) = body.value.kind else { return err; };
        if block.stmts.len() != 1 {
            return err;
        }
        let rustc_hir::StmtKind::Semi(expr) = block.stmts[0].kind else { return err; };
        let rustc_hir::ExprKind::Call(fun, args) = expr.kind else { return err; };
        let rustc_hir::ExprKind::Path(rustc_hir::QPath::Resolved(None, path)) = fun.kind else { return err; };
        let last_segment = path.segments.last().expect("one segment in path");
        if ctxt.verus_items.id_to_name.get(&last_segment.res.def_id())
            != Some(&VerusItem::Global(crate::verus_items::GlobalItem::SizeOf))
        {
            return err;
        }
        let Some(generic_args) = last_segment.args else { return err; };
        let rustc_hir::GenericArg::Type(ty) = generic_args.args[0] else { return err; };
        let ty = types.node_type(ty.hir_id);
        let ty = crate::rust_to_vir_base::mid_ty_to_vir(
            ctxt.tcx,
            &ctxt.verus_items,
            def_id,
            item.span,
            &ty,
            true,
        )?;
        let rustc_hir::ExprKind::Lit(lit) = args[0].kind else { return err; };
        let rustc_ast::LitKind::Int(size, rustc_ast::LitIntType::Unsuffixed) = lit.node else { return err; };

        match &*ty {
            vir::ast::TypX::Int(IntRange::USize) => {
                let arch_word_bits = &mut Arc::make_mut(ctxt).arch_word_bits;
                if arch_word_bits.is_some() {
                    return crate::util::err_span(
                        item.span,
                        "the size of usize can only be set once per crate",
                    );
                }
                *arch_word_bits = Some(match size {
                    4 | 8 => vir::ast::ArchWordBits::Exactly((size as u32) * 8),
                    _ => {
                        return crate::util::err_span(
                            item.span,
                            "usize can be either 32 or 64 bits",
                        );
                    }
                });
            }
            _ => {
                return crate::util::err_span(item.span, "only usize is currently supported here");
            }
        }
    }
    Ok(())
}
