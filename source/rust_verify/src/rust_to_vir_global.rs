use std::sync::Arc;

use rustc_hir::{Item, ItemKind};
use vir::ast::{IntRange, Typ, TypX, VirErr};

use crate::{context::Context, unsupported_err_unless, verus_items::VerusItem};

#[derive(Debug, Hash)]
pub(crate) struct TypIgnoreImplPaths(pub Typ);

impl PartialEq for TypIgnoreImplPaths {
    fn eq(&self, other: &Self) -> bool {
        vir::ast_util::types_equal(&self.0, &other.0)
    }
}

impl Eq for TypIgnoreImplPaths {}

pub(crate) fn process_const_early<'tcx>(
    ctxt: &mut Context<'tcx>,
    typs_sizes_set: &mut std::collections::HashMap<TypIgnoreImplPaths, u128>,
    item: &Item<'tcx>,
) -> Result<(), VirErr> {
    let attrs = ctxt.tcx.hir().attrs(item.hir_id());
    let vattrs = ctxt.get_verifier_attrs(attrs)?;
    if vattrs.size_of_global {
        let err = crate::util::err_span(item.span, "invalid global size_of");
        let ItemKind::Const(_ty, generics, body_id) = item.kind else {
            return err;
        };
        unsupported_err_unless!(
            generics.params.len() == 0 && generics.predicates.len() == 0,
            item.span,
            "const generics"
        );
        let def_id = body_id.hir_id.owner.to_def_id();

        let body = crate::rust_to_vir_func::find_body(ctxt, &body_id);

        let types = crate::rust_to_vir_func::body_id_to_types(ctxt.tcx, &body_id);

        let rustc_hir::ExprKind::Block(block, _) = body.value.kind else {
            return err;
        };
        if block.stmts.len() < 1 {
            return err;
        }
        let rustc_hir::StmtKind::Semi(expr) = block.stmts[0].kind else {
            return err;
        };
        let rustc_hir::ExprKind::Call(fun, args) = expr.kind else {
            return err;
        };
        let rustc_hir::ExprKind::Path(rustc_hir::QPath::Resolved(None, path)) = fun.kind else {
            return err;
        };
        let last_segment = path.segments.last().expect("one segment in path");
        if ctxt.verus_items.id_to_name.get(&last_segment.res.def_id())
            != Some(&VerusItem::Global(crate::verus_items::GlobalItem::SizeOf))
        {
            return err;
        }
        let Some(generic_args) = last_segment.args else {
            return err;
        };
        let rustc_hir::GenericArg::Type(ty) = generic_args.args[0] else {
            return err;
        };
        let ty = types.node_type(ty.hir_id);
        let ty = crate::rust_to_vir_base::mid_ty_to_vir(
            ctxt.tcx,
            &ctxt.verus_items,
            def_id,
            item.span,
            &ty,
            true,
        )?;
        let rustc_hir::ExprKind::Lit(lit) = args[0].kind else {
            return err;
        };
        let rustc_ast::LitKind::Int(size, rustc_ast::LitIntType::Unsuffixed) = lit.node else {
            return err;
        };

        vir::layout::layout_of_typ_supported(&ty, &crate::spans::err_air_span(item.span))?;

        match typs_sizes_set.entry(TypIgnoreImplPaths(ty.clone())) {
            std::collections::hash_map::Entry::Occupied(_occ) => {
                return crate::util::err_span(
                    item.span,
                    format!(
                        "the size of `{}` can only be set once per crate",
                        vir::ast_util::typ_to_diagnostic_str(&ty)
                    ),
                );
            }
            std::collections::hash_map::Entry::Vacant(vac) => {
                vac.insert(size);
            }
        }

        if let TypX::Int(IntRange::USize | IntRange::ISize) = &*ty {
            let arch_word_bits = &mut Arc::make_mut(ctxt).arch_word_bits;
            if let Some(arch_word_bits) = arch_word_bits {
                let vir::ast::ArchWordBits::Exactly(size_bits_set) = arch_word_bits else {
                    panic!("unexpected ArchWordBits");
                };
                if (size * 8) as u32 != *size_bits_set {
                    return crate::util::err_span(
                        item.span,
                        format!("usize or isize have already been set to {} bits", *size_bits_set),
                    );
                }
            }
            *arch_word_bits = Some(match size {
                4 | 8 => vir::ast::ArchWordBits::Exactly((size * 8) as u32),
                _ => {
                    return crate::util::err_span(
                        item.span,
                        "usize and isize can be either 32 or 64 bits",
                    );
                }
            });
        }
    }
    Ok(())
}
