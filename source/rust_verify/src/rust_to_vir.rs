/*
Convert Rust HIR/THIR to VIR for verification.

For soundness's sake, be as defensive as possible:
- if we're not prepared to verify a feature of Rust, disallow the feature
- explicitly match all fields of the Rust AST so we catch any features added in the future
*/

use crate::rust_to_vir_adts::{check_item_enum, check_item_struct};
use crate::rust_to_vir_func::{check_foreign_item_fn, check_item_fn};
use crate::{unsupported, unsupported_unless};
use rustc_ast::Attribute;
use rustc_hir::{
    Crate, ForeignItem, ForeignItemId, ForeignItemKind, HirId, Item, ItemId, ItemKind, ModuleItems,
};
use rustc_middle::ty::TyCtxt;
use rustc_span::def_id::LocalDefId;
use std::rc::Rc;
use vir::ast::{Krate, KrateX, VirErr};

fn check_item<'tcx>(
    tcx: TyCtxt<'tcx>,
    krate: &'tcx Crate<'tcx>,
    vir: &mut KrateX,
    id: &ItemId,
    item: &'tcx Item<'tcx>,
) -> Result<(), VirErr> {
    match &item.kind {
        ItemKind::Fn(sig, generics, body_id) => {
            check_item_fn(
                tcx,
                krate,
                vir,
                item.ident,
                tcx.hir().attrs(item.hir_id()),
                sig,
                generics,
                body_id,
            )?;
        }
        ItemKind::Use { .. } => {}
        ItemKind::ExternCrate { .. } => {}
        ItemKind::Mod { .. } => {}
        ItemKind::ForeignMod { .. } => {}
        ItemKind::Struct(variant_data, generics) => {
            check_item_struct(tcx, krate, vir, item.span, id, variant_data, generics);
        }
        ItemKind::Enum(enum_def, generics) => {
            check_item_enum(tcx, krate, vir, item.span, id, enum_def, generics);
        }
        _ => {
            unsupported!("unsupported item", item);
        }
    }
    Ok(())
}

fn check_module<'tcx>(
    _tcx: TyCtxt<'tcx>,
    _id: &LocalDefId,
    module_items: &'tcx ModuleItems,
) -> Result<(), VirErr> {
    match module_items {
        ModuleItems { items, trait_items, impl_items, foreign_items } => {
            for _id in items {
                // TODO
            }
            unsupported_unless!(trait_items.len() == 0, "trait definitions", trait_items);
            unsupported_unless!(impl_items.len() == 0, "impl definitions", impl_items);
            for _id in foreign_items {
                // TODO
            }
        }
    }
    Ok(())
}

fn check_foreign_item<'tcx>(
    tcx: TyCtxt<'tcx>,
    vir: &mut KrateX,
    _id: &ForeignItemId,
    item: &'tcx ForeignItem<'tcx>,
) -> Result<(), VirErr> {
    match &item.kind {
        ForeignItemKind::Fn(decl, idents, generics) => {
            check_foreign_item_fn(
                tcx,
                vir,
                item.ident,
                item.span,
                tcx.hir().attrs(item.hir_id()),
                decl,
                idents,
                generics,
            )?;
        }
        _ => {
            unsupported!("unsupported item", item);
        }
    }
    Ok(())
}

fn check_attr<'tcx>(
    _tcx: TyCtxt<'tcx>,
    _id: &HirId,
    _attr: &'tcx [Attribute],
) -> Result<(), VirErr> {
    // TODO
    Ok(())
}

pub fn crate_to_vir<'tcx>(tcx: TyCtxt<'tcx>, krate: &'tcx Crate<'tcx>) -> Result<Krate, VirErr> {
    let Crate {
        item: _,
        exported_macros,
        non_exported_macro_attrs,
        items,
        trait_items,
        impl_items,
        foreign_items,
        bodies: _,
        trait_impls,
        body_ids: _,
        modules,
        proc_macros,
        trait_map,
        attrs,
    } = krate;
    let mut vir: KrateX = Default::default();
    unsupported_unless!(
        exported_macros.len() == 0,
        "exported macros from a crate",
        exported_macros
    );
    unsupported_unless!(
        non_exported_macro_attrs.len() == 0,
        "non-exported macro attributes",
        non_exported_macro_attrs
    );
    for (id, item) in foreign_items {
        check_foreign_item(tcx, &mut vir, id, item)?;
    }
    for (id, item) in items {
        check_item(tcx, krate, &mut vir, id, item)?;
    }
    unsupported_unless!(trait_items.len() == 0, "trait definitions", trait_items);
    unsupported_unless!(impl_items.len() == 0, "impl definitions", impl_items);
    unsupported_unless!(trait_impls.len() == 0, "trait implementations", trait_impls);
    for (id, module) in modules {
        check_module(tcx, id, module)?;
    }
    unsupported_unless!(proc_macros.len() == 0, "procedural macros", proc_macros);
    unsupported_unless!(trait_map.len() == 0, "traits", trait_map);
    for (id, attr) in attrs {
        check_attr(tcx, id, attr)?;
    }
    Ok(Rc::new(vir))
}
