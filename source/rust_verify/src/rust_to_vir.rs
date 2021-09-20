/*
Convert Rust HIR/THIR to VIR for verification.

For soundness's sake, be as defensive as possible:
- if we're not prepared to verify a feature of Rust, disallow the feature
- explicitly match all fields of the Rust AST so we catch any features added in the future
*/

use crate::context::Context;
use crate::rust_to_vir_adts::{check_item_enum, check_item_struct};
use crate::rust_to_vir_base::{hack_check_def_name, hack_get_def_name, mk_visibility};
use crate::rust_to_vir_func::{check_foreign_item_fn, check_item_fn};
use crate::util::unsupported_err_span;
use crate::{err_unless, unsupported_err, unsupported_err_unless, unsupported_unless};
use rustc_ast::Attribute;
use rustc_hir::{
    Crate, ForeignItem, ForeignItemId, ForeignItemKind, HirId, Item,
    ItemId, ItemKind, ModuleItems, QPath, TraitRef, TyKind,
};
use rustc_middle::ty::TyCtxt;
use std::collections::HashMap;
use std::sync::Arc;
use vir::ast::{Krate, KrateX, Path, VirErr};

fn check_item<'tcx>(
    ctxt: &Context<'tcx>,
    vir: &mut KrateX,
    module_path: &Path,
    id: &ItemId,
    item: &'tcx Item<'tcx>,
) -> Result<(), VirErr> {
    let visibility = mk_visibility(&Some(module_path.clone()), &item.vis);
    match &item.kind {
        ItemKind::Fn(sig, generics, body_id) => {
            check_item_fn(
                ctxt,
                vir,
                None,
                item.def_id.to_def_id(),
                visibility,
                ctxt.tcx.hir().attrs(item.hir_id()),
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
            // TODO use rustc_middle info here? if sufficient, it may allow for a single code path
            // for definitions of the local crate and imported crates
            // let adt_def = tcx.adt_def(item.def_id);
            check_item_struct(
                ctxt,
                vir,
                item.span,
                id,
                visibility,
                ctxt.tcx.hir().attrs(item.hir_id()),
                variant_data,
                generics,
            )?;
        }
        ItemKind::Enum(enum_def, generics) => {
            // TODO use rustc_middle? see `Struct` case
            check_item_enum(
                ctxt,
                vir,
                item.span,
                id,
                visibility,
                ctxt.tcx.hir().attrs(item.hir_id()),
                enum_def,
                generics,
            )?;
        }
        ItemKind::Impl(impll) => {
            if let Some(TraitRef { path, hir_ref_id: _ }) = impll.of_trait {
                unsupported_err_unless!(
                    hack_check_def_name(
                        ctxt.tcx,
                        path.res.def_id(),
                        "core",
                        "marker::StructuralEq"
                    ) || hack_check_def_name(ctxt.tcx, path.res.def_id(), "core", "cmp::Eq")
                        || hack_check_def_name(
                            ctxt.tcx,
                            path.res.def_id(),
                            "core",
                            "marker::StructuralPartialEq"
                        )
                        || hack_check_def_name(
                            ctxt.tcx,
                            path.res.def_id(),
                            "core",
                            "cmp::PartialEq"
                        )
                        || hack_check_def_name(
                            ctxt.tcx,
                            path.res.def_id(),
                            "builtin",
                            "Structural"
                        ),
                    item.span,
                    "non_eq_trait_impl",
                    path
                );
                if hack_check_def_name(ctxt.tcx, path.res.def_id(), "builtin", "Structural") {
                    let ty = {
                        // TODO extract to rust_to_vir_base, or use
                        // https://doc.rust-lang.org/nightly/nightly-rustc/rustc_typeck/fn.hir_ty_to_ty.html
                        // ?
                        let def_id = match impll.self_ty.kind {
                            rustc_hir::TyKind::Path(QPath::Resolved(None, path)) => {
                                path.res.def_id()
                            }
                            _ => panic!(
                                "self type of impl is not resolved: {:?}",
                                impll.self_ty.kind
                            ),
                        };
                        ctxt.tcx.type_of(def_id)
                    };
                    // TODO: this may be a bit of a hack: to query the TyCtxt for the StructuralEq impl it seems we need
                    // a concrete type, so apply ! to all type parameters
                    let ty_kind_applied_never =
                        if let rustc_middle::ty::TyKind::Adt(def, substs) = ty.kind() {
                            rustc_middle::ty::TyKind::Adt(
                                def,
                                ctxt.tcx.mk_substs(substs.iter().map(|g| match g.unpack() {
                                    rustc_middle::ty::subst::GenericArgKind::Type(_) => {
                                        (*ctxt.tcx).types.never.into()
                                    }
                                    _ => g,
                                })),
                            )
                        } else {
                            panic!("Structural impl for non-adt type");
                        };
                    let ty_applied_never = ctxt.tcx.mk_ty(ty_kind_applied_never);
                    err_unless!(
                        ty_applied_never.is_structural_eq_shallow(ctxt.tcx),
                        item.span,
                        format!("Structural impl for non-structural type {:?}", ty),
                        ty
                    );
                }
            } else {
                unsupported_err_unless!(
                    impll.of_trait.is_none(),
                    item.span,
                    "unsupported impl of trait",
                    item
                );
                unsupported_err_unless!(
                    impll.generics.params.len() == 0,
                    item.span,
                    "unsupported impl of non-trait with generics",
                    item
                );
                match impll.self_ty.kind {
                    TyKind::Path(QPath::Resolved(_, _path)) => {
                        for impl_item in impll.items {
                            // TODO once we have references
                            unsupported_err!(item.span, "unsupported method in impl", impl_item);
                        }
                    }
                    _ => {
                        unsupported_err!(item.span, "unsupported impl of non-path type", item);
                    }
                }
            }
        }
        ItemKind::Const(_ty, _body_id) => {
            unsupported_err_unless!(
                hack_get_def_name(ctxt.tcx, _body_id.hir_id.owner.to_def_id())
                    .starts_with("_DERIVE_builtin_Structural_FOR_"),
                item.span,
                "unsupported const",
                item
            );
        }
        _ => {
            unsupported_err!(item.span, "unsupported item", item);
        }
    }
    Ok(())
}

fn check_module<'tcx>(
    _tcx: TyCtxt<'tcx>,
    module_path: &Path,
    module_items: &'tcx ModuleItems,
    item_to_module: &mut HashMap<ItemId, Path>,
) -> Result<(), VirErr> {
    match module_items {
        ModuleItems { items, trait_items, impl_items, foreign_items } => {
            for item_id in items {
                item_to_module.insert(*item_id, module_path.clone());
            }
            unsupported_unless!(trait_items.len() == 0, "trait definitions", trait_items);
            for _id in impl_items {
                // TODO?
            }
            for _id in foreign_items {
                // TODO
            }
        }
    }
    Ok(())
}

fn check_foreign_item<'tcx>(
    ctxt: &Context<'tcx>,
    vir: &mut KrateX,
    _id: &ForeignItemId,
    item: &'tcx ForeignItem<'tcx>,
) -> Result<(), VirErr> {
    match &item.kind {
        ForeignItemKind::Fn(decl, idents, generics) => {
            check_foreign_item_fn(
                ctxt,
                vir,
                item.def_id.to_def_id(),
                item.span,
                mk_visibility(&None, &item.vis),
                ctxt.tcx.hir().attrs(item.hir_id()),
                decl,
                idents,
                generics,
            )?;
        }
        _ => {
            unsupported_err!(item.span, "unsupported item", item);
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

pub fn crate_to_vir<'tcx>(ctxt: &Context<'tcx>) -> Result<Krate, VirErr> {
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
    } = ctxt.krate;
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
    let mut item_to_module: HashMap<ItemId, Path> = HashMap::new();
    for (id, module) in modules {
        let path = crate::rust_to_vir_base::def_to_path(ctxt.tcx, id.to_def_id());
        check_module(ctxt.tcx, &path, module, &mut item_to_module)?;
        vir.module_ids.push(path);
    }
    for (id, item) in foreign_items {
        check_foreign_item(ctxt, &mut vir, id, item)?;
    }
    for (id, item) in items {
        check_item(ctxt, &mut vir, &item_to_module[id], id, item)?;
    }
    unsupported_unless!(trait_items.len() == 0, "trait definitions", trait_items);
    for (_id, impl_item) in impl_items {
        let impl_item_ident = impl_item.ident.as_str();
        // TODO: check whether these implement the correct trait
        unsupported_unless!(
            impl_item_ident == "assert_receiver_is_total_eq"
                || impl_item_ident == "eq"
                || impl_item_ident == "ne"
                || impl_item_ident == "assert_receiver_is_structural",
            "impl definition",
            impl_item
        );
    }
    for (id, _trait_impl) in trait_impls {
        unsupported_unless!(
            hack_check_def_name(ctxt.tcx, *id, "core", "marker::StructuralEq")
                || hack_check_def_name(ctxt.tcx, *id, "core", "cmp::Eq")
                || hack_check_def_name(ctxt.tcx, *id, "core", "marker::StructuralPartialEq")
                || hack_check_def_name(ctxt.tcx, *id, "core", "cmp::PartialEq")
                || hack_check_def_name(ctxt.tcx, *id, "builtin", "Structural"),
            "non_eq_trait_impl",
            id
        );
    }
    unsupported_unless!(proc_macros.len() == 0, "procedural macros", proc_macros);
    unsupported_unless!(trait_map.iter().all(|(_, v)| v.len() == 0), "traits", trait_map);
    for (id, attr) in attrs {
        check_attr(ctxt.tcx, id, attr)?;
    }
    Ok(Arc::new(vir))
}
