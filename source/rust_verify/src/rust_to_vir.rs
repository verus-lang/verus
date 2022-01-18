/*
Convert Rust HIR/THIR to VIR for verification.

For soundness's sake, be as defensive as possible:
- if we're not prepared to verify a feature of Rust, disallow the feature
- explicitly match all fields of the Rust AST so we catch any features added in the future
*/

use crate::context::Context;
use crate::rust_to_vir_adts::{check_item_enum, check_item_struct};
use crate::rust_to_vir_base::{def_id_to_vir_path, get_mode, hack_get_def_name, mk_visibility};
use crate::rust_to_vir_func::{check_foreign_item_fn, check_item_fn};
use crate::util::unsupported_err_span;
use crate::sm_to_vir::{SMCtxt};
use crate::{err_unless, unsupported_err, unsupported_err_unless, unsupported_unless};
use rustc_ast::Attribute;
use rustc_hir::{
    AssocItemKind, Crate, ForeignItem, ForeignItemId, ForeignItemKind, HirId, ImplItemKind, Item,
    ItemId, ItemKind, ModuleItems, QPath, TraitRef, TyKind,
};
use rustc_middle::ty::TyCtxt;
use std::collections::HashMap;
use std::sync::Arc;
use vir::ast::{Krate, KrateX, Mode, Path, VirErr};
use vir::ast_util::path_as_rust_name;

fn check_item<'tcx>(
    ctxt: &Context<'tcx>,
    vir: &mut KrateX,
    sm_ctxt: &mut SMCtxt,
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
                None,
                item.def_id.to_def_id(),
                visibility,
                ctxt.tcx.hir().attrs(item.hir_id()),
                sig,
                None,
                None,
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
                sm_ctxt,
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
                let path_name = path_as_rust_name(&def_id_to_vir_path(ctxt.tcx, path.res.def_id()));
                let ignore = if path_name == "builtin::Structural" {
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
                    true
                } else if path_name == "core::marker::StructuralEq"
                    || path_name == "core::cmp::Eq"
                    || path_name == "core::marker::StructuralPartialEq"
                    || path_name == "core::cmp::PartialEq"
                    || path_name == "builtin::Structural"
                {
                    // TODO SOUNDNESS additional checks of the implementation
                    true
                } else {
                    false
                };

                if ignore {
                    for impl_item_ref in impll.items {
                        match impl_item_ref.kind {
                            AssocItemKind::Fn { has_self } if has_self => {
                                if let ImplItemKind::Fn(sig, _) =
                                    &ctxt.tcx.hir().impl_item(impl_item_ref.id).kind
                                {
                                    ctxt.erasure_info
                                        .borrow_mut()
                                        .ignored_functions
                                        .push(sig.span.data());
                                } else {
                                    panic!("Fn impl item expected");
                                }
                            }
                            _ => {}
                        }
                    }
                    return Ok(());
                }
            }

            match impll.self_ty.kind {
                TyKind::Path(QPath::Resolved(
                    None,
                    rustc_hir::Path { res: rustc_hir::def::Res::Def(_, self_def_id), .. },
                )) => {
                    let self_path = def_id_to_vir_path(ctxt.tcx, *self_def_id);
                    let trait_path = impll.of_trait.as_ref().map(|TraitRef { path, .. }| {
                        def_id_to_vir_path(ctxt.tcx, path.res.def_id())
                    });
                    let adt_mode = {
                        let attrs = ctxt.tcx.hir().attrs(
                            ctxt.tcx
                                .hir()
                                .get_if_local(*self_def_id)
                                .expect("non-local def id of fun")
                                .hir_id()
                                .expect("adt must have hir_id"),
                        );
                        get_mode(Mode::Exec, attrs)
                    };
                    for impl_item_ref in impll.items {
                        match impl_item_ref.kind {
                            AssocItemKind::Fn { has_self: _ } => {
                                let impl_item = ctxt.tcx.hir().impl_item(impl_item_ref.id);
                                let impl_item_visibility =
                                    mk_visibility(&Some(module_path.clone()), &impl_item.vis);
                                match &impl_item.kind {
                                    ImplItemKind::Fn(sig, body_id) => {
                                        check_item_fn(
                                            ctxt,
                                            vir,
                                            Some(sm_ctxt),
                                            Some((self_path.clone(), adt_mode)),
                                            impl_item.def_id.to_def_id(),
                                            impl_item_visibility,
                                            ctxt.tcx.hir().attrs(impl_item.hir_id()),
                                            sig,
                                            trait_path.clone(),
                                            Some(&impll.generics),
                                            &impl_item.generics,
                                            body_id,
                                        )?;
                                    }
                                    _ => unsupported_err!(
                                        item.span,
                                        "unsupported item in impl",
                                        impl_item_ref
                                    ),
                                }
                            }
                            AssocItemKind::Type => {
                                let _impl_item = ctxt.tcx.hir().impl_item(impl_item_ref.id);
                                // the type system handles this for Trait impls
                            }
                            _ => unsupported_err!(
                                item.span,
                                "unsupported item ref in impl",
                                impl_item_ref
                            ),
                        }
                    }
                }
                _ => {
                    unsupported_err!(item.span, "unsupported impl of non-path type", item);
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
        exported_macros: _,
        non_exported_macro_attrs,
        items,
        trait_items,
        impl_items,
        foreign_items,
        bodies: _,
        trait_impls: _,
        body_ids: _,
        modules,
        proc_macros,
        trait_map: _,
        attrs,
    } = ctxt.krate;
    let mut vir: KrateX = Default::default();
    unsupported_unless!(
        non_exported_macro_attrs.len() == 0,
        "non-exported macro attributes",
        non_exported_macro_attrs
    );
    let mut item_to_module: HashMap<ItemId, Path> = HashMap::new();
    for (id, module) in modules {
        let path = crate::rust_to_vir_base::def_id_to_vir_path(ctxt.tcx, id.to_def_id());
        check_module(ctxt.tcx, &path, module, &mut item_to_module)?;
        vir.module_ids.push(path);
    }
    for (id, item) in foreign_items {
        check_foreign_item(ctxt, &mut vir, id, item)?;
    }
    let mut sm_ctxt = SMCtxt::new();
    for (id, item) in items {
        check_item(ctxt, &mut vir, &mut sm_ctxt, &item_to_module[id], id, item)?;
    }
    unsupported_unless!(trait_items.len() == 0, "trait definitions", trait_items);
    for (_id, impl_item) in impl_items {
        match impl_item.kind {
            ImplItemKind::Fn(_, _) => {
                let impl_item_ident = impl_item.ident.as_str();
                if impl_item_ident == "assert_receiver_is_total_eq"
                    || impl_item_ident == "eq"
                    || impl_item_ident == "ne"
                    || impl_item_ident == "assert_receiver_is_structural"
                {
                    // TODO: check whether these implement the correct trait
                }
            }
            ImplItemKind::TyAlias(_ty) => {
                // checked by the type system
            }
            _ => {
                unsupported_err!(impl_item.span, "unsupported_impl_item", impl_item);
            }
        }
    }
    // for (id, _trait_impl) in trait_impls {
    //
    // }
    unsupported_unless!(proc_macros.len() == 0, "procedural macros", proc_macros);
    // unsupported_unless!(trait_map.iter().all(|(_, v)| v.len() == 0), "traits", trait_map);
    for (id, attr) in attrs {
        check_attr(ctxt.tcx, id, attr)?;
    }
    Ok(Arc::new(vir))
}
