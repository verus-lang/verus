/*
Convert Rust HIR/THIR to VIR for verification.

For soundness's sake, be as defensive as possible:
- if we're not prepared to verify a feature of Rust, disallow the feature
- explicitly match all fields of the Rust AST so we catch any features added in the future
*/

use crate::attributes::{get_mode, get_verifier_attrs};
use crate::context::Context;
use crate::def::is_get_variant_fn_name;
use crate::rust_to_vir_adts::{check_item_enum, check_item_struct};
use crate::rust_to_vir_base::{
    def_id_to_vir_path, fn_item_hir_id_to_self_def_id, hack_get_def_name, mk_visibility, ty_to_vir,
};
use crate::rust_to_vir_func::{check_foreign_item_fn, check_item_fn};
use crate::util::{err_span_str, unsupported_err_span};
use crate::{err_unless, unsupported_err};

use rustc_hir::{
    AssocItemKind, ForeignItem, ForeignItemId, ForeignItemKind, ImplItemKind, Item, ItemId,
    ItemKind, OwnerNode, QPath, TraitRef, TyKind,
};

use std::collections::HashMap;
use std::sync::Arc;
use vir::ast::{Krate, KrateX, Mode, Path, VirErr};
use vir::ast_util::path_as_rust_name;

fn check_item<'tcx>(
    ctxt: &Context<'tcx>,
    vir: &mut KrateX,
    module_path: &Path,
    id: &ItemId,
    item: &'tcx Item<'tcx>,
) -> Result<(), VirErr> {
    let visibility = mk_visibility(&Some(module_path.clone()), &item.vis, true);
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
                module_path,
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
                module_path,
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
                        format!("structural impl for non-structural type {:?}", ty),
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
                                    mk_visibility(&Some(module_path.clone()), &impl_item.vis, true);
                                match &impl_item.kind {
                                    ImplItemKind::Fn(sig, body_id) => {
                                        let fn_attrs = ctxt.tcx.hir().attrs(impl_item.hir_id());
                                        let fn_vattrs = get_verifier_attrs(fn_attrs)?;
                                        if fn_vattrs.is_variant {
                                            let valid = fn_item_hir_id_to_self_def_id(
                                                ctxt.tcx,
                                                impl_item.hir_id(),
                                            )
                                            .map(|self_def_id| ctxt.tcx.adt_def(self_def_id))
                                            .and_then(|adt| {
                                                is_get_variant_fn_name(&impl_item.ident).and_then(
                                                    |(variant_name, variant_field)| {
                                                        adt.variants
                                                            .iter()
                                                            .find(|v| {
                                                                v.ident.as_str() == variant_name
                                                            })
                                                            .and_then(|variant| {
                                                                use crate::def::FieldName;
                                                                match variant_field {
                                                                    Some(FieldName::Named(
                                                                        f_name,
                                                                    )) => variant
                                                                        .fields
                                                                        .iter()
                                                                        .find(|f| {
                                                                            f.ident.as_str()
                                                                                == f_name
                                                                        })
                                                                        .map(|_| ()),
                                                                    Some(FieldName::Unnamed(
                                                                        f_num,
                                                                    )) => (f_num
                                                                        < variant.fields.len())
                                                                    .then(|| ()),
                                                                    None => Some(()),
                                                                }
                                                            })
                                                    },
                                                )
                                            })
                                            .is_some();
                                            if !valid
                                                || get_mode(Mode::Exec, fn_attrs) != Mode::Spec
                                            {
                                                return err_span_str(
                                                    sig.span,
                                                    "invalid is_variant function, do not use #[verifier(is_variant)] directly, use the #[is_variant] macro instead",
                                                );
                                            }
                                        } else {
                                            check_item_fn(
                                                ctxt,
                                                vir,
                                                Some((self_path.clone(), adt_mode)),
                                                impl_item.def_id.to_def_id(),
                                                impl_item_visibility,
                                                fn_attrs,
                                                sig,
                                                trait_path.clone(),
                                                Some(&impll.generics),
                                                &impl_item.generics,
                                                body_id,
                                            )?;
                                        }
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
        ItemKind::Const(ty, body_id) => {
            if hack_get_def_name(ctxt.tcx, body_id.hir_id.owner.to_def_id())
                .starts_with("_DERIVE_builtin_Structural_FOR_")
            {
                ctxt.erasure_info.borrow_mut().ignored_functions.push(item.span.data());
                return Ok(());
            }
            crate::rust_to_vir_func::check_item_const(
                ctxt,
                vir,
                item.span,
                item.def_id.to_def_id(),
                visibility,
                ctxt.tcx.hir().attrs(item.hir_id()),
                &ty_to_vir(ctxt.tcx, ty),
                body_id,
            )?;
        }
        ItemKind::Macro(_macro_def) => {}
        _ => {
            unsupported_err!(item.span, "unsupported item", item);
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
                mk_visibility(&None, &item.vis, true),
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

pub fn crate_to_vir<'tcx>(ctxt: &Context<'tcx>) -> Result<Krate, VirErr> {
    let mut vir: KrateX = Default::default();
    let mut item_to_module: HashMap<ItemId, Path> = HashMap::new();
    for (owner_id, owner_opt) in ctxt.krate.owners.iter_enumerated() {
        if let Some(owner) = owner_opt {
            match owner.node() {
                OwnerNode::Item(Item { kind: ItemKind::Mod(mod_), def_id, .. }) => {
                    let path =
                        crate::rust_to_vir_base::def_id_to_vir_path(ctxt.tcx, def_id.to_def_id());
                    vir.module_ids.push(path.clone());
                    item_to_module.extend(mod_.item_ids.iter().map(move |ii| (*ii, path.clone())))
                }
                OwnerNode::Crate(mod_) => {
                    let path =
                        crate::rust_to_vir_base::def_id_to_vir_path(ctxt.tcx, owner_id.to_def_id());
                    vir.module_ids.push(path.clone());
                    item_to_module.extend(mod_.item_ids.iter().map(move |ii| (*ii, path.clone())))
                }
                _ => (),
            }
        }
    }
    for owner in ctxt.krate.owners.iter() {
        if let Some(owner) = owner {
            match owner.node() {
                OwnerNode::Item(item) => {
                    let item_path;
                    // If the item does not belong to a module, use the def_id of its owner as the
                    // module path
                    let module_path = if let Some(path) = item_to_module.get(&item.item_id()) {
                        path
                    } else {
                        let owned_by = ctxt.krate.owners[item.hir_id().owner]
                            .as_ref()
                            .expect("owner of item")
                            .node();
                        item_path = def_id_to_vir_path(ctxt.tcx, owned_by.def_id().to_def_id());
                        &item_path
                    };
                    check_item(ctxt, &mut vir, module_path, &item.item_id(), item)?
                }
                OwnerNode::ForeignItem(foreign_item) => check_foreign_item(
                    ctxt,
                    &mut vir,
                    &foreign_item.foreign_item_id(),
                    foreign_item,
                )?,
                OwnerNode::TraitItem(trait_item) => {
                    unsupported_err!(trait_item.span, "trait items", trait_item)
                }
                OwnerNode::ImplItem(impl_item) => match impl_item.kind {
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
                },
                OwnerNode::Crate(_mod_) => (),
            }
        }
    }
    Ok(Arc::new(vir))
}
