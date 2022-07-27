/*
Convert Rust HIR/THIR to VIR for verification.

For soundness's sake, be as defensive as possible:
- if we're not prepared to verify a feature of Rust, disallow the feature
- explicitly match all fields of the Rust AST so we catch any features added in the future
*/

use crate::attributes::{get_mode, get_verifier_attrs, GetVariantField};
use crate::context::Context;
use crate::def::{get_variant_fn_name, is_variant_fn_name};
use crate::rust_to_vir_adts::{check_item_enum, check_item_struct};
use crate::rust_to_vir_base::{
    check_generics_bounds, def_id_to_vir_path, fn_item_hir_id_to_self_def_id, hack_get_def_name,
    ident_to_var, mk_visibility, ty_to_vir, typ_path_and_ident_to_vir_path,
};
use crate::rust_to_vir_func::{check_foreign_item_fn, check_item_fn};
use crate::util::{err_span_str, spanned_new, unsupported_err_span};
use crate::{err_unless, unsupported_err, unsupported_err_unless};

use rustc_ast::IsAuto;
use rustc_hir::{
    AssocItemKind, ForeignItem, ForeignItemId, ForeignItemKind, ImplItemKind, ImplicitSelfKind,
    Item, ItemId, ItemKind, OwnerNode, QPath, TraitFn, TraitItem, TraitItemKind, TraitRef, TyKind,
    Unsafety,
};

use std::collections::HashMap;
use std::sync::Arc;
use vir::ast::{Fun, FunX, FunctionKind, Krate, KrateX, Mode, Path, TypX, VirErr};
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
                item.def_id.to_def_id(),
                FunctionKind::Static,
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
            //
            // UPDATE: We now use _some_ rustc_middle info with the adt_def, which we
            // use to get rustc_middle types. However, we don't exclusively use
            // rustc_middle; in fact, we still rely on attributes which we can only
            // get from the HIR data.

            let tyof = ctxt.tcx.type_of(item.def_id.to_def_id());
            let adt_def = tyof.ty_adt_def().expect("adt_def");

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
                adt_def,
            )?;
        }
        ItemKind::Enum(enum_def, generics) => {
            let tyof = ctxt.tcx.type_of(item.def_id.to_def_id());
            let adt_def = tyof.ty_adt_def().expect("adt_def");

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
                adt_def,
            )?;
        }
        ItemKind::Impl(impll) => {
            let attrs = ctxt.tcx.hir().attrs(item.hir_id());
            let vattrs = get_verifier_attrs(attrs)?;

            if vattrs.external {
                return Ok(());
            }
            if impll.unsafety != Unsafety::Normal {
                return err_span_str(item.span, "the verifier does not support `unsafe` here");
            }

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
                    let self_typ = ty_to_vir(ctxt.tcx, impll.self_ty);
                    let datatype_typ_args = if let TypX::Datatype(_, typ_args) = &*self_typ {
                        typ_args.clone()
                    } else {
                        panic!("expected datatype")
                    };
                    let self_path = def_id_to_vir_path(ctxt.tcx, *self_def_id);
                    let trait_path_typ_args =
                        impll.of_trait.as_ref().map(|TraitRef { path, .. }| {
                            crate::rust_to_vir_base::def_id_to_datatype_typ_args(
                                ctxt.tcx,
                                path.res.def_id(),
                                path.segments,
                            )
                        });
                    for impl_item_ref in impll.items {
                        match impl_item_ref.kind {
                            AssocItemKind::Fn { has_self } => {
                                let impl_item = ctxt.tcx.hir().impl_item(impl_item_ref.id);
                                let mut impl_item_visibility =
                                    mk_visibility(&Some(module_path.clone()), &impl_item.vis, true);
                                match &impl_item.kind {
                                    ImplItemKind::Fn(sig, body_id) => {
                                        let fn_attrs = ctxt.tcx.hir().attrs(impl_item.hir_id());
                                        let fn_vattrs = get_verifier_attrs(fn_attrs)?;
                                        if fn_vattrs.is_variant.is_some()
                                            || fn_vattrs.get_variant.is_some()
                                        {
                                            let find_variant = |variant_name: &str| {
                                                fn_item_hir_id_to_self_def_id(
                                                    ctxt.tcx,
                                                    impl_item.hir_id(),
                                                )
                                                .map(|self_def_id| ctxt.tcx.adt_def(self_def_id))
                                                .and_then(|adt| {
                                                    adt.variants
                                                        .iter()
                                                        .find(|v| v.ident.as_str() == variant_name)
                                                })
                                            };
                                            let valid = if let Some(variant_name) =
                                                fn_vattrs.is_variant
                                            {
                                                find_variant(&variant_name).is_some()
                                                    && impl_item.ident.as_str()
                                                        == is_variant_fn_name(&variant_name)
                                            } else if let Some((variant_name, field_name)) =
                                                fn_vattrs.get_variant
                                            {
                                                let field_name_str = match field_name {
                                                    GetVariantField::Unnamed(i) => format!("{}", i),
                                                    GetVariantField::Named(n) => n,
                                                };
                                                find_variant(&variant_name)
                                                    .and_then(|variant| {
                                                        variant.fields.iter().find(|f| {
                                                            f.ident.as_str()
                                                                == field_name_str.as_str()
                                                        })
                                                    })
                                                    .is_some()
                                                    && impl_item.ident.as_str()
                                                        == get_variant_fn_name(
                                                            &variant_name,
                                                            &field_name_str,
                                                        )
                                            } else {
                                                unreachable!()
                                            };
                                            if !valid
                                                || get_mode(Mode::Exec, fn_attrs) != Mode::Spec
                                            {
                                                return err_span_str(
                                                    sig.span,
                                                    "invalid is_variant function, do not use #[verifier(is_variant)] directly, use the #[is_variant] macro instead",
                                                );
                                            }
                                        } else {
                                            let kind = if let Some((trait_path, trait_typ_args)) =
                                                trait_path_typ_args.clone()
                                            {
                                                unsupported_err_unless!(
                                                    has_self,
                                                    sig.span,
                                                    "method without self"
                                                );
                                                impl_item_visibility = mk_visibility(
                                                    &Some(module_path.clone()),
                                                    &impl_item.vis,
                                                    false,
                                                );
                                                let ident = ident_to_var(&impl_item_ref.ident);
                                                let ident = Arc::new(ident);
                                                let path = typ_path_and_ident_to_vir_path(
                                                    &trait_path,
                                                    ident,
                                                );
                                                let fun = FunX { path, trait_path: None };
                                                let method = Arc::new(fun);
                                                let datatype = self_path.clone();
                                                let datatype_typ_args = datatype_typ_args.clone();
                                                FunctionKind::TraitMethodImpl {
                                                    method,
                                                    trait_path,
                                                    trait_typ_args,
                                                    datatype,
                                                    datatype_typ_args,
                                                }
                                            } else {
                                                FunctionKind::Static
                                            };
                                            check_item_fn(
                                                ctxt,
                                                vir,
                                                impl_item.def_id.to_def_id(),
                                                kind,
                                                impl_item_visibility,
                                                fn_attrs,
                                                sig,
                                                trait_path_typ_args.clone().map(|(p, _)| p),
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
        ItemKind::Static(..)
            if get_verifier_attrs(ctxt.tcx.hir().attrs(item.hir_id()))?.external =>
        {
            return Ok(());
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
        ItemKind::Trait(IsAuto::No, Unsafety::Normal, trait_generics, bounds, trait_items) => {
            let generics_bnds = check_generics_bounds(ctxt.tcx, trait_generics, false)?;
            for b in bounds.iter() {
                match &*crate::rust_to_vir_base::check_generic_bound(ctxt.tcx, b.span(), b)? {
                    vir::ast::GenericBoundX::Traits(ts) if ts.len() == 0 => {}
                    _ => {
                        unsupported_err!(item.span, "trait generic bounds");
                    }
                }
            }
            let trait_path = def_id_to_vir_path(ctxt.tcx, item.def_id.to_def_id());
            let mut methods: Vec<Fun> = Vec::new();
            for trait_item_ref in *trait_items {
                let trait_item = ctxt.tcx.hir().trait_item(trait_item_ref.id);
                let TraitItem { ident: _, def_id, generics: item_generics, kind, span } =
                    trait_item;
                let generics_bnds = check_generics_bounds(ctxt.tcx, item_generics, false)?;
                unsupported_err_unless!(generics_bnds.len() == 0, *span, "trait generics");
                match kind {
                    TraitItemKind::Fn(sig, fun) => {
                        let body_id = match fun {
                            TraitFn::Required(..) => {
                                // REVIEW: it would be nice to allow spec functions to omit the body,
                                // but rustc seems to drop the parameter attributes if there's no body.
                                unsupported_err!(
                                    *span,
                                    "trait function must have a body that calls no_method_body()"
                                )
                            }
                            TraitFn::Provided(body_id) => body_id,
                        };
                        if let ImplicitSelfKind::None = sig.decl.implicit_self {
                            unsupported_err!(*span, "trait function must have a self argument")
                        }
                        let attrs = ctxt.tcx.hir().attrs(trait_item.hir_id());
                        let fun = check_item_fn(
                            ctxt,
                            vir,
                            def_id.to_def_id(),
                            FunctionKind::TraitMethodDecl { trait_path: trait_path.clone() },
                            visibility.clone(),
                            attrs,
                            sig,
                            None,
                            Some(trait_generics),
                            item_generics,
                            body_id,
                        )?;
                        if let Some(fun) = fun {
                            methods.push(fun);
                        }
                    }
                    _ => {
                        unsupported_err!(item.span, "unsupported item", item);
                    }
                }
            }
            let traitx = vir::ast::TraitX {
                name: trait_path,
                methods: Arc::new(methods),
                typ_params: Arc::new(generics_bnds),
            };
            vir.traits.push(spanned_new(item.span, traitx));
        }
        ItemKind::TyAlias(_ty, _generics) => {
            // type alias (like lines of the form `type X = ...;`
            // Nothing to do here - we can rely on Rust's type resolution to handle these
        }
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
                    let path = def_id_to_vir_path(ctxt.tcx, def_id.to_def_id());
                    vir.module_ids.push(path.clone());
                    item_to_module.extend(mod_.item_ids.iter().map(move |ii| (*ii, path.clone())))
                }
                OwnerNode::Crate(mod_) => {
                    let path = def_id_to_vir_path(ctxt.tcx, owner_id.to_def_id());
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
                OwnerNode::TraitItem(_trait_item) => {
                    // handled by ItemKind::Trait
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
