/*
Convert Rust HIR/THIR to VIR for verification.

For soundness's sake, be as defensive as possible:
- if we're not prepared to verify a feature of Rust, disallow the feature
- explicitly match all fields of the Rust AST so we catch any features added in the future
*/

use crate::attributes::get_verifier_attrs;
use crate::context::Context;
use crate::rust_to_vir_adts::{check_item_enum, check_item_struct, check_item_union};
use crate::rust_to_vir_base::{
    check_generics_bounds, def_id_to_vir_path, mid_ty_to_vir, mk_visibility,
    process_predicate_bounds, typ_path_and_ident_to_vir_path,
};
use crate::rust_to_vir_func::{check_foreign_item_fn, check_item_fn, CheckItemFnEither};
use crate::rust_to_vir_global::TypIgnoreImplPaths;
use crate::util::{err_span, unsupported_err_span};
use crate::verus_items::{self, MarkerItem, RustItem, VerusItem};
use crate::{err_unless, unsupported_err, unsupported_err_unless};

use rustc_ast::IsAuto;
use rustc_hir::{
    AssocItemKind, ForeignItem, ForeignItemId, ForeignItemKind, ImplItemKind, Item, ItemId,
    ItemKind, MaybeOwner, Mutability, OpaqueTy, OpaqueTyOrigin, OwnerNode, QPath, TraitFn,
    TraitItem, TraitItemKind, TraitRef, Unsafety,
};
use vir::def::trait_self_type_param;

use std::collections::HashMap;
use std::sync::Arc;
use vir::ast::{Fun, FunX, FunctionKind, Krate, KrateX, Path, Typ, VirErr};

fn check_item<'tcx>(
    ctxt: &Context<'tcx>,
    vir: &mut KrateX,
    mpath: Option<&Option<Path>>,
    id: &ItemId,
    item: &'tcx Item<'tcx>,
) -> Result<(), VirErr> {
    // delay computation of module_path because some external or builtin items don't have a valid Path
    let module_path = || {
        if let Some(Some(path)) = mpath {
            path.clone()
        } else {
            let owned_by = ctxt.krate.owners[item.hir_id().owner.def_id]
                .as_owner()
                .as_ref()
                .expect("owner of item")
                .node();
            def_id_to_vir_path(ctxt.tcx, &ctxt.verus_items, owned_by.def_id().to_def_id())
        }
    };

    let attrs = ctxt.tcx.hir().attrs(item.hir_id());
    let vattrs = get_verifier_attrs(attrs, Some(&mut *ctxt.diagnostics.borrow_mut()))?;
    if vattrs.internal_reveal_fn {
        return Ok(());
    }
    if vattrs.external_fn_specification && !matches!(&item.kind, ItemKind::Fn(..)) {
        return err_span(item.span, "`external_fn_specification` attribute not supported here");
    }
    if vattrs.external_type_specification && !matches!(&item.kind, ItemKind::Struct(..)) {
        if matches!(&item.kind, ItemKind::Enum(..)) {
            return err_span(
                item.span,
                "`external_type_specification` proxy type should use a struct with a single field to declare the external type (even if the external type is an enum)",
            );
        } else {
            return err_span(
                item.span,
                "`external_type_specification` attribute not supported here",
            );
        }
    }

    let visibility = || mk_visibility(ctxt, item.owner_id.to_def_id());

    let mut handle_const_or_static = |body_id: &rustc_hir::BodyId| {
        let def_id = body_id.hir_id.owner.to_def_id();
        let path = def_id_to_vir_path(ctxt.tcx, &ctxt.verus_items, def_id);
        if vattrs.size_of_global {
            return Ok(()); // handled earlier
        }
        if path.segments.iter().find(|s| s.starts_with("_DERIVE_builtin_Structural_FOR_")).is_some()
        {
            ctxt.erasure_info
                .borrow_mut()
                .ignored_functions
                .push((item.owner_id.to_def_id(), item.span.data()));
            return Ok(());
        }

        let mid_ty = ctxt.tcx.type_of(def_id).skip_binder();
        let vir_ty = mid_ty_to_vir(ctxt.tcx, &ctxt.verus_items, def_id, item.span, &mid_ty, false)?;

        crate::rust_to_vir_func::check_item_const_or_static(
            ctxt,
            vir,
            item.span,
            item.owner_id.to_def_id(),
            visibility(),
            &module_path(),
            ctxt.tcx.hir().attrs(item.hir_id()),
            &vir_ty,
            body_id,
            matches!(item.kind, ItemKind::Static(_, _, _)),
        )
    };

    match &item.kind {
        ItemKind::Fn(sig, generics, body_id) => {
            check_item_fn(
                ctxt,
                &mut vir.functions,
                item.owner_id.to_def_id(),
                FunctionKind::Static,
                visibility(),
                &module_path(),
                ctxt.tcx.hir().attrs(item.hir_id()),
                sig,
                None,
                generics,
                CheckItemFnEither::BodyId(body_id),
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

            if vattrs.is_external(&ctxt.cmd_line_args) {
                if vattrs.external_type_specification {
                    return err_span(
                        item.span,
                        "a type cannot be marked both `external_type_specification` and `external`",
                    );
                }

                let def_id = id.owner_id.to_def_id();
                let path = def_id_to_vir_path(ctxt.tcx, &ctxt.verus_items, def_id);
                vir.external_types.push(path);

                return Ok(());
            }

            let tyof = ctxt.tcx.type_of(item.owner_id.to_def_id()).skip_binder();
            let adt_def = tyof.ty_adt_def().expect("adt_def");

            check_item_struct(
                ctxt,
                vir,
                &module_path(),
                item.span,
                id,
                visibility(),
                ctxt.tcx.hir().attrs(item.hir_id()),
                variant_data,
                generics,
                adt_def,
            )?;
        }
        ItemKind::Enum(enum_def, generics) => {
            if vattrs.is_external(&ctxt.cmd_line_args) {
                let def_id = id.owner_id.to_def_id();
                let path = def_id_to_vir_path(ctxt.tcx, &ctxt.verus_items, def_id);
                vir.external_types.push(path);

                return Ok(());
            }

            let tyof = ctxt.tcx.type_of(item.owner_id.to_def_id()).skip_binder();
            let adt_def = tyof.ty_adt_def().expect("adt_def");

            // TODO use rustc_middle? see `Struct` case
            check_item_enum(
                ctxt,
                vir,
                &module_path(),
                item.span,
                id,
                visibility(),
                ctxt.tcx.hir().attrs(item.hir_id()),
                enum_def,
                generics,
                &adt_def,
            )?;
        }
        ItemKind::Union(variant_data, generics) => {
            if vattrs.is_external(&ctxt.cmd_line_args) {
                let def_id = id.owner_id.to_def_id();
                let path = def_id_to_vir_path(ctxt.tcx, &ctxt.verus_items, def_id);
                vir.external_types.push(path);

                return Ok(());
            }

            let tyof = ctxt.tcx.type_of(item.owner_id.to_def_id()).skip_binder();
            let adt_def = tyof.ty_adt_def().expect("adt_def");

            check_item_union(
                ctxt,
                vir,
                &module_path(),
                item.span,
                id,
                visibility(),
                ctxt.tcx.hir().attrs(item.hir_id()),
                variant_data,
                generics,
                &adt_def,
            )?;
        }
        ItemKind::Impl(impll) => {
            let impl_def_id = item.owner_id.to_def_id();
            let impl_path = def_id_to_vir_path(ctxt.tcx, &ctxt.verus_items, impl_def_id);

            if vattrs.is_external(&ctxt.cmd_line_args) {
                return Ok(());
            }
            if impll.unsafety != Unsafety::Normal {
                return err_span(item.span, "the verifier does not support `unsafe` here");
            }

            if let Some(TraitRef { path, hir_ref_id: _ }) = impll.of_trait {
                let trait_def_id = path.res.def_id();

                let rust_item = verus_items::get_rust_item(ctxt.tcx, trait_def_id);
                if matches!(rust_item, Some(RustItem::Fn | RustItem::FnOnce | RustItem::FnMut)) {
                    return err_span(
                        item.span,
                        "Verus does not support implementing this trait via an `impl` block",
                    );
                }

                let verus_item = ctxt.verus_items.id_to_name.get(&trait_def_id);

                let ignore = if let Some(VerusItem::Marker(MarkerItem::Structural)) = verus_item {
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
                        ctxt.tcx.type_of(def_id).skip_binder()
                    };
                    // TODO: this may be a bit of a hack: to query the TyCtxt for the StructuralEq impl it seems we need
                    // a concrete type, so apply ! to all type parameters
                    let ty_kind_applied_never = if let rustc_middle::ty::TyKind::Adt(def, substs) =
                        ty.kind()
                    {
                        rustc_middle::ty::TyKind::Adt(
                            def.to_owned(),
                            ctxt.tcx.mk_args_from_iter(substs.iter().map(|g| match g.unpack() {
                                rustc_middle::ty::GenericArgKind::Type(_) => {
                                    (*ctxt.tcx).types.never.into()
                                }
                                _ => g,
                            })),
                        )
                    } else {
                        panic!("Structural impl for non-adt type");
                    };
                    let ty_applied_never = ctxt.tcx.mk_ty_from_kind(ty_kind_applied_never);
                    err_unless!(
                        ty_applied_never.is_structural_eq_shallow(ctxt.tcx),
                        item.span,
                        format!("structural impl for non-structural type {:?}", ty),
                        ty
                    );
                    true
                } else if let Some(
                    RustItem::StructuralEq
                    | RustItem::StructuralPartialEq
                    | RustItem::PartialEq
                    | RustItem::Eq,
                ) = rust_item
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
                                let impl_item = ctxt.tcx.hir().impl_item(impl_item_ref.id);
                                if let ImplItemKind::Fn(sig, _) = &impl_item.kind {
                                    ctxt.erasure_info
                                        .borrow_mut()
                                        .ignored_functions
                                        .push((impl_item.owner_id.to_def_id(), sig.span.data()));
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

            let trait_path_typ_args = if let Some(TraitRef { path, .. }) = &impll.of_trait {
                let trait_ref =
                    ctxt.tcx.impl_trait_ref(item.owner_id.to_def_id()).expect("impl_trait_ref");
                let trait_did = trait_ref.skip_binder().def_id;
                let impl_paths = crate::rust_to_vir_base::get_impl_paths(
                    ctxt.tcx,
                    &ctxt.verus_items,
                    impl_def_id,
                    trait_did,
                    trait_ref.skip_binder().args,
                );
                // If we have `impl X for Z<A, B, C>` then the list of types is [X, A, B, C].
                // We keep this full list, with the first element being the Self type X
                let mut types: Vec<Typ> = Vec::new();
                for ty in trait_ref.skip_binder().args.types() {
                    types.push(mid_ty_to_vir(
                        ctxt.tcx,
                        &ctxt.verus_items,
                        impl_def_id,
                        impll.generics.span,
                        &ty,
                        false,
                    )?);
                }
                let types = Arc::new(types);
                let path_span = path.span.to(impll.self_ty.span);
                let path = def_id_to_vir_path(ctxt.tcx, &ctxt.verus_items, path.res.def_id());
                let (typ_params, typ_bounds) = crate::rust_to_vir_base::check_generics_bounds_fun(
                    ctxt.tcx,
                    &ctxt.verus_items,
                    impll.generics,
                    impl_def_id,
                    Some(&mut *ctxt.diagnostics.borrow_mut()),
                )?;
                let trait_impl = vir::ast::TraitImplX {
                    impl_path: impl_path.clone(),
                    typ_params,
                    typ_bounds,
                    trait_path: path.clone(),
                    trait_typ_args: types.clone(),
                    trait_typ_arg_impls: ctxt.spanned_new(path_span, impl_paths),
                };
                vir.trait_impls.push(ctxt.spanned_new(item.span, trait_impl));
                Some((trait_ref, path, types))
            } else {
                None
            };

            for impl_item_ref in impll.items {
                match impl_item_ref.kind {
                    AssocItemKind::Fn { has_self: true | false } => {
                        let impl_item = ctxt.tcx.hir().impl_item(impl_item_ref.id);
                        let impl_item_visibility =
                            mk_visibility(&ctxt, impl_item.owner_id.to_def_id());
                        match &impl_item.kind {
                            ImplItemKind::Fn(sig, body_id) => {
                                let fn_attrs = ctxt.tcx.hir().attrs(impl_item.hir_id());
                                let kind = if let Some((_, trait_path, trait_typ_args)) =
                                    trait_path_typ_args.clone()
                                {
                                    let ident = impl_item_ref.ident.to_string();
                                    let ident = Arc::new(ident);
                                    let path = typ_path_and_ident_to_vir_path(&trait_path, ident);
                                    let fun = FunX { path };
                                    let method = Arc::new(fun);
                                    FunctionKind::TraitMethodImpl {
                                        method,
                                        impl_path: impl_path.clone(),
                                        trait_path,
                                        trait_typ_args,
                                    }
                                } else {
                                    FunctionKind::Static
                                };
                                check_item_fn(
                                    ctxt,
                                    &mut vir.functions,
                                    impl_item.owner_id.to_def_id(),
                                    kind,
                                    impl_item_visibility,
                                    &module_path(),
                                    fn_attrs,
                                    sig,
                                    Some((&impll.generics, impl_def_id)),
                                    &impl_item.generics,
                                    CheckItemFnEither::BodyId(body_id),
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
                        let impl_item = ctxt.tcx.hir().impl_item(impl_item_ref.id);
                        if impl_item.generics.params.len() != 0
                            || impl_item.generics.predicates.len() != 0
                            || impl_item.generics.has_where_clause_predicates
                        {
                            unsupported_err!(
                                item.span,
                                "unsupported generics on associated type",
                                impl_item_ref
                            );
                        }
                        if let ImplItemKind::Type(_ty) = impl_item.kind {
                            let name = Arc::new(impl_item.ident.to_string());
                            let ty = ctxt.tcx.type_of(impl_item.owner_id.to_def_id()).skip_binder();
                            let typ = mid_ty_to_vir(
                                ctxt.tcx,
                                &ctxt.verus_items,
                                impl_item.owner_id.to_def_id(),
                                impl_item.span,
                                &ty,
                                false,
                            )?;
                            if let Some((trait_ref, trait_path, trait_typ_args)) =
                                trait_path_typ_args.clone()
                            {
                                let (typ_params, typ_bounds) =
                                    crate::rust_to_vir_base::check_generics_bounds_fun(
                                        ctxt.tcx,
                                        &ctxt.verus_items,
                                        impll.generics,
                                        impl_def_id,
                                        Some(&mut *ctxt.diagnostics.borrow_mut()),
                                    )?;

                                let ai = ctxt.tcx.associated_item(impl_item.owner_id.to_def_id());
                                let bounds = ctxt.tcx.item_bounds(ai.trait_item_def_id.unwrap());
                                let inst_bounds = bounds
                                    .instantiate(ctxt.tcx, &trait_ref.instantiate_identity().args);
                                let param_env = ctxt.tcx.param_env(impl_item.owner_id.to_def_id());
                                let inst_bounds =
                                    ctxt.tcx.normalize_erasing_regions(param_env, inst_bounds);

                                let mut impl_paths = Vec::new();
                                for inst_pred in inst_bounds {
                                    if let rustc_middle::ty::ClauseKind::Trait(_) =
                                        inst_pred.kind().skip_binder()
                                    {
                                        let poly_trait_refs = inst_pred.kind().map_bound(|p| {
                                            if let rustc_middle::ty::ClauseKind::Trait(tp) = &p {
                                                tp.trait_ref
                                            } else {
                                                unreachable!()
                                            }
                                        });
                                        let candidate = ctxt.tcx.codegen_select_candidate((
                                            param_env,
                                            poly_trait_refs.skip_binder(),
                                        ));
                                        if let Ok(impl_source) = candidate {
                                            if let rustc_middle::traits::ImplSource::UserDefined(
                                                u,
                                            ) = impl_source
                                            {
                                                let impl_path = def_id_to_vir_path(
                                                    ctxt.tcx,
                                                    &ctxt.verus_items,
                                                    u.impl_def_id,
                                                );
                                                impl_paths.push(impl_path);
                                            }
                                        }
                                    }
                                }

                                let assocx = vir::ast::AssocTypeImplX {
                                    name,
                                    impl_path: impl_path.clone(),
                                    typ_params,
                                    typ_bounds,
                                    trait_path,
                                    trait_typ_args,
                                    typ,
                                    impl_paths: Arc::new(impl_paths),
                                };
                                vir.assoc_type_impls.push(ctxt.spanned_new(impl_item.span, assocx));
                            } else {
                                unsupported_err!(
                                    item.span,
                                    "unsupported item ref in impl",
                                    impl_item_ref
                                );
                            }
                        } else {
                            unsupported_err!(
                                item.span,
                                "unsupported item ref in impl",
                                impl_item_ref
                            );
                        }
                    }
                    _ => unsupported_err!(item.span, "unsupported item ref in impl", impl_item_ref),
                }
            }
        }
        ItemKind::Static(..)
            if get_verifier_attrs(
                ctxt.tcx.hir().attrs(item.hir_id()),
                Some(&mut *ctxt.diagnostics.borrow_mut()),
            )?
            .is_external(&ctxt.cmd_line_args) =>
        {
            return Ok(());
        }
        ItemKind::Const(_ty, generics, body_id) => {
            unsupported_err_unless!(
                generics.params.len() == 0 && generics.predicates.len() == 0,
                item.span,
                "const generics"
            );
            handle_const_or_static(body_id)?;
        }
        ItemKind::Static(_ty, Mutability::Not, body_id) => {
            handle_const_or_static(body_id)?;
        }
        ItemKind::Static(_ty, Mutability::Mut, _body_id) => {
            if vattrs.external {
                return Ok(());
            }
            unsupported_err!(item.span, "static mut");
        }
        ItemKind::Macro(_, _) => {}
        ItemKind::Trait(IsAuto::No, Unsafety::Normal, trait_generics, _bounds, trait_items) => {
            if vattrs.is_external(&ctxt.cmd_line_args) {
                return Ok(());
            }

            let trait_def_id = item.owner_id.to_def_id();
            let trait_path = def_id_to_vir_path(ctxt.tcx, &ctxt.verus_items, trait_def_id);
            let (generics_params, typ_bounds) = {
                let (generics_params, mut typ_bounds) = check_generics_bounds(
                    ctxt.tcx,
                    &ctxt.verus_items,
                    trait_generics,
                    false,
                    trait_def_id,
                    None,
                    Some(&mut *ctxt.diagnostics.borrow_mut()),
                )?;
                // Remove the Self: Trait bound introduced by rustc
                Arc::make_mut(&mut typ_bounds).retain(|gb| {
                    match &**gb {
                        vir::ast::GenericBoundX::Trait(bnd, tp) => {
                            if bnd == &trait_path {
                                let gp: Vec<_> = Some(trait_self_type_param())
                                    .into_iter()
                                    .chain(generics_params.iter().map(|(p, _)| p.clone()))
                                    .map(|p| Some(p))
                                    .collect();
                                let tp: Vec<_> = tp
                                    .iter()
                                    .map(|p| match &**p {
                                        vir::ast::TypX::TypParam(p) => Some(p.clone()),
                                        _ => None,
                                    })
                                    .collect();
                                assert_eq!(*tp, *gp);
                                return false;
                            }
                        }
                    }
                    true
                });
                (generics_params, typ_bounds)
            };
            let mut assoc_typs: Vec<vir::ast::Ident> = Vec::new();
            let mut assoc_typs_bounds: Vec<vir::ast::GenericBound> = Vec::new();
            let mut methods: Vec<vir::ast::Function> = Vec::new();
            let mut method_names: Vec<Fun> = Vec::new();
            for trait_item_ref in *trait_items {
                let trait_item = ctxt.tcx.hir().trait_item(trait_item_ref.id);
                let TraitItem {
                    ident,
                    owner_id,
                    generics: item_generics,
                    kind,
                    span,
                    defaultness: _,
                } = trait_item;
                let (generics_params, generics_bnds) = check_generics_bounds(
                    ctxt.tcx,
                    &ctxt.verus_items,
                    item_generics,
                    false,
                    owner_id.to_def_id(),
                    None,
                    Some(&mut *ctxt.diagnostics.borrow_mut()),
                )?;
                unsupported_err_unless!(generics_params.len() == 0, *span, "trait generics");
                unsupported_err_unless!(generics_bnds.len() == 0, *span, "trait generics");
                match kind {
                    TraitItemKind::Fn(sig, fun) => {
                        let body_id = match fun {
                            TraitFn::Provided(body_id) => CheckItemFnEither::BodyId(body_id),
                            TraitFn::Required(param_names) => {
                                CheckItemFnEither::ParamNames(*param_names)
                            }
                        };
                        let attrs = ctxt.tcx.hir().attrs(trait_item.hir_id());
                        let fun = check_item_fn(
                            ctxt,
                            &mut methods,
                            owner_id.to_def_id(),
                            FunctionKind::TraitMethodDecl { trait_path: trait_path.clone() },
                            visibility(),
                            &module_path(),
                            attrs,
                            sig,
                            Some((trait_generics, trait_def_id)),
                            item_generics,
                            body_id,
                        )?;
                        if let Some(fun) = fun {
                            method_names.push(fun);
                        }
                    }
                    TraitItemKind::Type([], None) => {
                        assoc_typs.push(Arc::new(ident.to_string()));
                    }
                    TraitItemKind::Type(_, Some(_)) => {
                        return err_span(
                            item.span,
                            "Verus does not yet support associated types with a concrete type",
                        );
                    }
                    TraitItemKind::Type(_generic_bounds, None) => {
                        assoc_typs.push(Arc::new(ident.to_string()));

                        let bounds = ctxt
                            .tcx
                            .item_bounds(trait_item.owner_id.def_id.to_def_id())
                            .skip_binder();
                        let bounds = bounds.iter().map(|p| (p, *span)).collect::<Vec<_>>();
                        let vir_bounds = process_predicate_bounds(
                            ctxt.tcx,
                            trait_def_id,
                            &ctxt.verus_items,
                            bounds.iter(),
                        )?;
                        assoc_typs_bounds.extend(vir_bounds);
                    }
                    TraitItemKind::Const(_, _) => {
                        return err_span(
                            item.span,
                            "Verus does not yet support associated constants",
                        );
                    }
                }
            }
            let mut methods = vir::headers::make_trait_decls(methods)?;
            vir.functions.append(&mut methods);
            let traitx = vir::ast::TraitX {
                name: trait_path,
                visibility: visibility(),
                methods: Arc::new(method_names),
                assoc_typs: Arc::new(assoc_typs),
                typ_params: generics_params,
                typ_bounds,
                assoc_typs_bounds: Arc::new(assoc_typs_bounds),
            };
            vir.traits.push(ctxt.spanned_new(item.span, traitx));
        }
        ItemKind::TyAlias(_ty, _generics) => {
            // type alias (like lines of the form `type X = ...;`
            // Nothing to do here - we can rely on Rust's type resolution to handle these
        }
        ItemKind::GlobalAsm(..) =>
        //TODO(utaal): add a crate-level attribute to enable global_asm
        {
            return Ok(());
        }
        ItemKind::OpaqueTy(OpaqueTy {
            generics: _,
            bounds: _,
            origin: OpaqueTyOrigin::AsyncFn(_),
            in_trait: _,
            lifetime_mapping: _,
        }) => {
            return Ok(());
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
                item.owner_id.to_def_id(),
                item.span,
                mk_visibility(ctxt, item.owner_id.to_def_id()),
                ctxt.tcx.hir().attrs(item.hir_id()),
                decl,
                idents,
                generics,
            )?;
        }
        ForeignItemKind::Static(..)
            if get_verifier_attrs(
                ctxt.tcx.hir().attrs(item.hir_id()),
                Some(&mut *ctxt.diagnostics.borrow_mut()),
            )?
            .is_external(&ctxt.cmd_line_args) =>
        {
            return Ok(());
        }
        _ => {
            unsupported_err!(item.span, "unsupported foreign item", item);
        }
    }
    Ok(())
}

struct VisitMod<'tcx> {
    _tcx: rustc_middle::ty::TyCtxt<'tcx>,
    ids: Vec<ItemId>,
}

impl<'tcx> rustc_hir::intravisit::Visitor<'tcx> for VisitMod<'tcx> {
    type Map = rustc_middle::hir::map::Map<'tcx>;

    fn visit_item(&mut self, item: &'tcx Item<'tcx>) {
        self.ids.push(item.item_id());
        rustc_hir::intravisit::walk_item(self, item);
    }
}

pub fn crate_to_vir<'tcx>(ctxt: &mut Context<'tcx>) -> Result<Krate, VirErr> {
    let mut vir: KrateX = Default::default();

    // Map each item to the module that contains it, or None if the module is external
    let mut item_to_module: HashMap<ItemId, Option<Path>> = HashMap::new();
    for (owner_id, owner_opt) in ctxt.krate.owners.iter_enumerated() {
        if let MaybeOwner::Owner(owner) = owner_opt {
            match owner.node() {
                OwnerNode::Item(item @ Item { kind: ItemKind::Mod(mod_), owner_id, .. }) => {
                    let attrs = ctxt.tcx.hir().attrs(item.hir_id());
                    let vattrs =
                        get_verifier_attrs(attrs, Some(&mut *ctxt.diagnostics.borrow_mut()))?;
                    if vattrs.external {
                        // Recursively mark every item in the module external,
                        // even in nested modules
                        use crate::rustc_hir::intravisit::Visitor;
                        let mut visitor = VisitMod { _tcx: ctxt.tcx, ids: Vec::new() };
                        visitor.visit_item(item);
                        item_to_module.extend(visitor.ids.iter().map(move |ii| (*ii, None)))
                    } else {
                        // Shallowly visit just the top-level items (don't visit nested modules)
                        let path =
                            def_id_to_vir_path(ctxt.tcx, &ctxt.verus_items, owner_id.to_def_id());
                        vir.modules.push(
                            ctxt.spanned_new(item.span, vir::ast::ModuleX { path: path.clone() }),
                        );
                        let path = Some(path);
                        item_to_module
                            .extend(mod_.item_ids.iter().map(move |ii| (*ii, path.clone())))
                    };
                }
                OwnerNode::Crate(mod_) => {
                    let path =
                        def_id_to_vir_path(ctxt.tcx, &ctxt.verus_items, owner_id.to_def_id());
                    vir.modules.push(ctxt.spanned_new(
                        mod_.spans.inner_span,
                        vir::ast::ModuleX { path: path.clone() },
                    ));
                    item_to_module
                        .extend(mod_.item_ids.iter().map(move |ii| (*ii, Some(path.clone()))))
                }
                _ => (),
            }
        }
    }

    let mut typs_sizes_set: HashMap<TypIgnoreImplPaths, u128> = HashMap::new();
    for (_, owner_opt) in ctxt.krate.owners.iter_enumerated() {
        if let MaybeOwner::Owner(owner) = owner_opt {
            match owner.node() {
                OwnerNode::Item(item) => {
                    crate::rust_to_vir_global::process_const_early(
                        ctxt,
                        &mut typs_sizes_set,
                        item,
                    )?;
                }
                _ => (),
            }
        }
    }
    {
        let ctxt = Arc::make_mut(ctxt);
        let arch_word_bits = ctxt.arch_word_bits.unwrap_or(vir::ast::ArchWordBits::Either32Or64);
        ctxt.arch_word_bits = Some(arch_word_bits);
        vir.arch.word_bits = arch_word_bits;
    }
    for owner in ctxt.krate.owners.iter() {
        if let MaybeOwner::Owner(owner) = owner {
            match owner.node() {
                OwnerNode::Item(item) => {
                    // If the item does not belong to a module, use the def_id of its owner as the
                    // module path
                    let mpath = item_to_module.get(&item.item_id());
                    if let Some(None) = mpath {
                        // whole module is external, so skip the item
                        continue;
                    }
                    check_item(ctxt, &mut vir, mpath, &item.item_id(), item)?
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
                    ImplItemKind::Type(_ty) => {
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

    let erasure_info = ctxt.erasure_info.borrow();
    vir.external_fns = erasure_info.external_functions.clone();
    vir.path_as_rust_names = vir::ast_util::get_path_as_rust_names_for_krate(&ctxt.vstd_crate_name);

    Ok(Arc::new(vir))
}
