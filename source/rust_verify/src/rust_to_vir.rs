/*
Convert Rust HIR/THIR to VIR for verification.

For soundness's sake, be as defensive as possible:
- if we're not prepared to verify a feature of Rust, disallow the feature
- explicitly match all fields of the Rust AST so we catch any features added in the future
*/

use crate::context::Context;
use crate::reveal_hide::handle_reveal_hide;
use crate::rust_to_vir_adts::{check_item_enum, check_item_struct, check_item_union};
use crate::rust_to_vir_base::{
    def_id_to_vir_path, mid_ty_to_vir, mk_visibility, typ_path_and_ident_to_vir_path,
};
use crate::rust_to_vir_func::{check_foreign_item_fn, check_item_fn, CheckItemFnEither};
use crate::rust_to_vir_global::TypIgnoreImplPaths;
use crate::util::{err_span, unsupported_err_span};
use crate::verus_items::{self, MarkerItem, RustItem, VerusItem};
use crate::{err_unless, unsupported_err, unsupported_err_unless};

use rustc_ast::IsAuto;
use rustc_hir::def_id::DefId;
use rustc_hir::{
    AssocItemKind, ForeignItem, ForeignItemId, ForeignItemKind, ImplItemKind, Item, ItemId,
    ItemKind, MaybeOwner, Mutability, OpaqueTy, OpaqueTyOrigin, OwnerNode, QPath, TraitRef,
    Unsafety,
};
use vir::def::Spanned;

use indexmap::{IndexMap, IndexSet};
use std::collections::HashMap;
use std::sync::Arc;
use vir::ast::{
    Fun, FunX, Function, FunctionKind, ImplPath, Krate, KrateX, Path, Trait, TraitImpl, Typ, Typs,
    VirErr,
};

fn check_item<'tcx>(
    ctxt: &Context<'tcx>,
    vir: &mut KrateX,
    mpath: Option<&Option<Path>>,
    id: &ItemId,
    item: &'tcx Item<'tcx>,
    external_fn_specification_trait_method_impls: &mut Vec<(DefId, rustc_span::Span)>,
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
    let vattrs = ctxt.get_verifier_attrs(attrs)?;
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
    if vattrs.is_external(&ctxt.cmd_line_args)
        && crate::rust_to_vir_base::def_id_to_vir_path_option(
            ctxt.tcx,
            Some(&ctxt.verus_items),
            item.owner_id.to_def_id(),
        )
        .is_none()
    {
        // If the path of an external item would cause a panic in def_id_to_vir_path,
        // ignore it completely to avoid a panic (potentially leading to less informative
        // error messages to users if they try to access the external item directly from Verus code)
        return Ok(());
    }

    let visibility = || mk_visibility(ctxt, item.owner_id.to_def_id());

    let mut handle_const_or_static = |body_id: &rustc_hir::BodyId| {
        let def_id = body_id.hir_id.owner.to_def_id();
        let path = def_id_to_vir_path(ctxt.tcx, &ctxt.verus_items, def_id);
        if vattrs.size_of_global {
            return Ok(()); // handled earlier
        }
        if vattrs.item_broadcast_use {
            let err = crate::util::err_span(item.span, "invalid module-level broadcast use");
            let ItemKind::Const(_ty, generics, body_id) = item.kind else {
                return err;
            };
            unsupported_err_unless!(
                generics.params.len() == 0 && generics.predicates.len() == 0,
                item.span,
                "const generics with broadcast"
            );
            let _def_id = body_id.hir_id.owner.to_def_id();

            let body = crate::rust_to_vir_func::find_body(ctxt, &body_id);

            let rustc_hir::ExprKind::Block(block, _) = body.value.kind else {
                return err;
            };

            let funs = block
                .stmts
                .iter()
                .map(|stmt| {
                    let err =
                        crate::util::err_span(item.span, "invalid module-level broadcast use");

                    let rustc_hir::StmtKind::Semi(expr) = stmt.kind else {
                        return err;
                    };

                    let rustc_hir::ExprKind::Call(fun_target, args) = expr.kind else {
                        return err;
                    };

                    let rustc_hir::ExprKind::Path(rustc_hir::QPath::Resolved(None, fun_path)) =
                        &fun_target.kind
                    else {
                        return err;
                    };

                    let Some(VerusItem::Directive(verus_items::DirectiveItem::RevealHide)) =
                        ctxt.get_verus_item(fun_path.res.def_id())
                    else {
                        return err;
                    };

                    let args: Vec<_> = args.iter().collect();

                    let crate::reveal_hide::RevealHideResult::RevealItem(fun) = handle_reveal_hide(
                        ctxt,
                        expr,
                        args.len(),
                        &args,
                        ctxt.tcx,
                        None::<fn(vir::ast::ExprX) -> Result<vir::ast::Expr, VirErr>>,
                    )?
                    else {
                        panic!("handle_reveal_hide must return a RevealItem");
                    };

                    Ok(fun)
                })
                .collect::<Result<Vec<_>, _>>()?;

            let Some(Some(mpath)) = mpath else {
                unsupported_err!(item.span, "unsupported broadcast use here", item);
            };
            let module = vir
                .modules
                .iter_mut()
                .find(|m| &m.x.path == mpath)
                .expect("cannot find current module");
            let reveals = &mut Arc::make_mut(module).x.reveals;
            if reveals.is_some() {
                return err_span(
                    item.span,
                    "only one module-level `broadcast use` allowed for each module",
                );
            }
            let span = crate::spans::err_air_span(item.span);
            *reveals = Some(Spanned::new(span, funs));

            return Ok(());
        }
        if path.segments.iter().find(|s| s.starts_with("_DERIVE_builtin_Structural_FOR_")).is_some()
        {
            ctxt.erasure_info
                .borrow_mut()
                .ignored_functions
                .push((item.owner_id.to_def_id(), item.span.data()));
            return Ok(());
        }

        if vattrs.is_external(&ctxt.cmd_line_args) {
            let mut erasure_info = ctxt.erasure_info.borrow_mut();
            let path = def_id_to_vir_path(ctxt.tcx, &ctxt.verus_items, item.owner_id.to_def_id());
            let name = Arc::new(FunX { path: path.clone() });
            erasure_info.external_functions.push(name);
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
                Some(&mut vir.reveal_groups),
                item.owner_id.to_def_id(),
                FunctionKind::Static,
                visibility(),
                &module_path(),
                ctxt.tcx.hir().attrs(item.hir_id()),
                sig,
                None,
                generics,
                CheckItemFnEither::BodyId(body_id),
                None,
                None,
                external_fn_specification_trait_method_impls,
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
                adt_def,
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
                adt_def,
            )?;
        }
        ItemKind::Impl(impll) => {
            let impl_def_id = item.owner_id.to_def_id();
            let impl_path = def_id_to_vir_path(ctxt.tcx, &ctxt.verus_items, impl_def_id);

            if vattrs.is_external(&ctxt.cmd_line_args) {
                return Ok(());
            }

            if impll.unsafety != Unsafety::Normal && impll.of_trait.is_none() {
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

                /* sealed, `unsafe` */
                {
                    let trait_attrs = ctxt.tcx.get_attrs_unchecked(trait_def_id);
                    let sealed = crate::attributes::is_sealed(
                        trait_attrs,
                        Some(&mut *ctxt.diagnostics.borrow_mut()),
                    )?;

                    if sealed {
                        return err_span(item.span, "cannot implement `sealed` trait");
                    } else if impll.unsafety != Unsafety::Normal {
                        return err_span(item.span, "the verifier does not support `unsafe` here");
                    }
                }

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
                let impl_def_id = item.owner_id.to_def_id();
                let path_span = path.span.to(impll.self_ty.span);
                let (trait_path, types, trait_impl) = trait_impl_to_vir(
                    ctxt,
                    item.span,
                    path_span,
                    impl_def_id,
                    Some(impll.generics),
                    module_path(),
                )?;
                vir.trait_impls.push(trait_impl);
                let trait_ref = ctxt.tcx.impl_trait_ref(impl_def_id).expect("impl_trait_ref");
                Some((trait_ref, trait_path, types))
            } else {
                None
            };

            for impl_item_ref in impll.items {
                let impl_item = ctxt.tcx.hir().impl_item(impl_item_ref.id);
                let fn_attrs = ctxt.tcx.hir().attrs(impl_item.hir_id());
                if trait_path_typ_args.is_some() {
                    let vattrs = ctxt.get_verifier_attrs(fn_attrs)?;
                    if vattrs.external {
                        return err_span(
                            item.span,
                            "an item in a trait impl cannot be marked external - you can either use external_body, or mark the entire trait impl as external",
                        );
                    }
                }

                match impl_item_ref.kind {
                    AssocItemKind::Fn { has_self: true | false } => {
                        let impl_item_visibility =
                            mk_visibility(&ctxt, impl_item.owner_id.to_def_id());
                        match &impl_item.kind {
                            ImplItemKind::Fn(sig, body_id) => {
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
                                        inherit_body_from: None,
                                    }
                                } else {
                                    FunctionKind::Static
                                };
                                check_item_fn(
                                    ctxt,
                                    &mut vir.functions,
                                    Some(&mut vir.reveal_groups),
                                    impl_item.owner_id.to_def_id(),
                                    kind,
                                    impl_item_visibility,
                                    &module_path(),
                                    fn_attrs,
                                    sig,
                                    Some((&impll.generics, impl_def_id)),
                                    &impl_item.generics,
                                    CheckItemFnEither::BodyId(body_id),
                                    None,
                                    None,
                                    external_fn_specification_trait_method_impls,
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
                                    crate::rust_to_vir_base::check_generics_bounds_no_polarity(
                                        ctxt.tcx,
                                        &ctxt.verus_items,
                                        impll.generics.span,
                                        Some(impll.generics),
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
                                                impl_paths.push(ImplPath::TraitImplPath(impl_path));
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
            if ctxt
                .get_verifier_attrs(ctxt.tcx.hir().attrs(item.hir_id()))?
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
            if vattrs.is_external(&ctxt.cmd_line_args) {
                return Ok(());
            }
            unsupported_err!(item.span, "static mut");
        }
        ItemKind::Macro(_, _) => {}
        ItemKind::Trait(IsAuto::No, Unsafety::Normal, trait_generics, _bounds, trait_items) => {
            if vattrs.is_external(&ctxt.cmd_line_args) {
                if vattrs.external_trait_specification.is_some() {
                    return err_span(
                        item.span,
                        "a trait cannot be marked both `external_trait_specification` and `external`",
                    );
                }
                return Ok(());
            }

            let trait_def_id = item.owner_id.to_def_id();
            crate::rust_to_vir_trait::translate_trait(
                ctxt,
                vir,
                item.span,
                trait_def_id,
                visibility(),
                &module_path(),
                trait_generics,
                trait_items,
                &vattrs,
                external_fn_specification_trait_method_impls,
            )?;
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
            if vattrs.is_external(&ctxt.cmd_line_args) {
                return Ok(());
            }
            unsupported_err!(item.span, "unsupported item", item);
        }
    }
    Ok(())
}

fn trait_impl_to_vir<'tcx>(
    ctxt: &Context<'tcx>,
    span: rustc_span::Span,
    path_span: rustc_span::Span,
    impl_def_id: rustc_hir::def_id::DefId,
    hir_generics: Option<&'tcx rustc_hir::Generics<'tcx>>,
    module_path: Path,
) -> Result<(Path, Typs, TraitImpl), VirErr> {
    let trait_ref = ctxt.tcx.impl_trait_ref(impl_def_id).expect("impl_trait_ref");
    let trait_did = trait_ref.skip_binder().def_id;
    let impl_paths = crate::rust_to_vir_base::get_impl_paths(
        ctxt.tcx,
        &ctxt.verus_items,
        impl_def_id,
        trait_did,
        trait_ref.skip_binder().args,
        None,
    );
    // If we have `impl X for Z<A, B, C>` then the list of types is [X, A, B, C].
    // We keep this full list, with the first element being the Self type X
    let mut types: Vec<Typ> = Vec::new();
    for ty in trait_ref.skip_binder().args.types() {
        types.push(mid_ty_to_vir(ctxt.tcx, &ctxt.verus_items, impl_def_id, span, &ty, false)?);
    }
    let types = Arc::new(types);
    let trait_path = def_id_to_vir_path(ctxt.tcx, &ctxt.verus_items, trait_did);
    let (typ_params, typ_bounds) = crate::rust_to_vir_base::check_generics_bounds_no_polarity(
        ctxt.tcx,
        &ctxt.verus_items,
        span,
        hir_generics,
        impl_def_id,
        Some(&mut *ctxt.diagnostics.borrow_mut()),
    )?;
    let impl_path = def_id_to_vir_path(ctxt.tcx, &ctxt.verus_items, impl_def_id);
    let trait_impl = vir::ast::TraitImplX {
        impl_path: impl_path.clone(),
        typ_params,
        typ_bounds,
        trait_path: trait_path.clone(),
        trait_typ_args: types.clone(),
        trait_typ_arg_impls: ctxt.spanned_new(path_span, impl_paths),
        owning_module: Some(module_path),
    };
    let trait_impl = ctxt.spanned_new(span, trait_impl);
    Ok((trait_path, types, trait_impl))
}

fn collect_external_trait_impls<'tcx>(
    ctxt: &Context<'tcx>,
    krate: &mut KrateX,
    external_fn_specification_trait_method_impls: &Vec<(DefId, rustc_span::Span)>,
) -> Result<(), VirErr> {
    if external_fn_specification_trait_method_impls.len() == 0 {
        return Ok(());
    }

    let mut func_map = HashMap::<Fun, Function>::new();
    for function in krate.functions.iter() {
        func_map.insert(function.x.name.clone(), function.clone());
    }
    let mut trait_map = HashMap::<Path, Trait>::new();
    for traitt in krate.traits.iter() {
        trait_map.insert(traitt.x.name.clone(), traitt.clone());
    }

    let mut new_trait_impls = IndexMap::<Path, (DefId, Vec<(DefId, rustc_span::Span)>)>::new();

    for (def_id, span) in external_fn_specification_trait_method_impls.iter() {
        let trait_method_impl = def_id_to_vir_path(ctxt.tcx, &ctxt.verus_items, *def_id);
        let trait_impl = trait_method_impl.pop_segment();
        match new_trait_impls.get_mut(&trait_impl) {
            Some(m) => {
                m.1.push((*def_id, *span));
            }
            None => {
                let impl_def_id = ctxt.tcx.impl_of_method(*def_id).unwrap();
                new_trait_impls.insert(trait_impl, (impl_def_id, vec![(*def_id, *span)]));
            }
        }
    }

    for (impl_path, (impl_def_id, funs)) in new_trait_impls.iter() {
        let trait_ref = ctxt.tcx.impl_trait_ref(impl_def_id).expect("impl_trait_ref");
        let trait_did = trait_ref.skip_binder().def_id;
        let trait_path = def_id_to_vir_path(ctxt.tcx, &ctxt.verus_items, trait_did);
        let Some(traitt) = trait_map.get(&trait_path) else {
            continue;
        };

        let span = funs[0].1;

        let mut methods_we_have = IndexSet::<vir::ast::Ident>::new();
        for (fun_def_id, fun_span) in funs.iter() {
            let path = def_id_to_vir_path(ctxt.tcx, &ctxt.verus_items, *fun_def_id);
            if !methods_we_have.insert(path.last_segment()) {
                return err_span(*fun_span, "duplicate external_fn_specification for this method");
            }
        }

        if traitt.x.assoc_typs_bounds.len() > 0 {
            return err_span(
                span,
                "not supported: using external_fn_specification for a trait method impl where the trait has associated types",
            );
        }
        for method in traitt.x.methods.iter() {
            if !methods_we_have.contains::<vir::ast::Ident>(&method.path.last_segment()) {
                return err_span(
                    span,
                    format!(
                        "using external_fn_specification for this function requires you to specify all other functions for the same trait impl, but the method `{:}` is missing",
                        method.path.last_segment()
                    ),
                );
            }
        }

        let module_path = impl_path.pop_segment();

        let (_trait_path, _types, trait_impl) =
            trait_impl_to_vir(ctxt, span, span, *impl_def_id, None, module_path)?;
        krate.trait_impls.push(trait_impl);
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
        _ => {
            if ctxt
                .get_verifier_attrs(ctxt.tcx.hir().attrs(item.hir_id()))?
                .is_external(&ctxt.cmd_line_args)
            {
                return Ok(());
            } else {
                unsupported_err!(item.span, "unsupported foreign item", item);
            }
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
    type NestedFilter = rustc_middle::hir::nested_filter::All;

    fn nested_visit_map(&mut self) -> Self::Map {
        self._tcx.hir()
    }

    fn visit_item(&mut self, item: &'tcx Item<'tcx>) {
        self.ids.push(item.item_id());
        rustc_hir::intravisit::walk_item(self, item);
    }
}

pub type ItemToModuleMap = HashMap<ItemId, Option<Path>>;

pub fn crate_to_vir<'tcx>(ctxt: &mut Context<'tcx>) -> Result<(Krate, ItemToModuleMap), VirErr> {
    let mut vir: KrateX = KrateX {
        functions: Vec::new(),
        reveal_groups: Vec::new(),
        datatypes: Vec::new(),
        traits: Vec::new(),
        trait_impls: Vec::new(),
        assoc_type_impls: Vec::new(),
        modules: Vec::new(),
        external_fns: Vec::new(),
        external_types: Vec::new(),
        path_as_rust_names: Vec::new(),
        arch: vir::ast::Arch { word_bits: vir::ast::ArchWordBits::Either32Or64 },
    };

    let mut external_fn_specification_trait_method_impls = vec![];

    // Map each item to the module that contains it, or None if the module is external
    let mut item_to_module: HashMap<ItemId, Option<Path>> = HashMap::new();
    for (owner_id, owner_opt) in ctxt.krate.owners.iter_enumerated() {
        if let MaybeOwner::Owner(owner) = owner_opt {
            match owner.node() {
                OwnerNode::Item(item @ Item { kind: ItemKind::Mod(mod_), owner_id, .. }) => {
                    let attrs = ctxt.tcx.hir().attrs(item.hir_id());
                    let vattrs = ctxt.get_verifier_attrs(attrs)?;
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
                        vir.modules.push(ctxt.spanned_new(
                            item.span,
                            vir::ast::ModuleX { path: path.clone(), reveals: None },
                        ));
                        let path = Some(path);
                        item_to_module
                            .extend(mod_.item_ids.iter().map(move |ii| (*ii, path.clone())))
                    };
                }
                OwnerNode::Item(item @ Item { kind: _, owner_id: _, .. }) => {
                    // If we have something like:
                    //    #[verifier::external_body]
                    //    fn test() {
                    //        fn nested_item() { ... }
                    //    }
                    // Then we need to make sure nested_item() gets marked external.
                    let attrs = ctxt.tcx.hir().attrs(item.hir_id());
                    let vattrs = ctxt.get_verifier_attrs(attrs)?;
                    if vattrs.external || vattrs.external_body {
                        use crate::rustc_hir::intravisit::Visitor;
                        let mut visitor = VisitMod { _tcx: ctxt.tcx, ids: Vec::new() };
                        visitor.visit_item(item);
                        item_to_module.extend(visitor.ids.iter().skip(1).map(move |ii| (*ii, None)))
                    }
                }
                OwnerNode::Crate(mod_) => {
                    let path =
                        def_id_to_vir_path(ctxt.tcx, &ctxt.verus_items, owner_id.to_def_id());
                    vir.modules.push(ctxt.spanned_new(
                        mod_.spans.inner_span,
                        vir::ast::ModuleX { path: path.clone(), reveals: None },
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
                    check_item(
                        ctxt,
                        &mut vir,
                        mpath,
                        &item.item_id(),
                        item,
                        &mut external_fn_specification_trait_method_impls,
                    )?
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
                        let attrs = ctxt.tcx.hir().attrs(impl_item.hir_id());
                        let vattrs = ctxt.get_verifier_attrs(attrs)?;
                        if !vattrs.is_external(&ctxt.cmd_line_args) {
                            unsupported_err!(impl_item.span, "unsupported_impl_item", impl_item);
                        }
                    }
                },
                OwnerNode::Crate(_mod_) => (),
            }
        }
    }

    let erasure_info = ctxt.erasure_info.borrow();
    vir.external_fns = erasure_info.external_functions.clone();
    vir.path_as_rust_names = vir::ast_util::get_path_as_rust_names_for_krate(&ctxt.vstd_crate_name);

    collect_external_trait_impls(ctxt, &mut vir, &external_fn_specification_trait_method_impls)?;

    Ok((Arc::new(vir), item_to_module))
}
