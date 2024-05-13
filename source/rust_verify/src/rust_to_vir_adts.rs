use crate::attributes::{get_mode, VerifierAttrs};
use crate::context::Context;
use crate::rust_to_vir_base::{
    check_generics_bounds_with_polarity, def_id_to_vir_path, mid_ty_to_vir, mk_visibility,
    mk_visibility_from_vis,
};
use crate::rust_to_vir_impl::ExternalInfo;
use crate::unsupported_err_unless;
use crate::util::err_span;
use air::ast_util::str_ident;
use rustc_ast::Attribute;
use rustc_hir::{EnumDef, Generics, ItemId, VariantData};
use rustc_middle::ty::{GenericArgsRef, TyKind};
use rustc_span::Span;
use std::collections::HashMap;
use std::sync::Arc;
use vir::ast::{
    CtorPrintStyle, Datatype, DatatypeTransparency, DatatypeX, Fun, Function, Ident, KrateX, Mode,
    Path, TypX, Variant, VirErr,
};
use vir::ast_util::ident_binder;
use vir::def::field_ident_from_rust;

// The `rustc_hir::VariantData` is optional here because we won't have it available
// when handling external datatype definitions.
// Therefore, we need to get most of the information from rustc_middle.
// Luckily, the only thing we need the rustc_hir for is modes,
// and for external definitions, all the modes will be 'exec', so it's
// fine that we don't have the rustc_hir data in that case.

fn check_variant_data<'tcx, 'fd>(
    span: Span,
    ctxt: &Context<'tcx>,
    item_id: &ItemId,
    name: &Ident,
    variant_data_opt: Option<&'tcx rustc_hir::VariantData<'tcx>>,
    variant_def: &'tcx rustc_middle::ty::VariantDef,
    substs: Option<GenericArgsRef<'tcx>>,
    visibility: &vir::ast::Visibility,
) -> Result<(Variant, vir::ast::Visibility), VirErr>
where
    'tcx: 'fd,
{
    let empty = [];
    let hir_fields_opt = match variant_data_opt {
        Some(VariantData::Struct { fields, recovered }) => {
            // 'recovered' means that it was recovered from a syntactic error.
            // So we shouldn't get to this point if 'recovered' is true.
            unsupported_err_unless!(!recovered, span, "recovered_struct", variant_data_opt);
            Some(*fields)
        }
        Some(VariantData::Tuple(fields, _variant_id, _local_def_id)) => Some(*fields),
        Some(VariantData::Unit(_variant_id, _local_def_id)) => Some(&empty[..]),
        None => None,
    };

    let mut idx = 0;
    let mut vir_fields = vec![];
    let mut inner_vis = visibility.clone();

    for field_def in variant_def.fields.iter() {
        let hir_field_def_opt = hir_fields_opt.map(|hf| &hf[idx]);

        let field_def_ident = field_def.ident(ctxt.tcx);
        if let Some(hir_field_def) = hir_field_def_opt {
            assert!(hir_field_def.ident.name == field_def_ident.name);
        }
        let field_ty = match substs {
            Some(substs) => {
                // For external types, we need to substitute in the generics
                // from the proxy type
                field_def.ty(ctxt.tcx, substs)
            }
            None => {
                // For normal datatypes, this seems to work fine.
                ctxt.tcx.type_of(field_def.did).skip_binder()
            }
        };

        let ident = field_ident_from_rust(&field_def_ident.as_str());

        let typ = mid_ty_to_vir(
            ctxt.tcx,
            &ctxt.verus_items,
            item_id.owner_id.to_def_id(),
            span,
            &field_ty,
            false,
        )?;
        let mode = match hir_field_def_opt {
            Some(hir_field_def) => get_mode(Mode::Exec, ctxt.tcx.hir().attrs(hir_field_def.hir_id)),
            None => Mode::Exec,
        };
        let vis = mk_visibility_from_vis(ctxt, field_def.vis);
        inner_vis = inner_vis.join(&vis);
        let field = (typ, mode, vis);
        let vir_field = ident_binder(&ident, &field);

        vir_fields.push(vir_field);

        idx += 1;
    }
    if let Some(hir_fields) = hir_fields_opt {
        assert!(idx == hir_fields.len());
    }

    let vir_fields_binder = Variant {
        name: name.clone(),
        fields: Arc::new(vir_fields),
        ctor_style: get_ctor_print_style(variant_def),
    };
    Ok((vir_fields_binder, inner_vis))
}

fn get_ctor_print_style(variant_def: &rustc_middle::ty::VariantDef) -> CtorPrintStyle {
    match variant_def.ctor_kind() {
        None => CtorPrintStyle::Braces,
        Some(rustc_hir::def::CtorKind::Fn) => CtorPrintStyle::Parens,
        Some(rustc_hir::def::CtorKind::Const) => CtorPrintStyle::Const,
    }
}

pub(crate) fn check_item_struct<'tcx>(
    ctxt: &Context<'tcx>,
    vir: &mut KrateX,
    module_path: &Path,
    span: Span,
    id: &ItemId,
    visibility: vir::ast::Visibility,
    attrs: &[Attribute],
    variant_data: &'tcx VariantData<'tcx>,
    generics: &'tcx Generics<'tcx>,
    adt_def: rustc_middle::ty::AdtDef<'tcx>,
    external_info: &mut ExternalInfo,
) -> Result<(), VirErr> {
    assert!(adt_def.is_struct());
    let vattrs = ctxt.get_verifier_attrs(attrs)?;

    if vattrs.external_type_specification {
        return check_item_external(
            ctxt,
            vir,
            module_path,
            span,
            id,
            visibility,
            attrs,
            &vattrs,
            generics,
            adt_def,
            external_info,
        );
    }

    let def_id = id.owner_id.to_def_id();
    let (typ_params, typ_bounds) = check_generics_bounds_with_polarity(
        ctxt.tcx,
        &ctxt.verus_items,
        generics.span,
        Some(generics),
        vattrs.external_body,
        def_id,
        Some(&vattrs),
        Some(&mut *ctxt.diagnostics.borrow_mut()),
    )?;
    let path = def_id_to_vir_path(ctxt.tcx, &ctxt.verus_items, def_id);
    let name = path.segments.last().expect("unexpected struct path");

    let variant_name = name.clone();
    let (variant, transparency) = if vattrs.external_body {
        let variant = Variant {
            name: variant_name,
            fields: Arc::new(vec![]),
            ctor_style: CtorPrintStyle::Braces,
        };
        (variant, DatatypeTransparency::Never)
    } else {
        let (variant, inner_vis) = check_variant_data(
            span,
            ctxt,
            id,
            &variant_name,
            Some(variant_data),
            adt_def.non_enum_variant(),
            None,
            &visibility,
        )?;
        (variant, DatatypeTransparency::WhenVisible(inner_vis))
    };
    let variants = Arc::new(vec![variant]);
    let mode = get_mode(Mode::Exec, attrs);
    let datatype = DatatypeX {
        path,
        proxy: None,
        visibility,
        owning_module: Some(module_path.clone()),
        transparency,
        typ_params,
        typ_bounds,
        variants,
        mode,
        ext_equal: vattrs.ext_equal,
        user_defined_invariant_fn: None,
    };
    vir.datatypes.push(ctxt.spanned_new(span, datatype));
    Ok(())
}

pub fn get_mid_variant_def_by_name<'tcx>(
    ctxt: &Context<'tcx>,
    adt_def: rustc_middle::ty::AdtDef<'tcx>,
    variant_name: &str,
) -> &'tcx rustc_middle::ty::VariantDef {
    for variant_def in adt_def.variants().iter() {
        if variant_def.ident(ctxt.tcx).name.as_str() == variant_name {
            return variant_def;
        }
    }
    panic!("get_mid_variant_def_by_name failed to find variant");
}

pub(crate) fn check_item_enum<'tcx>(
    ctxt: &Context<'tcx>,
    vir: &mut KrateX,
    module_path: &Path,
    span: Span,
    id: &ItemId,
    visibility: vir::ast::Visibility,
    attrs: &[Attribute],
    enum_def: &'tcx EnumDef<'tcx>,
    generics: &'tcx Generics<'tcx>,
    adt_def: rustc_middle::ty::AdtDef<'tcx>,
) -> Result<(), VirErr> {
    assert!(adt_def.is_enum());

    let vattrs = ctxt.get_verifier_attrs(attrs)?;

    if vattrs.external_fn_specification {
        return err_span(span, "`external_fn_specification` attribute not supported here");
    }

    let def_id = id.owner_id.to_def_id();
    let (typ_params, typ_bounds) = check_generics_bounds_with_polarity(
        ctxt.tcx,
        &ctxt.verus_items,
        generics.span,
        Some(generics),
        vattrs.external_body,
        def_id,
        Some(&vattrs),
        Some(&mut *ctxt.diagnostics.borrow_mut()),
    )?;
    let path = def_id_to_vir_path(ctxt.tcx, &ctxt.verus_items, def_id);
    let mut total_vis = visibility.clone();
    let mut variants: Vec<_> = vec![];
    for variant in enum_def.variants.iter() {
        let variant_name = &variant.ident.as_str();
        let variant_def = get_mid_variant_def_by_name(ctxt, adt_def, variant_name);
        let variant_name = str_ident(variant_name);
        let (variant, total_vis2) = check_variant_data(
            variant.span,
            ctxt,
            id,
            &variant_name,
            Some(&variant.data),
            variant_def,
            None,
            &total_vis,
        )?;
        total_vis = total_vis2;
        variants.push(variant);
    }
    let transparency = if vattrs.external_body {
        DatatypeTransparency::Never
    } else {
        DatatypeTransparency::WhenVisible(total_vis)
    };
    vir.datatypes.push(ctxt.spanned_new(
        span,
        DatatypeX {
            path,
            proxy: None,
            visibility,
            owning_module: Some(module_path.clone()),
            transparency,
            typ_params,
            typ_bounds,
            variants: Arc::new(variants),
            mode: get_mode(Mode::Exec, attrs),
            ext_equal: vattrs.ext_equal,
            user_defined_invariant_fn: None,
        },
    ));
    Ok(())
}

pub(crate) fn check_item_union<'tcx>(
    ctxt: &Context<'tcx>,
    vir: &mut KrateX,
    module_path: &Path,
    span: Span,
    id: &ItemId,
    visibility: vir::ast::Visibility,
    attrs: &[Attribute],
    variant_data: &'tcx VariantData<'tcx>,
    generics: &'tcx Generics<'tcx>,
    adt_def: rustc_middle::ty::AdtDef<'tcx>,
) -> Result<(), VirErr> {
    assert!(adt_def.is_union());

    let vattrs = ctxt.get_verifier_attrs(attrs)?;

    if vattrs.external_fn_specification {
        return err_span(span, "`external_fn_specification` attribute not supported here");
    }

    let mode = get_mode(Mode::Exec, attrs);
    if mode != Mode::Exec {
        return err_span(span, "a 'union' can only be exec-mode");
    }
    let VariantData::Struct { fields: hir_fields, recovered: _ } = variant_data else {
        return err_span(span, "check_item_union: wrong VariantData");
    };
    for hir_field_def in hir_fields.iter() {
        let mode = get_mode(Mode::Exec, ctxt.tcx.hir().attrs(hir_field_def.hir_id));
        if mode != Mode::Exec {
            return err_span(span, "a union field can only be exec-mode");
        }
    }

    let def_id = id.owner_id.to_def_id();
    let (typ_params, typ_bounds) = check_generics_bounds_with_polarity(
        ctxt.tcx,
        &ctxt.verus_items,
        generics.span,
        Some(generics),
        vattrs.external_body,
        def_id,
        Some(&vattrs),
        Some(&mut *ctxt.diagnostics.borrow_mut()),
    )?;
    let path = def_id_to_vir_path(ctxt.tcx, &ctxt.verus_items, def_id);

    let (variants, transparency) = if vattrs.external_body {
        let name = path.segments.last().expect("unexpected struct path");
        let variant = Variant {
            name: name.clone(),
            fields: Arc::new(vec![]),
            ctor_style: CtorPrintStyle::Braces,
        };
        (vec![variant], DatatypeTransparency::Never)
    } else {
        let mut variants: Vec<_> = vec![];
        let mut total_vis = visibility.clone();
        assert!(adt_def.variants().len() == 1);
        let variant_def = adt_def.variants().iter().next().unwrap();
        for field_def in variant_def.fields.iter() {
            let variant_name = str_ident(field_def.ident(ctxt.tcx).as_str());
            let field_name = field_ident_from_rust(&variant_name);

            let vis = mk_visibility_from_vis(ctxt, field_def.vis);
            total_vis = total_vis.join(&vis);

            let field_ty = ctxt.tcx.type_of(field_def.did).skip_binder();
            let typ = mid_ty_to_vir(ctxt.tcx, &ctxt.verus_items, def_id, span, &field_ty, false)?;

            let field = (typ, Mode::Exec, vis);
            let variant = Variant {
                name: variant_name,
                fields: Arc::new(vec![ident_binder(&field_name, &field)]),
                ctor_style: get_ctor_print_style(adt_def.non_enum_variant()),
            };
            variants.push(variant);
        }
        (variants, DatatypeTransparency::WhenVisible(total_vis))
    };
    vir.datatypes.push(ctxt.spanned_new(
        span,
        DatatypeX {
            path,
            proxy: None,
            visibility,
            owning_module: Some(module_path.clone()),
            transparency,
            typ_params,
            typ_bounds,
            variants: Arc::new(variants),
            mode: get_mode(Mode::Exec, attrs),
            ext_equal: vattrs.ext_equal,
            user_defined_invariant_fn: None,
        },
    ));
    Ok(())
}

pub(crate) fn check_item_external<'tcx>(
    ctxt: &Context<'tcx>,
    vir: &mut KrateX,
    module_path: &Path,
    span: Span,
    id: &ItemId,
    proxy_visibility: vir::ast::Visibility,
    attrs: &[Attribute],
    vattrs: &VerifierAttrs,
    generics: &'tcx Generics<'tcx>,
    proxy_adt_def: rustc_middle::ty::AdtDef<'tcx>,
    external_info: &mut ExternalInfo,
) -> Result<(), VirErr> {
    // Like with functions, we disallow external_type_specification and external together
    // (This check is done in rust_to_vir)
    //
    // UNLIKE with functions, we DO allow external_type_specification and external_body
    // at the same time.
    //  - Use external_body for types that are treated opaquely (like std::Vec)
    //  - Don't use it for types that should be transparent (like Option, Result)
    //    where we want to have the variants and fields be public.
    // (This is a distinction that doesn't exist for exec functions,
    // whose bodies are never exported.)

    let mode = get_mode(Mode::Exec, attrs);
    if mode != Mode::Exec {
        return err_span(span, "external_type_specification can only be used with exec types");
    }

    // The proxy_adt_def should look like:
    //      struct X(Type);
    // where Type is some external Type that we need to look up
    assert!(proxy_adt_def.is_struct());
    let mut fields_iter = proxy_adt_def.all_fields();
    let first_field = match fields_iter.next() {
        None => {
            return err_span(span, "external_type_specification should look like `struct X(Type)`");
        }
        Some(first_field) => first_field,
    };
    if fields_iter.next().is_some() {
        return err_span(span, "external_type_specification should look like `struct X(Type)`");
    }
    let external_ty = ctxt.tcx.type_of(first_field.did).skip_binder();
    let (external_adt_def, substs_ref) = match external_ty.kind() {
        TyKind::Adt(adt_def, substs_ref) => (adt_def, substs_ref),
        _ => {
            return err_span(
                span,
                "external_type_specification: the external type needs to be a struct or enum",
            );
        }
    };
    if !external_adt_def.is_struct() && !external_adt_def.is_enum() {
        return err_span(
            span,
            "external_type_specification: the external type needs to be a struct or enum",
        );
    }

    if crate::verus_items::get_rust_item(ctxt.tcx, external_adt_def.did())
        == Some(crate::verus_items::RustItem::AllocGlobal)
    {
        // Don't need to add this to the krate, since we handle this as as a VIR Primitive.
        // We only get this far so we can add ourselves to the type_ids list.
        // note: seems that Global is added to lang_items in future version of Rust,
        // which makes it easier to get the ID so we can simplify this.
        external_info.add_type_id(external_adt_def.did());
        return Ok(());
    }

    // Check that the type args match.

    crate::rust_to_vir_base::check_item_external_generics(
        None, generics, false, substs_ref, false, span,
    )?;

    // Check that the trait bounds match.

    let external_predicates = external_adt_def.predicates(ctxt.tcx);
    let proxy_predicates = proxy_adt_def.predicates(ctxt.tcx);
    if !(external_predicates.parent.is_none() && proxy_predicates.parent.is_none()) {
        // I think this error is impossible?
        // 'Parent' nodes should only exist for stuff in an impl
        return err_span(span, "expected GenericPredicates to not have a parent");
    }
    let preds1 = external_predicates.instantiate(ctxt.tcx, substs_ref).predicates;
    let preds2 = proxy_predicates.instantiate(ctxt.tcx, substs_ref).predicates;
    let preds_match = crate::rust_to_vir_func::predicates_match(ctxt.tcx, &preds1, &preds2);
    if !preds_match {
        println!("external_predicates: {:#?}", external_predicates.predicates);
        println!("proxy_predicates: {:#?}", proxy_predicates.predicates);
        return err_span(span, "external_type_specification: trait bounds should match");
    }

    // Check that visibility is okay

    let external_def_id = external_adt_def.did();
    let external_item_visibility = mk_visibility(ctxt, external_def_id);
    if !vir::ast_util::is_visible_to_opt(&proxy_visibility, &external_item_visibility.restricted_to)
    {
        return err_span(
            span,
            "`external_type_specification` proxy type should be visible to the external type",
        );
    }

    // Turn it into VIR

    let def_id = id.owner_id.to_def_id();
    let (typ_params, typ_bounds) = check_generics_bounds_with_polarity(
        ctxt.tcx,
        &ctxt.verus_items,
        generics.span,
        Some(generics),
        vattrs.external_body,
        def_id,
        Some(&vattrs),
        Some(&mut *ctxt.diagnostics.borrow_mut()),
    )?;
    let mode = Mode::Exec;

    let path = def_id_to_vir_path(ctxt.tcx, &ctxt.verus_items, external_def_id);
    let name = path.segments.last().expect("unexpected struct path");

    if path.krate == Some(Arc::new("builtin".to_string())) {
        return err_span(span, "cannot apply `external_type_specification` to Verus builtin types");
    }

    let proxy_path = def_id_to_vir_path(ctxt.tcx, &ctxt.verus_items, proxy_adt_def.did());
    let proxy = ctxt.spanned_new(span, proxy_path);
    let proxy = Some((*proxy).clone());
    let owning_module = Some(module_path.clone());

    if vattrs.external_body {
        let transparency = DatatypeTransparency::Never;
        let variant_name = name.clone();
        let variant = Variant {
            name: variant_name,
            fields: Arc::new(vec![]),
            ctor_style: CtorPrintStyle::Braces,
        };
        let variants = Arc::new(vec![variant]);
        let visibility = external_item_visibility;
        let datatype = DatatypeX {
            path,
            proxy,
            visibility,
            owning_module,
            transparency,
            typ_params,
            typ_bounds,
            variants,
            mode,
            ext_equal: vattrs.ext_equal,
            user_defined_invariant_fn: None,
        };
        vir.datatypes.push(ctxt.spanned_new(span, datatype));
    } else if external_adt_def.is_struct() {
        let variant_name = Arc::new(name.clone());
        let (variant, inner_vis) = check_variant_data(
            span,
            ctxt,
            id,
            &variant_name,
            None,
            external_adt_def.non_enum_variant(),
            Some(substs_ref),
            &external_item_visibility,
        )?;
        if inner_vis != external_item_visibility {
            return err_span(
                span,
                "external_type_specification: private fields not supported for transparent datatypes (try 'external_body' instead?)",
            );
        }
        let transparency = DatatypeTransparency::WhenVisible(inner_vis);

        let variants = Arc::new(vec![variant]);
        let visibility = external_item_visibility;
        let datatype = DatatypeX {
            path,
            proxy,
            visibility,
            owning_module,
            transparency,
            typ_params,
            typ_bounds,
            variants,
            mode,
            ext_equal: vattrs.ext_equal,
            user_defined_invariant_fn: None,
        };
        vir.datatypes.push(ctxt.spanned_new(span, datatype));
    } else {
        // enum

        let mut total_vis = external_item_visibility.clone();
        let mut variants: Vec<_> = vec![];
        for variant_def in external_adt_def.variants().iter() {
            let variant_def_ident = variant_def.ident(ctxt.tcx);
            let variant_name = variant_def_ident.name.as_str();
            let variant_name = str_ident(variant_name);

            let (variant, total_vis2) = check_variant_data(
                span,
                ctxt,
                id,
                &variant_name,
                None,
                variant_def,
                Some(substs_ref),
                &total_vis,
            )?;
            total_vis = total_vis2;
            variants.push(variant);
        }

        if total_vis != external_item_visibility {
            return err_span(
                span,
                "external_type_specification: private fields not supported for transparent datatypes (try 'external_body' instead?)",
            );
        }

        let transparency = DatatypeTransparency::WhenVisible(total_vis);
        let variants = Arc::new(variants);
        let visibility = external_item_visibility;

        let datatype = DatatypeX {
            path,
            proxy,
            visibility,
            owning_module,
            transparency,
            typ_params,
            typ_bounds,
            variants,
            mode,
            ext_equal: vattrs.ext_equal,
            user_defined_invariant_fn: None,
        };
        vir.datatypes.push(ctxt.spanned_new(span, datatype));
    }

    Ok(())
}

pub(crate) fn setup_type_invariants(krate: &mut KrateX) -> Result<(), VirErr> {
    let mut path_to_idx_opt = None;
    let mut get_datatype_idx = |dts: &Vec<Datatype>, path: &Path| {
        if path_to_idx_opt.is_none() {
            let mut path_to_idx = HashMap::<Path, usize>::new();
            for (i, dt) in dts.iter().enumerate() {
                path_to_idx.insert(dt.x.path.clone(), i);
            }
            path_to_idx_opt = Some(path_to_idx);
        }
        path_to_idx_opt.as_ref().unwrap().get(path).cloned()
    };
    let get_fun_span = |fs: &Vec<Function>, fun: &Fun| {
        for f in fs.iter() {
            if &f.x.name == fun {
                return f.span.clone();
            }
        }
        panic!("get_fun_span failed");
    };

    for f in krate.functions.iter() {
        if f.x.attrs.is_type_invariant_fn {
            if f.x.params.len() != 1 {
                return Err(vir::messages::error(
                    &f.span,
                    "#[verifier::type_invariant]: expected 1 parameter",
                ));
            }
            let param_typ = &f.x.params[0].x.typ;
            let param_typ = vir::ast_util::undecorate_typ(param_typ);
            if let TypX::Datatype(path, ..) = &*param_typ {
                if let Some(idx) = get_datatype_idx(&krate.datatypes, path) {
                    let mut dt = (*krate.datatypes[idx]).clone();
                    if let Some(f2) = &dt.x.user_defined_invariant_fn {
                        return Err(vir::messages::error(
                            &f.span,
                            "type_invariant: multiple type invariants defined for the same type",
                        )
                        .primary_span(&get_fun_span(&krate.functions, f2)));
                    }
                    dt.x.user_defined_invariant_fn = Some(f.x.name.clone());
                    krate.datatypes[idx] = Arc::new(dt);
                } else {
                    return Err(vir::messages::error(
                        &f.span,
                        "type_invariant: expected parameter to be a datatype declared in this crate",
                    ));
                }
            } else {
                return Err(vir::messages::error(
                    &f.span,
                    "type_invariant: expected parameter to be a datatype declared in this crate",
                ));
            }
        }
    }

    Ok(())
}
