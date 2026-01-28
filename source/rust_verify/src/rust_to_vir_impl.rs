use crate::automatic_derive::is_automatically_derived;
use crate::context::Context;
use crate::external::CrateItems;
use crate::rust_to_vir_base::{
    def_id_to_vir_path_option, mid_ty_const_to_vir, mk_visibility, typ_path_and_ident_to_vir_path,
};
use crate::rust_to_vir_func::{CheckItemFnEither, check_item_fn};
use crate::unsupported_err;
use crate::util::{err_span, vir_err_span_str};
use crate::verus_items::{self, MarkerItem, RustItem, VerusItem};
use indexmap::{IndexMap, IndexSet};
use rustc_hir::{ConstItemRhs, ImplItemKind, Item, QPath, Safety, TraitImplHeader, TraitRef};
use rustc_middle::ty::{AssocKind, GenericArgKind, PseudoCanonicalInput, TypingEnv};
use rustc_span::Span;
use rustc_span::def_id::DefId;
use std::collections::{HashMap, HashSet};
use std::sync::Arc;
use vir::ast::{
    AssocTypeImpl, AssocTypeImplX, Dt, Fun, FunX, Function, FunctionKind, Ident, ImplPath, Krate,
    KrateX, Path, Trait, TraitImpl, Typ, Typs, VirErr,
};

// Used to collect all needed external trait implementations
pub(crate) struct ExternalInfo {
    // all known local traits (both declared-in-verus and #[verifier::external_trait_specification])
    // TODO: include marker traits, once we're confident we can handle them
    pub(crate) local_trait_ids: Vec<DefId>,
    // all known traits (both declared-in-verus and #[verifier::external_trait_specification])
    pub(crate) trait_id_set: HashSet<DefId>,
    // all known datatypes (both declared-in-verus and #[verifier::external_type_specification])
    type_paths: HashSet<Path>,
    // type_id_map[d] will be true if path(d) is in type_paths; otherwise false or absent
    type_id_map: HashMap<DefId, bool>,
    // all non-external trait impls
    pub(crate) internal_trait_impls: HashSet<DefId>,
    // all #[verifier::external_fn_specification] functions that implement a trait
    pub(crate) external_fn_specification_trait_method_impls: Vec<(DefId, rustc_span::Span)>,
    // For verifier::external_trait_extension(TSpec via TSpecImpl),
    // replace all "impl TSpecImpl" with "impl TSpec"
    pub(crate) external_trait_extension_impl_map: HashMap<Path, Path>,
}

impl ExternalInfo {
    pub(crate) fn new() -> ExternalInfo {
        ExternalInfo {
            local_trait_ids: Vec::new(),
            trait_id_set: HashSet::new(),
            type_paths: HashSet::new(),
            type_id_map: HashMap::new(),
            internal_trait_impls: HashSet::new(),
            external_fn_specification_trait_method_impls: Vec::new(),
            external_trait_extension_impl_map: HashMap::new(),
        }
    }

    pub(crate) fn add_type_id(&mut self, def_id: DefId) {
        self.type_id_map.insert(def_id, true);
    }

    pub(crate) fn has_type_id<'tcx>(&mut self, ctxt: &Context<'tcx>, def_id: DefId) -> bool {
        match self.type_id_map.get(&def_id).copied() {
            None => {
                let path = ctxt.def_id_to_vir_path(def_id);
                let has = self.type_paths.contains(&path);
                self.type_id_map.insert(def_id, has);
                has
            }
            Some(b) => b,
        }
    }
}

fn trait_impl_to_vir<'tcx>(
    ctxt: &Context<'tcx>,
    span: rustc_span::Span,
    path_span: rustc_span::Span,
    impl_def_id: DefId,
    hir_generics: Option<&'tcx rustc_hir::Generics<'tcx>>,
    external_info: &mut ExternalInfo,
    module_path: Path,
    auto_imported: bool,
    external_trait_blanket: bool,
) -> Result<Option<(Path, Typs, TraitImpl)>, VirErr> {
    let trait_polarity = ctxt.tcx.impl_polarity(impl_def_id);
    if trait_polarity == rustc_middle::ty::ImplPolarity::Negative {
        // Negative impls currently show up in two expected cases:
        // - Send
        // - Sync
        // and in one surprising case:
        // - Iterator
        //   - see https://github.com/rust-lang/rust/commit/1a8109253196064e26a427d9184874ae14c55f6e
        // Currently, we ignore negative impls;
        // trait_conflicts.rs should protect us from any overlap caused by ignoring negative impls
        // TODO: better handling of negative impls
        return Ok(None);
    }

    let trait_ref = ctxt.tcx.impl_trait_ref(impl_def_id);
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
    let args = trait_ref.skip_binder().args;
    for arg in args.iter() {
        match arg.kind() {
            GenericArgKind::Lifetime(_) => {}
            GenericArgKind::Type(ty) => {
                types.push(ctxt.mid_ty_to_vir(impl_def_id, span, &ty, false)?);
            }
            GenericArgKind::Const(cnst) => {
                types.push(mid_ty_const_to_vir(ctxt.tcx, Some(span), &cnst)?);
            }
        }
    }

    let types = Arc::new(types);
    let mut trait_path = ctxt.def_id_to_vir_path(trait_did);
    if let Some(spec) = external_info.external_trait_extension_impl_map.get(&trait_path) {
        trait_path = spec.clone();
    }
    let (typ_params, typ_bounds) = crate::rust_to_vir_base::check_generics_bounds_no_polarity(
        ctxt.tcx,
        &ctxt.verus_items,
        span,
        hir_generics,
        impl_def_id,
        Some(&mut *ctxt.diagnostics.borrow_mut()),
    )?;
    let impl_path = ctxt.def_id_to_vir_path(impl_def_id);
    let trait_impl = vir::ast::TraitImplX {
        impl_path: impl_path.clone(),
        typ_params,
        typ_bounds,
        trait_path: trait_path.clone(),
        trait_typ_args: types.clone(),
        trait_typ_arg_impls: ctxt.spanned_new(path_span, impl_paths),
        owning_module: Some(module_path),
        auto_imported,
        external_trait_blanket,
    };
    let trait_impl = ctxt.spanned_new(span, trait_impl);
    Ok(Some((trait_path, types, trait_impl)))
}

fn translate_assoc_type<'tcx>(
    ctxt: &Context<'tcx>,
    name: Ident,
    impll_generics_span: Span,
    impll_generics: Option<&'tcx rustc_hir::Generics<'tcx>>,
    impl_item_span: Span,
    impl_item_id: DefId,
    impl_def_id: DefId,
    trait_path: Path,
    trait_typ_args: Typs,
) -> Result<AssocTypeImpl, VirErr> {
    let impl_path = ctxt.def_id_to_vir_path(impl_def_id);
    let trait_ref = ctxt.tcx.impl_trait_ref(impl_def_id);
    let ty = ctxt.tcx.type_of(impl_item_id).skip_binder();
    let typ = ctxt.mid_ty_to_vir(impl_item_id, impl_item_span, &ty, false)?;
    let (typ_params, typ_bounds) = crate::rust_to_vir_base::check_generics_bounds_no_polarity(
        ctxt.tcx,
        &ctxt.verus_items,
        impll_generics_span,
        impll_generics,
        impl_def_id,
        Some(&mut *ctxt.diagnostics.borrow_mut()),
    )?;

    let ai = ctxt.tcx.associated_item(impl_item_id);
    let assoc_def_id = ai.trait_item_def_id().unwrap();
    let bounds = ctxt.tcx.item_bounds(assoc_def_id);
    let assoc_generics = ctxt.tcx.generics_of(assoc_def_id);
    let mut assoc_args: Vec<rustc_middle::ty::GenericArg> =
        trait_ref.instantiate_identity().args.into_iter().collect();
    for p in &assoc_generics.own_params {
        let e = rustc_middle::ty::EarlyParamRegion {
            //def_id: p.def_id,
            index: assoc_generics.param_def_id_to_index(ctxt.tcx, p.def_id).expect("param_def"),
            name: p.name,
        };
        let r = rustc_middle::ty::Region::new_early_param(ctxt.tcx, e);
        assoc_args.push(rustc_middle::ty::GenericArg::from(r));
    }
    let inst_bounds = bounds.instantiate(ctxt.tcx, &*assoc_args);
    let typing_env = TypingEnv::post_analysis(ctxt.tcx, impl_item_id);
    let inst_bounds = ctxt.tcx.normalize_erasing_regions(typing_env, inst_bounds);

    let mut impl_paths = Vec::new();
    for inst_pred in inst_bounds {
        if let rustc_middle::ty::ClauseKind::Trait(_) = inst_pred.kind().skip_binder() {
            let poly_trait_refs = inst_pred.kind().map_bound(|p| {
                if let rustc_middle::ty::ClauseKind::Trait(tp) = &p {
                    tp.trait_ref
                } else {
                    unreachable!()
                }
            });
            let pseudo_canonical_inp =
                PseudoCanonicalInput { typing_env, value: poly_trait_refs.skip_binder() };
            let candidate = ctxt.tcx.codegen_select_candidate(pseudo_canonical_inp);
            if let Ok(impl_source) = candidate {
                if let rustc_middle::traits::ImplSource::UserDefined(u) = impl_source {
                    let impl_path = ctxt.def_id_to_vir_path(u.impl_def_id);
                    impl_paths.push(ImplPath::TraitImplPath(impl_path));
                }
            }
        }
    }

    let assocx = AssocTypeImplX {
        name,
        impl_path: impl_path.clone(),
        typ_params,
        typ_bounds,
        trait_path,
        trait_typ_args,
        typ,
        impl_paths: Arc::new(impl_paths),
    };
    Ok(ctxt.spanned_new(impl_item_span, assocx))
}

pub(crate) fn translate_impl<'tcx>(
    ctxt: &Context<'tcx>,
    vir: &mut KrateX,
    item: &'tcx Item<'tcx>,
    impll: &rustc_hir::Impl<'tcx>,
    module_path: Path,
    external_info: &mut ExternalInfo,
    crate_items: &CrateItems,
    attrs: &[rustc_hir::Attribute],
) -> Result<(), VirErr> {
    let impl_def_id = item.owner_id.to_def_id();
    let impl_path = ctxt.def_id_to_vir_path(impl_def_id);

    if let Some(TraitImplHeader { trait_ref: TraitRef { path, hir_ref_id: _ }, safety, .. }) =
        impll.of_trait
    {
        let trait_def_id = path.res.def_id();

        let rust_item = verus_items::get_rust_item(ctxt.tcx, trait_def_id);
        if matches!(rust_item, Some(RustItem::Fn | RustItem::FnOnce | RustItem::FnMut)) {
            return err_span(
                item.span,
                "Verus does not support implementing this trait via an `impl` block",
            );
        }

        let verus_item = ctxt.verus_items.id_to_name.get(&trait_def_id);

        if *safety != Safety::Safe {
            if matches!(rust_item, Some(RustItem::Send)) {
                return err_span(item.span, "unsafe impl for `Send` is not allowed");
            }
            if matches!(rust_item, Some(RustItem::Sync)) {
                return err_span(item.span, "unsafe impl for `Sync` is not allowed");
            }
        }

        let ignore = if let Some(VerusItem::Marker(MarkerItem::Structural)) = verus_item {
            let ty = {
                // TODO extract to rust_to_vir_base, or use
                // https://doc.rust-lang.org/nightly/nightly-rustc/rustc_typeck/fn.hir_ty_to_ty.html
                // ?
                let def_id = match impll.self_ty.kind {
                    rustc_hir::TyKind::Path(QPath::Resolved(None, path)) => path.res.def_id(),
                    _ => panic!("self type of impl is not resolved: {:?}", impll.self_ty.kind),
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
                    ctxt.tcx.mk_args_from_iter(substs.iter().map(|g| match g.kind() {
                        rustc_middle::ty::GenericArgKind::Type(_) => (*ctxt.tcx).types.never.into(),
                        _ => g,
                    })),
                )
            } else {
                panic!("Structural impl for non-adt type");
            };
            let ty_applied_never = ctxt.tcx.mk_ty_from_kind(ty_kind_applied_never);
            if !ty_applied_never.is_structural_eq_shallow(ctxt.tcx) {
                return Err(vir_err_span_str(
                    item.span,
                    &format!("structural impl for non-structural type {:?}", ty),
                )
                .help("make sure `PartialEq` is also auto-derived for this type"));
            }
            true
        } else {
            false
        };

        if ignore {
            for impl_item_id in impll.items {
                let assoc_item = ctxt.tcx.associated_item(impl_item_id.hir_id().owner.to_def_id());
                match assoc_item.kind {
                    AssocKind::Fn { has_self, .. } if has_self => {
                        let impl_item = ctxt.tcx.hir_impl_item(*impl_item_id);
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
        } else {
            /* sealed, `unsafe` */
            let trait_attrs = ctxt.tcx.get_all_attrs(trait_def_id);
            let sealed = crate::attributes::is_sealed(
                trait_attrs,
                Some(&mut *ctxt.diagnostics.borrow_mut()),
            )?;

            if sealed {
                return err_span(item.span, "cannot implement `sealed` trait");
            }
        }
    }

    let vattrs = ctxt.get_verifier_attrs(attrs)?;
    let trait_path_typ_args =
        if let Some(TraitImplHeader { trait_ref: TraitRef { path, .. }, .. }) = &impll.of_trait {
            let impl_def_id = item.owner_id.to_def_id();
            external_info.internal_trait_impls.insert(impl_def_id);
            let path_span = path.span.to(impll.self_ty.span);
            match trait_impl_to_vir(
                ctxt,
                item.span,
                path_span,
                impl_def_id,
                Some(impll.generics),
                external_info,
                module_path.clone(),
                false,
                vattrs.external_trait_blanket,
            )? {
                Some((trait_path, types, trait_impl)) => {
                    vir.trait_impls.push(trait_impl);
                    Some((trait_path, types))
                }
                _ => None,
            }
        } else {
            None
        };

    let autoderive_action = if let Some(of_trait) = impll.of_trait
        && is_automatically_derived(attrs)
    {
        let trait_def_id = of_trait.trait_ref.path.res.def_id();
        let rust_item = crate::verus_items::get_rust_item(ctxt.tcx, trait_def_id);
        let action = crate::automatic_derive::get_action(rust_item);
        Some(action)
    } else {
        None
    };

    for impl_item_id in impll.items {
        if vattrs.external_trait_blanket {
            continue;
        }
        let impl_item = ctxt.tcx.hir_impl_item(*impl_item_id);
        let fn_attrs = ctxt.tcx.hir_attrs(impl_item.hir_id());

        if crate_items.is_impl_item_external(*impl_item_id) {
            if trait_path_typ_args.is_some() {
                // sanity check - this should be redundant with prior check in external.rs
                return err_span(
                    item.span,
                    "an item in a trait impl cannot be marked external - you can either use external_body, or mark the entire trait impl as external",
                );
            }
            continue;
        }
        let assoc_item = ctxt.tcx.associated_item(impl_item_id.hir_id().owner.to_def_id());
        match assoc_item.kind {
            AssocKind::Fn { name: _name, has_self: true | false } => {
                let impl_item_visibility = mk_visibility(&ctxt, impl_item.owner_id.to_def_id());
                match &impl_item.kind {
                    ImplItemKind::Fn(sig, body_id) => {
                        let kind = if let Some((trait_path, trait_typ_args)) =
                            trait_path_typ_args.clone()
                        {
                            let ident = impl_item.ident.to_string();
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

                        let _ = crate::rust_to_vir_base::check_fn_opaque_ty(
                            ctxt,
                            vir,
                            &impl_item.owner_id.to_def_id(),
                        )?;

                        check_item_fn(
                            ctxt,
                            &mut vir.functions,
                            Some(&mut vir.reveal_groups),
                            impl_item.owner_id.to_def_id(),
                            kind,
                            impl_item_visibility,
                            &module_path,
                            fn_attrs,
                            &sig,
                            Some((&impll.generics, impl_def_id)),
                            &impl_item.generics,
                            CheckItemFnEither::BodyId(&body_id),
                            None,
                            None,
                            external_info,
                            autoderive_action.as_ref(),
                        )?;
                    }
                    _ => unsupported_err!(item.span, "unsupported item in impl", impl_item_id),
                }
            }
            AssocKind::Type { .. } => {
                if impl_item.generics.predicates.len() != 0
                    || impl_item.generics.has_where_clause_predicates
                {
                    unsupported_err!(
                        item.span,
                        "unsupported generics on associated type",
                        impl_item_id
                    );
                }
                if let ImplItemKind::Type(_ty) = impl_item.kind {
                    if let Some((trait_path, trait_typ_args)) = trait_path_typ_args.clone() {
                        let name = Arc::new(impl_item.ident.to_string());
                        let assoc_type_impl = translate_assoc_type(
                            ctxt,
                            name,
                            impll.generics.span,
                            Some(&impll.generics),
                            impl_item.span,
                            impl_item.owner_id.to_def_id(),
                            impl_def_id,
                            trait_path,
                            trait_typ_args,
                        )?;
                        vir.assoc_type_impls.push(assoc_type_impl);
                    } else {
                        unsupported_err!(item.span, "unsupported item ref in impl", impl_item_id);
                    }
                } else {
                    unsupported_err!(item.span, "unsupported item ref in impl", impl_item_id);
                }
            }
            AssocKind::Const { name: _name } => {
                if trait_path_typ_args.is_some() {
                    unsupported_err!(item.span, "not yet supported: const trait member")
                }
                if let ImplItemKind::Const(_ty, ConstItemRhs::Body(body_id)) = &impl_item.kind {
                    let def_id = body_id.hir_id.owner.to_def_id();
                    let mid_ty = ctxt.tcx.type_of(def_id).skip_binder();
                    let vir_ty = ctxt.mid_ty_to_vir(def_id, impl_item.span, &mid_ty, false)?;
                    crate::rust_to_vir_func::check_item_const_or_static(
                        ctxt,
                        &mut vir.functions,
                        impl_item.span,
                        impl_item.owner_id.to_def_id(),
                        mk_visibility(ctxt, impl_item.owner_id.to_def_id()),
                        &module_path,
                        ctxt.tcx.hir_attrs(impl_item.hir_id()),
                        &vir_ty,
                        &body_id,
                        false,
                        false,
                    )?;
                } else {
                    unsupported_err!(item.span, "unsupported item ref in impl", impl_item_id);
                }
            }
        }
    }
    Ok(())
}

pub(crate) fn collect_external_trait_impls<'tcx>(
    ctxt: &Context<'tcx>,
    imported: &Vec<Krate>,
    krate: &mut KrateX,
    external_info: &mut ExternalInfo,
) -> Result<(), VirErr> {
    let tcx = ctxt.tcx;
    let mut considered_impls: HashSet<DefId> = HashSet::new();
    let mut collected_impls: HashSet<DefId> = HashSet::new();

    // All known datatypes:
    for k in imported.iter().map(|k| &**k).chain(vec![&*krate].into_iter()) {
        for d in k.datatypes.iter() {
            if let Dt::Path(path) = &d.x.name {
                external_info.type_paths.insert(path.clone());
            }
        }
    }

    // Traits declared to Verus (as internal or external) in earlier crates
    let mut old_traits: HashSet<Path> = HashSet::new();
    // Traits declared to Verus (as internal or external) only in current crate
    // (may be current crate's external declaration of trait from another crate)
    let mut new_traits: HashSet<Path> = HashSet::new();

    // First, collect all traits known to Verus:
    for t in imported.iter().flat_map(|k| k.traits.iter()) {
        old_traits.insert(t.x.name.clone());
    }
    for t in krate.traits.iter() {
        if !old_traits.contains(&t.x.name) {
            new_traits.insert(t.x.name.clone());
        }
    }
    let mut all_traits = old_traits;
    all_traits.extend(new_traits.iter().cloned());
    let mut all_trait_ids: Vec<DefId> = Vec::new();
    for c in tcx.crates(()) {
        assert!(*c != rustc_span::def_id::LOCAL_CRATE);
        for trait_id in tcx.traits(*c) {
            let path = def_id_to_vir_path_option(tcx, Some(&ctxt.verus_items), *trait_id);
            if let Some(path) = path {
                if all_traits.contains(&path) {
                    all_trait_ids.push(*trait_id);
                }
            }
        }
    }
    // LOCAL_CRATE traits are separate:
    all_trait_ids.extend(external_info.local_trait_ids.iter().cloned());
    external_info.trait_id_set.extend(all_trait_ids.iter().cloned());

    let mut trait_map: HashMap<Path, Vec<Trait>> =
        krate.traits.iter().map(|t| (t.x.name.clone(), vec![t.clone()])).collect();
    for k in imported {
        for t in k.traits.iter() {
            trait_map.entry(t.x.name.clone()).or_default().push(t.clone());
        }
    }

    // Next, collect all possible new implementations of traits known to Verus:
    let mut auto_import_impls: Vec<DefId> = Vec::new();
    for trait_id in all_trait_ids {
        let path = ctxt.def_id_to_vir_path(trait_id);
        for impl_def_id in tcx.all_impls(trait_id) {
            if considered_impls.contains(&impl_def_id) {
                continue;
            }
            considered_impls.insert(impl_def_id);
            if external_info.internal_trait_impls.contains(&impl_def_id) {
                // already processed our own trait impls
                continue;
            }
            let is_new_trait = new_traits.contains(&path);
            let is_local_impl = impl_def_id.krate == rustc_span::def_id::LOCAL_CRATE;
            if is_new_trait || is_local_impl {
                // Either the trait is new to us, or the impl is new to us
                auto_import_impls.push(impl_def_id);
            }
        }
    }

    // Process only the new implementations that could be visible to Verus:
    'impls: for impl_def_id in auto_import_impls {
        let trait_ref = tcx.impl_trait_ref(&impl_def_id);
        for arg in trait_ref.skip_binder().args.iter() {
            if !crate::rust_to_vir_base::mid_arg_filter_for_external_impls(
                ctxt,
                arg.walk(),
                external_info,
            ) {
                continue 'impls;
            }
        }
        if !crate::rust_to_vir_base::mid_generics_filter_for_external_impls(
            ctxt,
            impl_def_id,
            external_info,
        ) {
            continue;
        }
        let span = tcx.def_span(&impl_def_id);
        let impl_path = ctxt.def_id_to_vir_path(impl_def_id);
        let module_path = impl_path.pop_segment();
        let t_impl_opt = trait_impl_to_vir(
            ctxt,
            span,
            span,
            impl_def_id,
            None,
            external_info,
            module_path,
            true,
            false,
        );
        if let Ok(Some((trait_path, trait_typ_args, trait_impl))) = t_impl_opt {
            let mut assoc_type_impls: Vec<AssocTypeImpl> = Vec::new();
            for assoc_item in tcx.associated_items(impl_def_id).in_definition_order() {
                match assoc_item.kind {
                    rustc_middle::ty::AssocKind::Type { .. } => {
                        let name = Arc::new(assoc_item.ident(tcx).to_string());
                        if !trait_map[&trait_path].iter().any(|t| t.x.assoc_typs.contains(&name)) {
                            continue;
                        }
                        if !crate::rust_to_vir_base::mid_ty_filter_for_external_impls(
                            ctxt,
                            &tcx.type_of(assoc_item.def_id).skip_binder(),
                            external_info,
                        ) {
                            continue 'impls;
                        }
                        match translate_assoc_type(
                            ctxt,
                            name,
                            span,
                            None,
                            span,
                            assoc_item.def_id,
                            impl_def_id,
                            trait_path.clone(),
                            trait_typ_args.clone(),
                        ) {
                            Ok(assoc_type_impl) => {
                                assoc_type_impls.push(assoc_type_impl);
                            }
                            _ => {
                                continue 'impls;
                            }
                        }
                    }
                    _ => {}
                }
            }
            krate.trait_impls.push(trait_impl);
            krate.assoc_type_impls.append(&mut assoc_type_impls);
            collected_impls.insert(impl_def_id);
        } else if let Ok(None) = t_impl_opt {
            // Negative impl; do nothing for now
        } else {
            // Ideally, our filtering should prevent us from reaching here.
            // Probably, we didn't want to include the external impl anyway,
            // so drop it rather than failing.
            // TODO: add a mode for rust_verify_test that fails if this is reached.
        }
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

    for (def_id, span) in external_info.external_fn_specification_trait_method_impls.iter() {
        let trait_method_impl = ctxt.def_id_to_vir_path(*def_id);
        let trait_impl = trait_method_impl.pop_segment();
        match new_trait_impls.get_mut(&trait_impl) {
            Some(m) => {
                m.1.push((*def_id, *span));
            }
            None => {
                let impl_def_id = tcx.impl_of_assoc(*def_id).unwrap();
                new_trait_impls.insert(trait_impl, (impl_def_id, vec![(*def_id, *span)]));
            }
        }
    }

    for (impl_path, (impl_def_id, funs)) in new_trait_impls.iter() {
        let trait_ref = tcx.impl_trait_ref(impl_def_id);
        let trait_did = trait_ref.skip_binder().def_id;
        let trait_path = ctxt.def_id_to_vir_path(trait_did);
        let Some(traitt) = trait_map.get(&trait_path) else {
            continue;
        };

        let span = funs[0].1;

        let mut methods_we_have = IndexSet::<vir::ast::Ident>::new();
        for (fun_def_id, fun_span) in funs.iter() {
            let path = ctxt.def_id_to_vir_path(*fun_def_id);
            if !methods_we_have.insert(path.last_segment()) {
                return err_span(*fun_span, "duplicate assume_specification for this method");
            }
        }

        for method in traitt.x.methods.iter() {
            let f = &func_map[method];
            if matches!(&f.x.kind, FunctionKind::TraitMethodDecl { has_default: true, .. }) {
                continue;
            }
            if !methods_we_have.contains::<vir::ast::Ident>(&method.path.last_segment()) {
                return err_span(
                    span,
                    format!(
                        "using assume_specification for this function requires you to specify all other functions for the same trait impl, but the method `{:}` is missing",
                        method.path.last_segment()
                    ),
                );
            }
        }

        if collected_impls.contains(impl_def_id) {
            continue;
        }

        let module_path = impl_path.pop_segment();

        if let Some((_trait_path, _types, trait_impl)) = trait_impl_to_vir(
            ctxt,
            span,
            span,
            *impl_def_id,
            None,
            external_info,
            module_path,
            false,
            false,
        )? {
            krate.trait_impls.push(trait_impl);
        }
    }

    Ok(())
}
