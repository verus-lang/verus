/*
Convert Rust HIR/THIR to VIR for verification.

For soundness's sake, be as defensive as possible:
- if we're not prepared to verify a feature of Rust, disallow the feature
- explicitly match all fields of the Rust AST so we catch any features added in the future
*/

use crate::context::Context;
use crate::external::{CrateItems, GeneralItemId, VerifOrExternal};
use crate::reveal_hide::handle_reveal_hide;
use crate::rust_to_vir_adts::{check_item_enum, check_item_struct, check_item_union};
use crate::rust_to_vir_base::{def_id_to_vir_path, mid_ty_to_vir, mk_visibility};
use crate::rust_to_vir_func::{check_foreign_item_fn, check_item_fn, CheckItemFnEither};
use crate::rust_to_vir_global::TypIgnoreImplPaths;
use crate::rust_to_vir_impl::ExternalInfo;
use crate::util::err_span;
use crate::verus_items::{self, VerusItem};
use crate::{unsupported_err, unsupported_err_unless};
use std::collections::HashSet;

use rustc_ast::IsAuto;
use rustc_hir::{
    ForeignItem, ForeignItemId, ForeignItemKind, ImplItemKind, Item, ItemId, ItemKind, MaybeOwner,
    Mutability, OpaqueTy, OpaqueTyOrigin, OwnerNode,
};
use vir::def::Spanned;

use std::collections::HashMap;
use std::sync::Arc;
use vir::ast::{FunX, FunctionKind, Krate, KrateX, Path, VirErr};

fn check_item<'tcx>(
    ctxt: &Context<'tcx>,
    vir: &mut KrateX,
    module_path: &Path,
    id: &ItemId,
    item: &'tcx Item<'tcx>,
    external_info: &mut ExternalInfo,
    crate_items: &CrateItems,
) -> Result<(), VirErr> {
    let attrs = ctxt.tcx.hir().attrs(item.hir_id());
    let vattrs = ctxt.get_verifier_attrs(attrs)?;
    if vattrs.internal_reveal_fn {
        return Ok(());
    }
    if vattrs.internal_const_body {
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

            let module = vir
                .modules
                .iter_mut()
                .find(|m| &m.x.path == module_path)
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

        let mid_ty = ctxt.tcx.type_of(def_id).skip_binder();
        let vir_ty = mid_ty_to_vir(ctxt.tcx, &ctxt.verus_items, def_id, item.span, &mid_ty, false)?;

        crate::rust_to_vir_func::check_item_const_or_static(
            ctxt,
            &mut vir.functions,
            item.span,
            item.owner_id.to_def_id(),
            visibility(),
            module_path,
            ctxt.tcx.hir().attrs(item.hir_id()),
            &vir_ty,
            body_id,
            matches!(item.kind, ItemKind::Static(_, _, _)),
        )?;

        Ok(())
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
                module_path,
                ctxt.tcx.hir().attrs(item.hir_id()),
                sig,
                None,
                generics,
                CheckItemFnEither::BodyId(body_id),
                None,
                None,
                external_info,
                None,
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

            let tyof = ctxt.tcx.type_of(item.owner_id.to_def_id()).skip_binder();
            let adt_def = tyof.ty_adt_def().expect("adt_def");

            check_item_struct(
                ctxt,
                vir,
                module_path,
                item.span,
                id,
                visibility(),
                ctxt.tcx.hir().attrs(item.hir_id()),
                variant_data,
                generics,
                adt_def,
                external_info,
            )?;
        }
        ItemKind::Enum(enum_def, generics) => {
            let tyof = ctxt.tcx.type_of(item.owner_id.to_def_id()).skip_binder();
            let adt_def = tyof.ty_adt_def().expect("adt_def");

            // TODO use rustc_middle? see `Struct` case
            check_item_enum(
                ctxt,
                vir,
                module_path,
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
            let tyof = ctxt.tcx.type_of(item.owner_id.to_def_id()).skip_binder();
            let adt_def = tyof.ty_adt_def().expect("adt_def");

            check_item_union(
                ctxt,
                vir,
                module_path,
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
            crate::rust_to_vir_impl::translate_impl(
                ctxt,
                vir,
                item,
                impll,
                module_path.clone(),
                external_info,
                crate_items,
                attrs,
            )?;
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
            unsupported_err!(item.span, "static mut");
        }
        ItemKind::Macro(_, _) => {}
        ItemKind::Trait(IsAuto::No, safety, trait_generics, _bounds, trait_items) => {
            let trait_def_id = item.owner_id.to_def_id();
            crate::rust_to_vir_trait::translate_trait(
                ctxt,
                vir,
                item.span,
                trait_def_id,
                visibility(),
                module_path,
                trait_generics,
                trait_items,
                &vattrs,
                external_info,
                crate_items,
                *safety,
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
        ForeignItemKind::Fn(rustc_hir::FnSig { decl, .. }, idents, generics) => {
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
            unsupported_err!(item.span, "unsupported foreign item", item);
        }
    }
    Ok(())
}

pub(crate) fn get_root_module_path<'tcx>(ctxt: &Context<'tcx>) -> Path {
    def_id_to_vir_path(ctxt.tcx, &ctxt.verus_items, rustc_hir::CRATE_OWNER_ID.to_def_id())
}

pub fn crate_to_vir<'a, 'tcx>(
    ctxt: &mut Context<'tcx>,
    imported: &Vec<Krate>,
) -> Result<(Krate, CrateItems), VirErr> {
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

    let mut external_info = ExternalInfo::new();

    // TODO: when we stop ignoring these traits,
    // they should probably declared explicitly as external traits
    let tcx = ctxt.tcx;
    external_info.trait_id_set.insert(tcx.lang_items().sized_trait().expect("lang_item"));
    external_info.trait_id_set.insert(tcx.lang_items().copy_trait().expect("lang_item"));
    external_info.trait_id_set.insert(tcx.lang_items().unpin_trait().expect("lang_item"));
    external_info.trait_id_set.insert(tcx.lang_items().sync_trait().expect("lang_item"));
    external_info.trait_id_set.insert(tcx.lang_items().tuple_trait().expect("lang_item"));
    external_info
        .trait_id_set
        .insert(tcx.get_diagnostic_item(rustc_span::sym::Send).expect("send"));

    let crate_items = crate::external::get_crate_items(ctxt)?;

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

    // Find all modules that contain at least 1 item of interest
    let mut used_modules = HashSet::<Path>::new();
    for crate_item in crate_items.items.iter() {
        match &crate_item.verif {
            VerifOrExternal::VerusAware { module_path } => {
                used_modules.insert(module_path.clone());
            }
            _ => {}
        }
    }
    // Insert those modules into vir.modules
    let root_module_path = get_root_module_path(ctxt);
    if used_modules.contains(&root_module_path) {
        let owner = ctxt.tcx.hir_owner_node(rustc_hir::CRATE_OWNER_ID);
        vir.modules.push(ctxt.spanned_new(
            owner.span(),
            vir::ast::ModuleX { path: root_module_path.clone(), reveals: None },
        ));
    }
    for (_owner_id, owner_opt) in ctxt.krate.owners.iter_enumerated() {
        if let MaybeOwner::Owner(owner) = owner_opt {
            match owner.node() {
                OwnerNode::Item(item @ Item { kind: ItemKind::Mod(_module), owner_id, .. }) => {
                    let path =
                        def_id_to_vir_path(ctxt.tcx, &ctxt.verus_items, owner_id.to_def_id());
                    if used_modules.contains(&path) {
                        vir.modules.push(ctxt.spanned_new(
                            item.span,
                            vir::ast::ModuleX { path: path.clone(), reveals: None },
                        ));
                    }
                }
                _ => {}
            }
        }
    }

    for crate_item in crate_items.items.iter() {
        match &crate_item.verif {
            VerifOrExternal::VerusAware { module_path } => {
                match crate_item.id {
                    GeneralItemId::ItemId(item_id) => {
                        let item = ctxt.tcx.hir().item(item_id);
                        check_item(
                            ctxt,
                            &mut vir,
                            &module_path,
                            &item_id,
                            item,
                            &mut external_info,
                            &crate_items,
                        )?;
                    }
                    GeneralItemId::ForeignItemId(foreign_item_id) => {
                        let foreign_item = ctxt.tcx.hir().foreign_item(foreign_item_id);
                        check_foreign_item(ctxt, &mut vir, &foreign_item_id, foreign_item)?;
                    }
                    GeneralItemId::ImplItemId(_impl_item_id) => {
                        // Processed as part of the impl (which is an Item)
                    }
                    GeneralItemId::TraitItemId(_trait_item_id) => {
                        // Processed as part of the impl (which is an Item)
                    }
                }
            }
            VerifOrExternal::External { path: Some(my_path), path_string: _, explicit: _ } => {
                // If possible, track this item in the VIR Krate for diagnostic purposes
                let (is_fn, is_datatype) = match crate_item.id {
                    GeneralItemId::ItemId(item_id) => {
                        let i = ctxt.tcx.hir().item(item_id);
                        match i.kind {
                            ItemKind::Fn(..) | ItemKind::Const(..) => (true, false),
                            ItemKind::Struct(..) | ItemKind::Enum(..) | ItemKind::Union(..) => {
                                (false, true)
                            }
                            _ => (false, false),
                        }
                    }
                    GeneralItemId::ForeignItemId(foreign_item_id) => {
                        let i = ctxt.tcx.hir().foreign_item(foreign_item_id);
                        match i.kind {
                            ForeignItemKind::Fn(..) => (true, false),
                            _ => (false, false),
                        }
                    }
                    GeneralItemId::ImplItemId(impl_item_id) => {
                        let i = ctxt.tcx.hir().impl_item(impl_item_id);
                        match i.kind {
                            ImplItemKind::Fn(..) => (true, false),
                            _ => (false, false),
                        }
                    }
                    GeneralItemId::TraitItemId(_trait_item_id) => (false, false),
                };
                if is_fn {
                    vir.external_fns.push(Arc::new(FunX { path: my_path.clone() }));
                }
                if is_datatype {
                    vir.external_types.push(my_path.clone());
                }
            }
            VerifOrExternal::External { path: None, path_string: _, explicit: _ } => {}
        }
    }

    vir.path_as_rust_names = vir::ast_util::get_path_as_rust_names_for_krate(&ctxt.vstd_crate_name);

    crate::rust_to_vir_impl::collect_external_trait_impls(
        ctxt,
        imported,
        &mut vir,
        &mut external_info,
    )?;

    crate::rust_to_vir_adts::setup_type_invariants(&mut vir)?;

    Ok((Arc::new(vir), crate_items))
}
