/*
Convert Rust HIR/THIR to VIR for verification.

For soundness's sake, be as defensive as possible:
- if we're not prepared to verify a feature of Rust, disallow the feature
- explicitly match all fields of the Rust AST so we catch any features added in the future
*/

use crate::context::Context;
use crate::reveal_hide::handle_reveal_hide;
use crate::rust_to_vir_adts::{check_item_enum, check_item_struct, check_item_union};
use crate::rust_to_vir_base::{def_id_to_vir_path, mid_ty_to_vir, mk_visibility};
use crate::rust_to_vir_func::{check_foreign_item_fn, check_item_fn, CheckItemFnEither};
use crate::rust_to_vir_global::TypIgnoreImplPaths;
use crate::rust_to_vir_impl::ExternalInfo;
use crate::util::{err_span, unsupported_err_span};
use crate::verus_items::{self, VerusItem};
use crate::{unsupported_err, unsupported_err_unless};

use rustc_ast::IsAuto;
use rustc_hir::{
    ForeignItem, ForeignItemId, ForeignItemKind, ImplItemKind, Item, ItemId, ItemKind, MaybeOwner,
    Mutability, OpaqueTy, OpaqueTyOrigin, OwnerNode, Unsafety,
};
use vir::def::Spanned;

use std::collections::HashMap;
use std::sync::Arc;
use vir::ast::{FunX, FunctionKind, Krate, KrateX, Path, VirErr};

fn check_item<'tcx>(
    ctxt: &Context<'tcx>,
    vir: &mut KrateX,
    mpath: Option<&Option<Path>>,
    id: &ItemId,
    item: &'tcx Item<'tcx>,
    external_info: &mut ExternalInfo,
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
                external_info,
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
                external_info,
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
            if vattrs.is_external(&ctxt.cmd_line_args) {
                return Ok(());
            }
            crate::rust_to_vir_impl::translate_impl(
                ctxt,
                vir,
                item,
                impll,
                module_path(),
                external_info,
            )?;
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
                external_info,
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

pub fn crate_to_vir<'tcx>(
    ctxt: &mut Context<'tcx>,
    imported: &Vec<Krate>,
) -> Result<(Krate, ItemToModuleMap), VirErr> {
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
                    check_item(ctxt, &mut vir, mpath, &item.item_id(), item, &mut external_info)?
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

    crate::rust_to_vir_impl::collect_external_trait_impls(
        ctxt,
        imported,
        &mut vir,
        &mut external_info,
    )?;

    crate::rust_to_vir_adts::setup_type_invariants(&mut vir)?;

    Ok((Arc::new(vir), item_to_module))
}
