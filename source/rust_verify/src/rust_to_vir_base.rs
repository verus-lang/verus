use crate::attributes::get_verifier_attrs;
use crate::context::{BodyCtxt, Context};
use crate::util::{err_span, unsupported_err_span};
use crate::verus_items::{self, BuiltinTypeItem, RustItem, VerusItem};
use crate::{unsupported_err, unsupported_err_unless};
use rustc_ast::{ByRef, Mutability};
use rustc_hir::definitions::DefPath;
use rustc_hir::{GenericParam, GenericParamKind, Generics, HirId, QPath, Ty};
use rustc_infer::infer::TyCtxtInferExt;
use rustc_middle::ty::Visibility;
use rustc_middle::ty::{AdtDef, TyCtxt, TyKind};
use rustc_middle::ty::{ClauseKind, GenericParamDefKind};
use rustc_middle::ty::{ImplPolarity, TraitPredicate};
use rustc_span::def_id::{DefId, LOCAL_CRATE};
use rustc_span::symbol::{kw, Ident};
use rustc_span::Span;
use rustc_trait_selection::infer::InferCtxtExt;
use std::collections::HashMap;
use std::sync::Arc;
use vir::ast::{
    GenericBoundX, ImplPath, IntRange, Path, PathX, Primitive, Typ, TypX, Typs, VirErr,
};
use vir::ast_util::{types_equal, undecorate_typ};
use vir::def::unique_local_name;

// TODO: eventually, this should just always be true
thread_local! {
    pub(crate) static MULTI_CRATE: std::sync::atomic::AtomicBool =
        std::sync::atomic::AtomicBool::new(false);
}

fn def_path_to_vir_path<'tcx>(tcx: TyCtxt<'tcx>, def_path: DefPath) -> Option<Path> {
    let multi_crate = MULTI_CRATE.with(|m| m.load(std::sync::atomic::Ordering::Relaxed));
    let krate = if def_path.krate == LOCAL_CRATE && !multi_crate {
        None
    } else {
        Some(Arc::new(tcx.crate_name(def_path.krate).to_string()))
    };
    let mut segments: Vec<vir::ast::Ident> = Vec::new();
    for d in def_path.data.iter() {
        use rustc_hir::definitions::DefPathData;
        match &d.data {
            DefPathData::ValueNs(symbol) | DefPathData::TypeNs(symbol) => {
                segments.push(Arc::new(symbol.to_string()));
            }
            DefPathData::Ctor => {
                segments.push(Arc::new(vir::def::RUST_DEF_CTOR.to_string()));
            }
            DefPathData::Impl => {
                segments.push(vir::def::impl_ident(d.disambiguator));
            }
            DefPathData::ForeignMod => {
                // this segment can be ignored
            }
            _ => return None,
        }
    }
    Some(Arc::new(PathX { krate, segments: Arc::new(segments) }))
}

pub(crate) fn typ_path_and_ident_to_vir_path<'tcx>(path: &Path, ident: vir::ast::Ident) -> Path {
    let mut path = (**path).clone();
    Arc::make_mut(&mut path.segments).push(ident);
    Arc::new(path)
}

// Register an alternative "friendly" paths for printing better error messages
// or for the command-line --verify-function arguments.
fn register_friendly_path_as_rust_name<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId, path: &Path) {
    let hir_id = if let Some(local_id) = def_id.as_local() {
        tcx.hir().local_def_id_to_hir_id(local_id)
    } else {
        return;
    };
    let node = tcx.hir().get(hir_id);
    let is_impl_item_fn = matches!(
        node,
        rustc_hir::Node::ImplItem(rustc_hir::ImplItem {
            kind: rustc_hir::ImplItemKind::Fn(..),
            ..
        })
    );
    if !is_impl_item_fn {
        return;
    }
    let parent_node = tcx.hir().get_parent(hir_id);
    let friendly_self_ty = match parent_node {
        rustc_hir::Node::Item(rustc_hir::Item {
            kind: rustc_hir::ItemKind::Impl(impll),
            owner_id,
            ..
        }) => match &impll.self_ty.kind {
            rustc_hir::TyKind::Path(QPath::Resolved(
                None,
                rustc_hir::Path { res: rustc_hir::def::Res::Def(_, self_def_id), .. },
            )) => def_path_to_vir_path(tcx, tcx.def_path(*self_def_id)),
            _ => {
                // To handle cases like [T] which are not syntactically datatypes
                // but converted into VIR datatypes.
                let self_ty = tcx.type_of(owner_id.to_def_id()).skip_binder();
                match self_ty.kind() {
                    TyKind::Slice(_) => Some(vir::def::slice_type()),
                    _ => None,
                }
            }
        },
        _ => None,
    };
    if let Some(ty_path) = friendly_self_ty {
        let friendly_path =
            typ_path_and_ident_to_vir_path(&ty_path, def_to_path_ident(tcx, def_id));
        vir::ast_util::set_path_as_rust_name(path, &friendly_path);
    }
}

fn def_to_path_ident<'tcx>(tcx: TyCtxt<'tcx>, def_id: DefId) -> vir::ast::Ident {
    let def_path = tcx.def_path(def_id);
    match def_path.data.last().expect("unexpected empty impl path").data {
        rustc_hir::definitions::DefPathData::ValueNs(name) => Arc::new(name.to_string()),
        _ => panic!("unexpected name of impl"),
    }
}

pub(crate) fn def_id_to_vir_path_option<'tcx>(
    tcx: TyCtxt<'tcx>,
    verus_items: &crate::verus_items::VerusItems,
    def_id: DefId,
) -> Option<Path> {
    let verus_item = verus_items.id_to_name.get(&def_id);
    if let Some(VerusItem::Pervasive(_, Some(fn_name))) = verus_item {
        // interpreter.rs and def.rs refer directly to some impl methods,
        // so make sure we use the fn_name names from `verus_items`
        let segments = fn_name.split("::").map(|x| Arc::new(x.to_string())).collect();
        let krate = Some(Arc::new("vstd".to_string()));
        return Some(Arc::new(PathX { krate, segments: Arc::new(segments) }));
    }
    let path = def_path_to_vir_path(tcx, tcx.def_path(def_id));
    if let Some(path) = &path {
        register_friendly_path_as_rust_name(tcx, def_id, path);
    }
    path
}

pub(crate) fn def_id_to_vir_path<'tcx>(
    tcx: TyCtxt<'tcx>,
    verus_items: &crate::verus_items::VerusItems,
    def_id: DefId,
) -> Path {
    def_id_to_vir_path_option(tcx, verus_items, def_id)
        .unwrap_or_else(|| panic!("unhandled name {:?}", def_id))
}

pub(crate) fn def_id_to_datatype<'tcx, 'hir>(
    tcx: TyCtxt<'tcx>,
    verus_items: &crate::verus_items::VerusItems,
    def_id: DefId,
    typ_args: Typs,
    impl_paths: vir::ast::ImplPaths,
) -> TypX {
    TypX::Datatype(def_id_to_vir_path(tcx, verus_items, def_id), typ_args, impl_paths)
}

pub(crate) fn foreign_param_to_var<'tcx>(ident: &Ident) -> String {
    ident.to_string()
}

pub(crate) fn local_to_var<'tcx>(
    ident: &Ident,
    local_id: rustc_hir::hir_id::ItemLocalId,
) -> String {
    unique_local_name(ident.to_string(), local_id.index())
}

pub(crate) fn qpath_to_ident<'tcx>(
    tcx: TyCtxt<'tcx>,
    qpath: &QPath<'tcx>,
) -> Option<vir::ast::Ident> {
    use rustc_hir::def::Res;
    use rustc_hir::{BindingAnnotation, Node, Pat, PatKind};
    if let QPath::Resolved(None, rustc_hir::Path { res: Res::Local(id), .. }) = qpath {
        if let Node::Pat(Pat {
            kind: PatKind::Binding(BindingAnnotation(ByRef::No, Mutability::Not), hir_id, x, None),
            ..
        }) = tcx.hir().get(*id)
        {
            Some(Arc::new(local_to_var(x, hir_id.local_id)))
        } else {
            None
        }
    } else {
        None
    }
}

pub(crate) fn get_impl_paths<'tcx>(
    tcx: TyCtxt<'tcx>,
    verus_items: &crate::verus_items::VerusItems,
    param_env_src: DefId,
    target_id: DefId,
    node_substs: &'tcx rustc_middle::ty::List<rustc_middle::ty::GenericArg<'tcx>>,
) -> vir::ast::ImplPaths {
    let preds = tcx.predicates_of(target_id);
    let clauses = preds.instantiate(tcx, node_substs).predicates;
    get_impl_paths_for_clauses(tcx, verus_items, param_env_src, clauses)
}

pub(crate) fn get_impl_paths_for_clauses<'tcx>(
    tcx: TyCtxt<'tcx>,
    verus_items: &crate::verus_items::VerusItems,
    param_env_src: DefId,
    clauses: Vec<rustc_middle::ty::Clause<'tcx>>,
) -> vir::ast::ImplPaths {
    let mut impl_paths = Vec::new();
    let param_env = tcx.param_env(param_env_src);

    // REVIEW: do we need this?
    // let normalized_substs = tcx.normalize_erasing_regions(param_env, node_substs);

    // Note: a worklist of impl ids might be easier to implement.
    // It would be nice simply because the number of impls is easily boundable.
    //
    // I'm not sure if it's sound, though. It might be possible for the same impl
    // to show up multiple times, but with different predicates that result in different
    // impls once you start nesting?
    // So I'm implementing this with a predicate worklist to be safe.

    let mut predicate_worklist: Vec<rustc_middle::ty::Clause> = clauses;

    let mut idx = 0;
    while idx < predicate_worklist.len() {
        if idx == 1000 {
            panic!("get_impl_paths nesting depth exceeds 1000");
        }

        let inst_pred = &predicate_worklist[idx];
        idx += 1;

        if let ClauseKind::Trait(_) = inst_pred.kind().skip_binder() {
            let inst_pred_erased = inst_pred.kind();

            let trait_refs = inst_pred_erased.map_bound(|p| {
                if let ClauseKind::Trait(tp) = &p { tp.trait_ref } else { unreachable!() }
            });

            let mut regions = HashMap::new();
            let delegate = rustc_middle::ty::fold::FnMutDelegate {
                regions: &mut |br| {
                    *regions.entry(br).or_insert(rustc_middle::ty::Region::new_free(
                        tcx,
                        param_env_src,
                        br.kind,
                    ))
                },
                types: &mut |b| panic!("unexpected bound ty in binder: {:?}", b),
                consts: &mut |b, ty| panic!("unexpected bound ct in binder: {:?} {}", b, ty),
            };
            let trait_refs = tcx.replace_escaping_bound_vars_uncached(trait_refs, delegate);

            let candidate = tcx.codegen_select_candidate((param_env, trait_refs.skip_binder()));
            if let Ok(impl_source) = candidate {
                if let rustc_middle::traits::ImplSource::UserDefined(u) = impl_source {
                    let impl_path = def_id_to_vir_path(tcx, verus_items, u.impl_def_id);
                    impl_paths.push(ImplPath::TraitImplPath(impl_path));

                    let preds = tcx.predicates_of(u.impl_def_id);
                    for p in preds.instantiate(tcx, u.args).predicates {
                        if !predicate_worklist.contains(&p) {
                            predicate_worklist.push(p);
                        }
                    }
                } else if let rustc_middle::traits::ImplSource::Builtin(
                    rustc_middle::traits::BuiltinImplSource::Misc,
                    _,
                ) = impl_source
                {
                    // When the needed trait bound is `FnDef(f) : FnOnce(...)`
                    // The `impl_source` doesn't have the information we need,
                    // so we have to special case this here.

                    // REVIEW: need to see if there are other problematic cases here;
                    // I think codegen_select_candidate lacks some information because
                    // it's used for codegen

                    match inst_pred_erased.skip_binder() {
                        ClauseKind::Trait(TraitPredicate {
                            trait_ref:
                                rustc_middle::ty::TraitRef {
                                    def_id: trait_def_id,
                                    args: trait_args,
                                    ..
                                },
                            polarity: ImplPolarity::Positive,
                        }) => {
                            if Some(trait_def_id) == tcx.lang_items().fn_trait()
                                || Some(trait_def_id) == tcx.lang_items().fn_mut_trait()
                                || Some(trait_def_id) == tcx.lang_items().fn_once_trait()
                            {
                                match trait_args.into_type_list(tcx)[0].kind() {
                                    TyKind::FnDef(fn_def_id, fn_node_substs) => {
                                        let fn_path =
                                            def_id_to_vir_path(tcx, verus_items, *fn_def_id);
                                        let fn_fun = Arc::new(vir::ast::FunX { path: fn_path });
                                        impl_paths.push(ImplPath::FnDefImplPath(fn_fun));

                                        let preds = tcx.predicates_of(fn_def_id);
                                        for p in preds.instantiate(tcx, fn_node_substs).predicates {
                                            if !predicate_worklist.contains(&p) {
                                                predicate_worklist.push(p);
                                            }
                                        }
                                    }
                                    _ => {}
                                }
                            }
                        }
                        _ => {}
                    }
                }
            }
        }
    }
    Arc::new(impl_paths)
}

pub(crate) fn mk_visibility<'tcx>(ctxt: &Context<'tcx>, def_id: DefId) -> vir::ast::Visibility {
    mk_visibility_from_vis(ctxt, ctxt.tcx.visibility(def_id))
}

pub(crate) fn mk_visibility_from_vis<'tcx>(
    ctxt: &Context<'tcx>,
    visibility: rustc_middle::ty::Visibility<DefId>,
) -> vir::ast::Visibility {
    let restricted_to = match visibility {
        Visibility::Public => None,
        Visibility::Restricted(id) => Some(def_id_to_vir_path(ctxt.tcx, &ctxt.verus_items, id)),
    };
    vir::ast::Visibility { restricted_to }
}

pub(crate) fn get_range(typ: &Typ) -> IntRange {
    match &*undecorate_typ(typ) {
        TypX::Int(range) => *range,
        _ => panic!("get_range {:?}", typ),
    }
}

pub(crate) fn mk_range<'tcx>(
    verus_items: &crate::verus_items::VerusItems,
    ty: &rustc_middle::ty::Ty<'tcx>,
) -> IntRange {
    match ty.kind() {
        TyKind::Adt(AdtDef(adt_def_data), _) => {
            let did = adt_def_data.did;
            let verus_item = verus_items.id_to_name.get(&did);
            match verus_item {
                Some(VerusItem::BuiltinType(BuiltinTypeItem::Int)) => IntRange::Int,
                Some(VerusItem::BuiltinType(BuiltinTypeItem::Nat)) => IntRange::Nat,
                _ => panic!("mk_range {:?}", ty),
            }
        }
        TyKind::Uint(rustc_middle::ty::UintTy::U8) => IntRange::U(8),
        TyKind::Uint(rustc_middle::ty::UintTy::U16) => IntRange::U(16),
        TyKind::Uint(rustc_middle::ty::UintTy::U32) => IntRange::U(32),
        TyKind::Uint(rustc_middle::ty::UintTy::U64) => IntRange::U(64),
        TyKind::Uint(rustc_middle::ty::UintTy::U128) => IntRange::U(128),
        TyKind::Uint(rustc_middle::ty::UintTy::Usize) => IntRange::USize,
        TyKind::Int(rustc_middle::ty::IntTy::I8) => IntRange::I(8),
        TyKind::Int(rustc_middle::ty::IntTy::I16) => IntRange::I(16),
        TyKind::Int(rustc_middle::ty::IntTy::I32) => IntRange::I(32),
        TyKind::Int(rustc_middle::ty::IntTy::I64) => IntRange::I(64),
        TyKind::Int(rustc_middle::ty::IntTy::I128) => IntRange::I(128),
        TyKind::Int(rustc_middle::ty::IntTy::Isize) => IntRange::ISize,
        _ => panic!("mk_range {:?}", ty),
    }
}

pub(crate) fn ty_is_global_allocator<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: &rustc_middle::ty::Ty<'tcx>,
) -> bool {
    match ty.kind() {
        TyKind::Adt(AdtDef(adt_def_data), args) => {
            let did = adt_def_data.did;
            let rust_item = verus_items::get_rust_item(tcx, did);
            if let Some(RustItem::AllocGlobal) = rust_item {
                assert!(args.len() == 0);
                true
            } else {
                false
            }
        }
        _ => false,
    }
}

pub(crate) fn mid_ty_simplify<'tcx>(
    tcx: TyCtxt<'tcx>,
    verus_items: &crate::verus_items::VerusItems,
    ty: &rustc_middle::ty::Ty<'tcx>,
    allow_mut_ref: bool,
) -> rustc_middle::ty::Ty<'tcx> {
    match ty.kind() {
        TyKind::Ref(_, t, Mutability::Not) => mid_ty_simplify(tcx, verus_items, t, allow_mut_ref),
        TyKind::Ref(_, t, Mutability::Mut) if allow_mut_ref => {
            mid_ty_simplify(tcx, verus_items, t, allow_mut_ref)
        }
        TyKind::Adt(AdtDef(adt_def_data), args) => {
            let did = adt_def_data.did;
            let is_ghost_or_tracked = matches!(
                verus_items.id_to_name.get(&did),
                Some(VerusItem::BuiltinType(BuiltinTypeItem::Ghost | BuiltinTypeItem::Tracked))
            );
            let rust_item = verus_items::get_rust_item(tcx, did);
            let is_box = rust_item == Some(verus_items::RustItem::Box);
            let is_smart_ptr =
                (matches!(rust_item, Some(verus_items::RustItem::Rc | verus_items::RustItem::Arc))
                    || is_ghost_or_tracked)
                    && args.len() == 1;
            if is_box || is_smart_ptr {
                if let rustc_middle::ty::GenericArgKind::Type(t) = args[0].unpack() {
                    mid_ty_simplify(tcx, verus_items, &t, false)
                } else {
                    panic!("unexpected type argument")
                }
            } else {
                ty.to_owned()
            }
        }
        _ => ty.to_owned(),
    }
}

// returns VIR Typ and whether Ghost/Tracked was erased from around the outside of the VIR Typ
pub(crate) fn mid_ty_to_vir_ghost<'tcx>(
    tcx: TyCtxt<'tcx>,
    verus_items: &crate::verus_items::VerusItems,
    param_env_src: DefId,
    span: Span,
    ty: &rustc_middle::ty::Ty<'tcx>,
    as_datatype: bool,
    allow_mut_ref: bool,
) -> Result<(Typ, bool), VirErr> {
    use vir::ast::TypDecoration;
    let t_rec = |t: &rustc_middle::ty::Ty<'tcx>| {
        mid_ty_to_vir_ghost(tcx, verus_items, param_env_src, span, t, as_datatype, allow_mut_ref)
    };
    let t_rec_flags = |t: &rustc_middle::ty::Ty<'tcx>, as_datatype: bool, allow_mut_ref: bool| {
        mid_ty_to_vir_ghost(tcx, verus_items, param_env_src, span, t, as_datatype, allow_mut_ref)
    };
    let t = match ty.kind() {
        TyKind::Bool => (Arc::new(TypX::Bool), false),
        TyKind::Uint(_) | TyKind::Int(_) => (Arc::new(TypX::Int(mk_range(verus_items, ty))), false),
        TyKind::Ref(_, tys, rustc_ast::Mutability::Not) => {
            let (t0, ghost) = t_rec(tys)?;
            (Arc::new(TypX::Decorate(TypDecoration::Ref, t0.clone())), ghost)
        }
        TyKind::Ref(_, tys, rustc_ast::Mutability::Mut) if allow_mut_ref => {
            let (t0, ghost) = t_rec(tys)?;
            (Arc::new(TypX::Decorate(TypDecoration::MutRef, t0.clone())), ghost)
        }
        TyKind::Param(param) if param.name == kw::SelfUpper => {
            (Arc::new(TypX::TypParam(vir::def::trait_self_type_param())), false)
        }
        TyKind::Param(param) => {
            (Arc::new(TypX::TypParam(Arc::new(param_ty_to_vir_name(param)))), false)
        }
        TyKind::Never => {
            // All types are inhabited in SMT; we pick an arbitrary inhabited type for Never
            let tuple0 = Arc::new(TypX::Tuple(Arc::new(vec![])));
            (Arc::new(TypX::Decorate(TypDecoration::Never, tuple0)), false)
        }
        TyKind::Tuple(_) => {
            let mut typs: Vec<Typ> = Vec::new();
            for t in ty.tuple_fields().iter() {
                typs.push(t_rec(&t)?.0);
            }
            (Arc::new(TypX::Tuple(Arc::new(typs))), false)
        }
        TyKind::Slice(ty) => {
            let typ = t_rec(ty)?.0;
            let typs = Arc::new(vec![typ]);
            (Arc::new(TypX::Primitive(Primitive::Slice, typs)), false)
        }
        TyKind::Array(ty, const_len) => {
            let typ = mid_ty_to_vir_ghost(
                tcx,
                verus_items,
                param_env_src,
                span,
                ty,
                as_datatype,
                allow_mut_ref,
            )?
            .0;
            let len = mid_ty_const_to_vir(tcx, Some(span), const_len)?;
            let typs = Arc::new(vec![typ, len]);
            (Arc::new(TypX::Primitive(Primitive::Array, typs)), false)
        }
        TyKind::Adt(AdtDef(adt_def_data), args) => {
            let did = adt_def_data.did;
            let is_strslice = matches!(
                verus_items.id_to_name.get(&did),
                Some(&crate::verus_items::VerusItem::Pervasive(
                    crate::verus_items::PervasiveItem::StrSlice,
                    _
                ))
            );
            if is_strslice && !as_datatype {
                return Ok((Arc::new(TypX::StrSlice), false));
            }
            let verus_item = verus_items.id_to_name.get(&did);
            if let Some(VerusItem::BuiltinType(BuiltinTypeItem::Int)) = verus_item {
                (Arc::new(TypX::Int(IntRange::Int)), false)
            } else if let Some(VerusItem::BuiltinType(BuiltinTypeItem::Nat)) = verus_item {
                (Arc::new(TypX::Int(IntRange::Nat)), false)
            } else {
                let mut typ_args: Vec<(Typ, bool)> = Vec::new();
                for arg in args.iter() {
                    match arg.unpack() {
                        rustc_middle::ty::GenericArgKind::Type(t) => {
                            typ_args.push(t_rec(&t)?);
                        }
                        rustc_middle::ty::GenericArgKind::Lifetime(_) => {}
                        rustc_middle::ty::GenericArgKind::Const(cnst) => {
                            typ_args.push((mid_ty_const_to_vir(tcx, Some(span), &cnst)?, false));
                        }
                    }
                }
                if Some(did) == tcx.lang_items().owned_box() && typ_args.len() == 2 {
                    let (t0, ghost) = &typ_args[0];

                    let allocator_arg = match args[1].unpack() {
                        rustc_middle::ty::GenericArgKind::Type(t) => t,
                        _ => {
                            panic!("Box expected type arg");
                        }
                    };
                    if !ty_is_global_allocator(tcx, &allocator_arg) {
                        unsupported_err!(span, "Box with allocator other than Global")
                    }
                    return Ok((Arc::new(TypX::Decorate(TypDecoration::Box, t0.clone())), *ghost));
                }
                if typ_args.len() >= 1 {
                    let (t0, ghost) = &typ_args[0];
                    let decorate = |d: TypDecoration, ghost: bool| {
                        Ok((Arc::new(TypX::Decorate(d, t0.clone())), ghost))
                    };
                    let verus_item = verus_items.id_to_name.get(&did);
                    let rust_item = verus_items::get_rust_item(tcx, did);
                    match (verus_item, rust_item) {
                        (Some(VerusItem::BuiltinType(BuiltinTypeItem::Ghost)), _) => {
                            assert!(typ_args.len() == 1);
                            return decorate(TypDecoration::Ghost, true);
                        }
                        (Some(VerusItem::BuiltinType(BuiltinTypeItem::Tracked)), _) => {
                            assert!(typ_args.len() == 1);
                            return decorate(TypDecoration::Tracked, true);
                        }
                        (_, Some(RustItem::Rc)) => {
                            assert!(typ_args.len() == 2);
                            return decorate(TypDecoration::Rc, *ghost);
                        }
                        (_, Some(RustItem::Arc)) => {
                            assert!(typ_args.len() == 2);
                            return decorate(TypDecoration::Arc, *ghost);
                        }
                        _ => {}
                    }
                }
                if let Some(VerusItem::BuiltinType(BuiltinTypeItem::FnSpec)) =
                    verus_items.id_to_name.get(&did)
                {
                    assert!(typ_args.len() == 2);
                    let typ_arg_tuple = typ_args[0].0.clone();
                    let ret_typ = typ_args[1].0.clone();
                    let param_typs = match &*typ_arg_tuple {
                        TypX::Tuple(typs) => typs.clone(),
                        _ => {
                            // TODO proper user-facing error msg here
                            panic!("expected first type argument of FnSpec to be a tuple");
                        }
                    };
                    return Ok((Arc::new(TypX::Lambda(param_typs, ret_typ)), false));
                }
                let typ_args = typ_args.into_iter().map(|(t, _)| t).collect();
                let impl_paths = get_impl_paths(tcx, verus_items, param_env_src, did, args);
                let datatypex =
                    def_id_to_datatype(tcx, verus_items, did, Arc::new(typ_args), impl_paths);
                (Arc::new(datatypex), false)
            }
        }
        TyKind::Closure(def, substs) => {
            let sig = substs.as_closure().sig();
            let mut args: Vec<Typ> = Vec::new();
            for t in sig.inputs().skip_binder().iter() {
                args.push(t_rec(t)?.0);
            }
            assert!(args.len() == 1);
            let args = match &*args[0] {
                TypX::Tuple(typs) => typs.clone(),
                _ => panic!("expected tuple type"),
            };

            let ret = t_rec(&sig.output().skip_binder())?.0;
            let id = def.as_local().unwrap().local_def_index.index();
            (Arc::new(TypX::AnonymousClosure(args, ret, id)), false)
        }
        TyKind::Alias(
            rustc_middle::ty::AliasKind::Projection | rustc_middle::ty::AliasKind::Inherent,
            t,
        ) => {
            // First, try to normalize to a non-projection type.
            // This can enable concrete operations on the type (e.g.
            // arithmetic if the normalized type is int) that
            // wouldn't be allowed if the type were left in an unnormalized form.
            use crate::rustc_trait_selection::traits::NormalizeExt;
            let param_env = tcx.param_env(param_env_src);
            let infcx = tcx.infer_ctxt().ignoring_regions().build();
            let cause = rustc_infer::traits::ObligationCause::dummy();
            let at = infcx.at(&cause, param_env);
            let resolved_ty = infcx.resolve_vars_if_possible(*ty);
            if !rustc_middle::ty::TypeVisitableExt::has_escaping_bound_vars(&resolved_ty) {
                let norm = at.normalize(*ty);
                if norm.value != *ty {
                    return t_rec(&norm.value);
                }
            }
            // If normalization isn't possible, return a projection type:
            let assoc_item = tcx.associated_item(t.def_id);
            let name = Arc::new(assoc_item.name.to_string());
            // Note: this looks like it would work, but trait_item_def_id is sometimes None:
            //   use crate::rustc_middle::ty::DefIdTree;
            //   let trait_def = tcx.parent(assoc_item.trait_item_def_id.expect("..."));
            let trait_def = tcx.generics_of(t.def_id).parent;
            if t.args.iter().find(|x| x.as_type().is_none()).is_some() {
                unsupported_err!(span, "projection type")
            }
            match (trait_def, t.args.into_type_list(tcx)) {
                (Some(trait_def), typs) if typs.len() >= 1 => {
                    let trait_path = def_id_to_vir_path(tcx, verus_items, trait_def);
                    // In rustc, see create_substs_for_ast_path and create_substs_for_generic_args
                    let mut trait_typ_args = Vec::new();
                    for ty in typs.iter() {
                        trait_typ_args.push(t_rec_flags(&ty, false, false)?.0);
                    }
                    let trait_typ_args = Arc::new(trait_typ_args);
                    let proj = TypX::Projection { trait_typ_args, trait_path, name };
                    return Ok((Arc::new(proj), false));
                }
                _ => {
                    unsupported_err!(span, "projection type")
                }
            }
        }
        TyKind::Alias(rustc_middle::ty::AliasKind::Opaque, _) => {
            unsupported_err!(span, "opaque type")
        }
        TyKind::Alias(rustc_middle::ty::AliasKind::Weak, _) => {
            unsupported_err!(span, "opaque type")
        }
        TyKind::FnDef(def_id, args) => {
            let param_env = tcx.param_env(param_env_src);
            let normalized_substs = tcx.normalize_erasing_regions(param_env, *args);
            let inst =
                rustc_middle::ty::Instance::resolve(tcx, param_env, *def_id, normalized_substs);
            let mut resolved = None;
            if let Ok(Some(inst)) = inst {
                if let rustc_middle::ty::InstanceDef::Item(did) = inst.def {
                    let path = def_id_to_vir_path(tcx, verus_items, did);
                    let fun = Arc::new(vir::ast::FunX { path });
                    resolved = Some(fun);
                }
            }

            let mut typ_args: Vec<(Typ, bool)> = Vec::new();
            for arg in args.iter() {
                match arg.unpack() {
                    rustc_middle::ty::GenericArgKind::Type(t) => {
                        typ_args.push(mid_ty_to_vir_ghost(
                            tcx,
                            verus_items,
                            param_env_src,
                            span,
                            &t,
                            as_datatype,
                            allow_mut_ref,
                        )?);
                    }
                    rustc_middle::ty::GenericArgKind::Lifetime(_) => {}
                    rustc_middle::ty::GenericArgKind::Const(cnst) => {
                        typ_args.push((mid_ty_const_to_vir(tcx, Some(span), &cnst)?, false));
                    }
                }
            }
            let typ_args = typ_args.into_iter().map(|(t, _)| t).collect();
            let path = def_id_to_vir_path(tcx, verus_items, *def_id);
            let fun = Arc::new(vir::ast::FunX { path });

            let typx = TypX::FnDef(fun, Arc::new(typ_args), resolved);
            (Arc::new(typx), false)
        }
        TyKind::Char => (Arc::new(TypX::Char), false),

        TyKind::Float(..) => unsupported_err!(span, "floating point types"),
        TyKind::Foreign(..) => unsupported_err!(span, "foreign types"),
        TyKind::Str => unsupported_err!(span, "str type"),
        TyKind::RawPtr(..) => unsupported_err!(span, "raw pointer types"),
        TyKind::Ref(_, _, rustc_ast::Mutability::Mut) => {
            unsupported_err!(span, "&mut types, except in special cases")
        }
        TyKind::FnPtr(..) => unsupported_err!(span, "function pointer types"),
        TyKind::Dynamic(..) => unsupported_err!(span, "dynamic types"),
        TyKind::Generator(..) => unsupported_err!(span, "generator types"),
        TyKind::GeneratorWitness(..) => unsupported_err!(span, "generator witness types"),
        TyKind::GeneratorWitnessMIR(_, _) => unsupported_err!(span, "generator witness mir types"),
        TyKind::Bound(..) => unsupported_err!(span, "for<'a> types"),
        TyKind::Placeholder(..) => unsupported_err!(span, "type inference placeholder types"),
        TyKind::Infer(..) => unsupported_err!(span, "type inference placeholder types"),
        TyKind::Error(..) => unsupported_err!(span, "type inference placeholder error types"),
    };
    Ok(t)
}

/*
pub(crate) fn mid_ty_to_vir_datatype<'tcx>(
    tcx: TyCtxt<'tcx>,
    verus_items: &crate::verus_items::VerusItems,
    param_env_src: DefId,
    span: Span,
    ty: rustc_middle::ty::Ty<'tcx>,
    allow_mut_ref: bool,
) -> Result<Typ, VirErr> {
    Ok(mid_ty_to_vir_ghost(tcx, verus_items, param_env_src, span, &ty, true, allow_mut_ref)?.0)
}
*/

// TODO: rename this back to mid_ty_to_vir
pub(crate) fn mid_ty_to_vir<'tcx>(
    tcx: TyCtxt<'tcx>,
    verus_items: &crate::verus_items::VerusItems,
    param_env_src: DefId,
    span: Span,
    ty: &rustc_middle::ty::Ty<'tcx>,
    allow_mut_ref: bool,
) -> Result<Typ, VirErr> {
    Ok(mid_ty_to_vir_ghost(tcx, verus_items, param_env_src, span, ty, false, allow_mut_ref)?.0)
}

pub(crate) fn mid_ty_const_to_vir<'tcx>(
    tcx: TyCtxt<'tcx>,
    span: Option<Span>,
    cnst: &rustc_middle::ty::Const<'tcx>,
) -> Result<Typ, VirErr> {
    // use rustc_middle::mir::interpret::{ConstValue, Scalar};
    use rustc_middle::ty::ConstKind;
    use rustc_middle::ty::ValTree;

    let cnst = match cnst.kind() {
        ConstKind::Unevaluated(unevaluated) => cnst.eval(tcx, tcx.param_env(unevaluated.def)),
        _ => *cnst,
    };
    match cnst.kind() {
        ConstKind::Param(param) => Ok(Arc::new(TypX::TypParam(Arc::new(param.name.to_string())))),
        ConstKind::Value(ValTree::Leaf(i)) => {
            let c = num_bigint::BigInt::from(i.assert_bits(i.size()));
            Ok(Arc::new(TypX::ConstInt(c)))
        }
        _ => {
            unsupported_err!(span.expect("span"), format!("const type argument {:?}", cnst))
        }
    }
}

pub(crate) fn is_type_std_rc_or_arc_or_ref<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: rustc_middle::ty::Ty<'tcx>,
) -> bool {
    match ty.kind() {
        TyKind::Adt(AdtDef(adt_def_data), _args) => {
            let did = adt_def_data.did;
            if let Some(RustItem::Rc | RustItem::Arc) = verus_items::get_rust_item(tcx, did) {
                return true;
            }
        }
        TyKind::Ref(_, _, Mutability::Not) => {
            return true;
        }
        _ => {}
    }
    false
}

// TODO remove if unused
pub(crate) fn _ty_resolved_path_to_debug_path(_tcx: TyCtxt<'_>, ty: &Ty) -> String {
    let Ty { hir_id: _, kind, span: _ } = ty;
    match kind {
        rustc_hir::TyKind::Path(QPath::Resolved(None, path)) => path
            .segments
            .iter()
            .map(|x| x.ident.name.to_ident_string())
            .collect::<Vec<_>>()
            .join("::"),
        _ => panic!("{:?} does not have a resolved path", ty),
    }
}

pub(crate) fn typ_of_node<'tcx>(
    bctx: &BodyCtxt<'tcx>,
    span: Span,
    id: &HirId,
    allow_mut_ref: bool,
) -> Result<Typ, VirErr> {
    mid_ty_to_vir(
        bctx.ctxt.tcx,
        &bctx.ctxt.verus_items,
        bctx.fun_id,
        span,
        &bctx.types.node_type(*id),
        allow_mut_ref,
    )
}

pub(crate) fn typ_of_node_expect_mut_ref<'tcx>(
    bctx: &BodyCtxt<'tcx>,
    span: Span,
    id: &HirId,
) -> Result<Typ, VirErr> {
    let ty = bctx.types.node_type(*id);
    if let TyKind::Ref(_, _tys, rustc_ast::Mutability::Mut) = ty.kind() {
        mid_ty_to_vir(bctx.ctxt.tcx, &bctx.ctxt.verus_items, bctx.fun_id, span, &ty, true)
    } else {
        err_span(span, "a mutable reference is expected here")
    }
}

pub(crate) fn implements_structural<'tcx>(
    ctxt: &Context<'tcx>,
    ty: rustc_middle::ty::Ty<'tcx>,
) -> bool {
    let structural_def_id = ctxt
        .verus_items
        .name_to_id
        .get(&VerusItem::Marker(crate::verus_items::MarkerItem::Structural))
        .expect("structural trait is not defined");

    use crate::rustc_middle::ty::TypeVisitableExt;
    let infcx = ctxt.tcx.infer_ctxt().build(); // TODO(main_new) correct?
    let ty = ctxt.tcx.erase_regions(ty);
    if ty.has_escaping_bound_vars() {
        return false;
    }
    let ty_impls_structural = infcx
        .type_implements_trait(
            *structural_def_id,
            vec![ty].into_iter(),
            rustc_middle::ty::ParamEnv::empty(),
        )
        .must_apply_modulo_regions();
    ty_impls_structural
}

// Do equality operations on these operands translate into the SMT solver's == operation?
pub(crate) fn is_smt_equality<'tcx>(
    bctx: &BodyCtxt<'tcx>,
    span: Span,
    id1: &HirId,
    id2: &HirId,
) -> Result<bool, VirErr> {
    let (t1, t2) = (typ_of_node(bctx, span, id1, false)?, typ_of_node(bctx, span, id2, false)?);
    match (&*undecorate_typ(&t1), &*undecorate_typ(&t2)) {
        (TypX::Bool, TypX::Bool) => Ok(true),
        (TypX::Int(_), TypX::Int(_)) => Ok(true),
        (TypX::Char, TypX::Char) => Ok(true),
        (TypX::Datatype(..), TypX::Datatype(..)) if types_equal(&t1, &t2) => {
            let ty = bctx.types.node_type(*id1);
            Ok(implements_structural(&bctx.ctxt, ty))
        }
        _ => Ok(false),
    }
}

// Do arithmetic operations on these operands translate into the SMT solver's <=, +, =>, etc.?
// (possibly with clipping/wrapping for finite-size integers?)
pub(crate) fn is_smt_arith<'tcx>(
    bctx: &BodyCtxt<'tcx>,
    span1: Span,
    span2: Span,
    id1: &HirId,
    id2: &HirId,
) -> Result<bool, VirErr> {
    let (t1, t2) = (typ_of_node(bctx, span1, id1, false)?, typ_of_node(bctx, span2, id2, false)?);
    match (&*undecorate_typ(&t1), &*undecorate_typ(&t2)) {
        (TypX::Bool, TypX::Bool) => Ok(true),
        (TypX::Int(_), TypX::Int(_)) => Ok(true),
        _ => Ok(false),
    }
}

pub(crate) fn check_generic_bound<'tcx>(
    tcx: TyCtxt<'tcx>,
    verus_items: &crate::verus_items::VerusItems,
    param_env_src: DefId,
    span: Span,
    trait_def_id: DefId,
    args: &Vec<rustc_middle::ty::Ty<'tcx>>,
) -> Result<Option<vir::ast::GenericBound>, VirErr> {
    if Some(trait_def_id) == tcx.lang_items().sized_trait()
        || Some(trait_def_id) == tcx.lang_items().copy_trait()
        || Some(trait_def_id) == tcx.lang_items().unpin_trait()
        || Some(trait_def_id) == tcx.lang_items().sync_trait()
        || Some(trait_def_id) == tcx.lang_items().tuple_trait()
        || Some(trait_def_id) == tcx.get_diagnostic_item(rustc_span::sym::Send)
    {
        // Rust language marker traits are ignored in VIR
        Ok(None)
    } else {
        let vir_args = args
            .iter()
            .map(|arg| mid_ty_to_vir(tcx, verus_items, param_env_src, span, arg, false))
            .collect::<Result<Vec<_>, _>>()?;
        let trait_name = def_id_to_vir_path(tcx, verus_items, trait_def_id);
        Ok(Some(Arc::new(GenericBoundX::Trait(trait_name, Arc::new(vir_args)))))
    }
}

// These 2 functions map a GenericParamDef or ParamTy to the name we use for that type
// parameter in VIR.
//
// In rustc_middle, all the type params have a symbol and an index.
// The indices are all unique. The symbols are unique for all the user-declared type
// params, but they aren't necessarily unique for synthetic params.
// (A synthetic param is a nameless type parameter created when the user writes
// something like `x: impl SomeTrait`.)
//
// In order to keep the AIR readable, though, we want to use the symbol names when
// possible. So:
//  - For synthetic params, use impl%{index} for the name.
//  - For other type params, just use the user-given type param name.

fn generic_param_def_to_vir_name(gen: &rustc_middle::ty::GenericParamDef) -> String {
    let is_synthetic = match gen.kind {
        GenericParamDefKind::Type { synthetic, .. } => synthetic,
        GenericParamDefKind::Const { .. } => false,
        _ => panic!("expected GenericParamDefKind::Type"),
    };

    if is_synthetic {
        vir::def::PREFIX_IMPL_TYPE_PARAM.to_string() + &gen.index.to_string()
    } else {
        gen.name.as_str().to_string()
    }
}

pub(crate) fn param_ty_to_vir_name(param: &rustc_middle::ty::ParamTy) -> String {
    let name = param.name.as_str();
    if name.starts_with("impl ") {
        vir::def::PREFIX_IMPL_TYPE_PARAM.to_string() + &param.index.to_string()
    } else {
        name.to_string()
    }
}

pub(crate) fn process_predicate_bounds<'tcx, 'a>(
    tcx: TyCtxt<'tcx>,
    param_env_src: DefId,
    verus_items: &crate::verus_items::VerusItems,
    predicates: impl Iterator<Item = &'a (rustc_middle::ty::Clause<'tcx>, Span)>,
) -> Result<Vec<vir::ast::GenericBound>, VirErr>
where
    'tcx: 'a,
{
    let mut bounds: Vec<vir::ast::GenericBound> = Vec::new();
    for (predicate, span) in predicates {
        // REVIEW: rustc docs say that skip_binder is "dangerous"
        match predicate.kind().skip_binder() {
            ClauseKind::RegionOutlives(_) | ClauseKind::TypeOutlives(_) => {
                // can ignore lifetime bounds
            }
            ClauseKind::Trait(TraitPredicate { trait_ref, polarity: ImplPolarity::Positive }) => {
                let substs = trait_ref.args;

                // For a bound like `T: SomeTrait<X, Y, Z>`, then:
                // T should be index 0,
                // X, Y, Z, should be the rest
                // The SomeTrait is given by the def_id

                // Note: I _think_ rustc organizes it this way because
                // T, X, Y, Z are actually all handled symmetrically
                // in the formal theory of Rust's traits;
                // i.e., the `Self` of a trait is actually the same as any of the other
                // type parameters, it's just special in the notation for convenience.
                //
                // Right now Verus only allows `Self` (in the example, `T`) to be a type param,
                // and it doesn't have full support for the other type params, so we special
                // case it here.

                let trait_def_id = trait_ref.def_id;

                if Some(trait_def_id) == tcx.lang_items().fn_trait()
                    || Some(trait_def_id) == tcx.lang_items().fn_mut_trait()
                    || Some(trait_def_id) == tcx.lang_items().fn_once_trait()
                {
                    // Ignore Fn bounds
                    continue;
                }

                let trait_params: Vec<rustc_middle::ty::Ty> = substs.types().collect();
                let generic_bound = check_generic_bound(
                    tcx,
                    verus_items,
                    param_env_src,
                    *span,
                    trait_def_id,
                    &trait_params,
                )?;
                if let Some(bound) = generic_bound {
                    bounds.push(bound);
                }
            }
            ClauseKind::Projection(pred) => {
                let item_def_id = pred.projection_ty.def_id;
                // The trait bound `F: Fn(A) -> B`
                // is really more like a trait bound `F: Fn<A, Output=B>`
                // The trait bounds that use = are called projections.
                // When Rust sees a trait bound like this, it actually creates *two*
                // bounds, a Trait bound for `F: Fn<A>` and a Projection for `Output=B`.
                //
                // We don't handle projections in general right now, but we skip
                // over them to support Fns
                // (What Verus actually cares about is the builtin 'FnWithSpecification'
                // trait which Fn/FnMut/FnOnce all get automatically.)

                if Some(item_def_id) == tcx.lang_items().fn_once_output() {
                    // Do nothing
                } else {
                    return err_span(*span, "Verus does yet not support this type of bound");
                }
            }
            ClauseKind::ConstArgHasType(..) => {
                // Do nothing
            }
            _ => {
                return err_span(*span, "Verus does yet not support this type of bound");
            }
        }
    }
    Ok(bounds)
}

pub(crate) fn check_generics_bounds<'tcx>(
    tcx: TyCtxt<'tcx>,
    verus_items: &crate::verus_items::VerusItems,
    hir_generics: &'tcx Generics<'tcx>,
    check_that_external_body_datatype_declares_positivity: bool,
    def_id: DefId,
    vattrs: Option<&crate::attributes::VerifierAttrs>,
    mut diagnostics: Option<&mut Vec<vir::ast::VirErrAs>>,
) -> Result<(vir::ast::TypPositives, vir::ast::GenericBounds), VirErr> {
    // TODO the 'predicates' object contains the parent def_id; we can use that
    // to handle all the params and bounds from the impl at once,
    // so then we can handle the case where a method adds extra bounds to an impl
    // type parameter

    let Generics {
        params: hir_params,
        has_where_clause_predicates: _,
        predicates: _,
        where_clause_span: _,
        span: generics_span,
    } = hir_generics;
    let generics = tcx.generics_of(def_id);

    let mut mid_params: Vec<&rustc_middle::ty::GenericParamDef> = vec![];
    for param in generics.params.iter() {
        match &param.kind {
            GenericParamDefKind::Lifetime { .. } => {} // ignore
            GenericParamDefKind::Type { .. } | GenericParamDefKind::Const { .. } => {
                mid_params.push(param);
            }
        }
    }

    let hir_params: Vec<&GenericParam> = hir_params
        .iter()
        .filter(|p| {
            match &p.kind {
                GenericParamKind::Lifetime { kind: _ } => false, // ignore
                GenericParamKind::Type { default: _, synthetic: _ } => true,
                GenericParamKind::Const { ty: _, default: _ } => true,
            }
        })
        .collect();

    let mut typ_params: Vec<(vir::ast::Ident, vir::ast::AcceptRecursiveType)> = Vec::new();

    // Process all trait bounds.
    let predicates = tcx.predicates_of(def_id);
    let bounds = process_predicate_bounds(tcx, def_id, verus_items, predicates.predicates.iter())?;

    // In traits, the first type param is Self. This is handled specially,
    // so we skip it here.
    // (Skipping it also allows the HIR type params and middle type params to line up.)
    let first_param_is_self = mid_params.len() > 0 && mid_params[0].name == kw::SelfUpper;
    let skip_n = if first_param_is_self { 1 } else { 0 };

    assert!(hir_params.len() + skip_n == mid_params.len());

    use vir::ast::AcceptRecursiveType;
    let mut accept_recs: HashMap<String, AcceptRecursiveType> = HashMap::new();
    if let Some(vattrs) = vattrs {
        for (x, acc) in &vattrs.accept_recursive_type_list {
            if accept_recs.contains_key(x) {
                return err_span(*generics_span, format!("duplicate parameter attribute {x}"));
            }
            accept_recs.insert(x.clone(), *acc);
        }
    }

    for (idx, mid_param) in mid_params.iter().skip(skip_n).enumerate() {
        match mid_param.kind {
            GenericParamDefKind::Type { .. } | GenericParamDefKind::Const { .. } => {}
            _ => {
                continue;
            }
        }

        // We still need to look at the HIR param because we need to check the attributes.
        let hir_param = &hir_params[idx];

        let vattrs = get_verifier_attrs(
            tcx.hir().attrs(hir_param.hir_id),
            if let Some(diagnostics) = &mut diagnostics { Some(diagnostics) } else { None },
        )?;
        let mut neg = vattrs.reject_recursive_types;
        let mut pos_some = vattrs.reject_recursive_types_in_ground_variants;
        let mut pos_all = vattrs.accept_recursive_types;
        let param_name = generic_param_def_to_vir_name(mid_param);
        match accept_recs.get(&param_name) {
            None => {}
            Some(AcceptRecursiveType::Reject) => neg = true,
            Some(AcceptRecursiveType::RejectInGround) => pos_some = true,
            Some(AcceptRecursiveType::Accept) => pos_all = true,
        }
        if accept_recs.contains_key(&param_name) {
            accept_recs.remove(&param_name);
        }
        let accept_rec = match (neg, pos_some, pos_all) {
            (true, false, false) => AcceptRecursiveType::Reject,
            // RejectInGround is the default
            (false, true, false) | (false, false, false) => AcceptRecursiveType::RejectInGround,
            (false, false, true) => AcceptRecursiveType::Accept,
            _ => {
                return err_span(
                    hir_param.span,
                    "type parameter can only have one of reject_recursive_types, reject_recursive_types_in_ground_variants, accept_recursive_types",
                );
            }
        };
        let GenericParam {
            hir_id: _,
            name: _,
            span,
            pure_wrt_drop,
            kind,
            def_id: _,
            colon_span: _,
            source: _,
        } = hir_param;

        unsupported_err_unless!(!pure_wrt_drop, *span, "generic pure_wrt_drop");

        if let GenericParamKind::Type { .. } = kind {
            if check_that_external_body_datatype_declares_positivity
                && !neg
                && !pos_some
                && !pos_all
            {
                return err_span(
                    *span,
                    "in external_body datatype, each type parameter must be one of: #[verifier::reject_recursive_types], #[verifier::reject_recursive_types_in_ground_variants], #[verifier::accept_recursive_types] (reject_recursive_types is always safe to use)",
                );
            }
        } else if let GenericParamKind::Const { .. } = kind {
        } else {
            panic!("mid_param is a Type, so we expected the HIR param to be a Type");
        }

        match &mid_param.kind {
            GenericParamDefKind::Const { .. }
            | GenericParamDefKind::Type { has_default: false, synthetic: true | false } => {
                // trait/function bounds
                typ_params.push((Arc::new(param_name), accept_rec));
            }
            _ => {
                unsupported_err!(*span, "this kind of generic param");
            }
        }
    }
    for x in accept_recs.keys() {
        return err_span(*generics_span, format!("unused parameter attribute {x}"));
    }
    Ok((Arc::new(typ_params), Arc::new(bounds)))
}

pub(crate) fn check_generics_bounds_fun<'tcx>(
    tcx: TyCtxt<'tcx>,
    verus_items: &crate::verus_items::VerusItems,
    generics: &'tcx Generics<'tcx>,
    def_id: DefId,
    diagnostics: Option<&mut Vec<vir::ast::VirErrAs>>,
) -> Result<(vir::ast::Idents, vir::ast::GenericBounds), VirErr> {
    let (typ_params, typ_bounds) =
        check_generics_bounds(tcx, verus_items, generics, false, def_id, None, diagnostics)?;
    let typ_params = typ_params.iter().map(|(x, _)| x.clone()).collect();
    Ok((Arc::new(typ_params), typ_bounds))
}

pub(crate) fn auto_deref_supported_for_ty<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: &rustc_middle::ty::Ty<'tcx>,
) -> bool {
    match ty.kind() {
        TyKind::Adt(AdtDef(adt_def_data), _args) => {
            let did = adt_def_data.did;
            let rust_item = verus_items::get_rust_item(tcx, did);
            return matches!(rust_item, Some(RustItem::Box | RustItem::Rc | RustItem::Arc));
        }
        _ => false,
    }
}
