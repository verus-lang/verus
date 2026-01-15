use crate::attributes::get_verifier_attrs;
use crate::config::new_mut_ref;
use crate::context::{BodyCtxt, Context};
use crate::resolve_traits::{ResolutionResult, ResolvedItem};
use crate::rust_to_vir_impl::ExternalInfo;
use crate::util::err_span;
use crate::verus_items::{self, BuiltinTypeItem, RustItem, VerusItem};
use crate::{unsupported_err, unsupported_err_unless};
use rustc_ast::{BindingMode, ByRef, Mutability};
use rustc_hir::definitions::DefPath;
use rustc_hir::{GenericParam, GenericParamKind, Generics, HirId, LifetimeParamKind, QPath, Ty};
use rustc_infer::infer::TyCtxtInferExt;
use rustc_middle::ty::{
    AdtDef, BoundVarIndexKind, BoundVarReplacerDelegate, Clause, ClauseKind, ConstKind, GenericArg,
    GenericArgKind, GenericParamDefKind, TermKind, TyCtxt, TyKind, TypeFoldable, TypeFolder,
    TypeSuperFoldable, TypeVisitableExt, TypingMode, ValTreeKind, Value, Visibility,
};
use rustc_middle::ty::{TraitPredicate, TypingEnv};
use rustc_span::Span;
use rustc_span::def_id::{DefId, LOCAL_CRATE};
use rustc_span::symbol::{Ident, kw};
use rustc_trait_selection::infer::InferCtxtExt;
use std::collections::HashMap;
use std::sync::Arc;
use vir::ast::{
    Dt, GenericBoundX, Idents, ImplPath, IntRange, IntegerTypeBitwidth, Mode, OpaqueTypeX, Path,
    PathX, Primitive, Sizedness, TraitId, Typ, TypDecorationArg, TypX, Typs, VarIdent, VirErr,
    VirErrAs,
};
use vir::ast_util::{str_unique_var, types_equal, undecorate_typ};

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
            DefPathData::OpaqueTy => {
                segments.push(Arc::new(
                    vir::def::RUST_OPAQUE_TYPE.to_string() + &d.disambiguator.to_string(),
                ));
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
        tcx.local_def_id_to_hir_id(local_id)
    } else {
        return;
    };
    let node = tcx.hir_node(hir_id);
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
    let mut parent_node = tcx.hir_parent_iter(hir_id);
    let (_, parent_node) = parent_node.next().expect("unexpected empty impl path");
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

pub(crate) fn def_id_to_friendly<'tcx>(
    tcx: TyCtxt<'tcx>,
    verus_items: Option<&crate::verus_items::VerusItems>,
    def_id: DefId,
) -> String {
    match def_id_to_vir_path_option(tcx, verus_items, def_id) {
        None => format!("{:?}", def_id),
        Some(p) => vir::ast_util::path_as_friendly_rust_name(&p),
    }
}

pub(crate) fn def_id_to_vir_path_option<'tcx>(
    tcx: TyCtxt<'tcx>,
    verus_items: Option<&crate::verus_items::VerusItems>,
    def_id: DefId,
) -> Option<Path> {
    if let Some(verus_items) = verus_items {
        let verus_item = verus_items.id_to_name.get(&def_id);
        if let Some(VerusItem::Vstd(_, Some(fn_name))) = verus_item {
            // interpreter.rs and def.rs refer directly to some impl methods,
            // so make sure we use the fn_name names from `verus_items`
            let segments = fn_name.split("::").map(|x| Arc::new(x.to_string())).collect();
            let krate = Some(Arc::new("vstd".to_string()));
            return Some(Arc::new(PathX { krate, segments: Arc::new(segments) }));
        }
    }
    let path = def_path_to_vir_path(tcx, tcx.def_path(def_id));
    if let Some(path) = &path {
        register_friendly_path_as_rust_name(tcx, def_id, path);
    }
    path
}

pub(crate) fn def_id_to_vir_path_ignoring_diagnostic_rename<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
) -> Path {
    def_id_to_vir_path_option(tcx, None, def_id)
        .unwrap_or_else(|| panic!("unhandled name {:?}", def_id))
}

pub(crate) fn def_id_to_vir_path<'tcx>(
    tcx: TyCtxt<'tcx>,
    verus_items: &crate::verus_items::VerusItems,
    def_id: DefId,
    path_def_id_map: Option<std::cell::RefMut<HashMap<Path, DefId>>>,
) -> Path {
    let result = def_id_to_vir_path_option(tcx, Some(verus_items), def_id)
        .unwrap_or_else(|| panic!("unhandled name {:?}", def_id));
    match path_def_id_map {
        Some(mut map) => map.insert(result.clone(), def_id),
        None => None,
    };
    result
}

pub(crate) fn def_id_to_datatype<'tcx, 'hir>(
    tcx: TyCtxt<'tcx>,
    verus_items: &crate::verus_items::VerusItems,
    path_def_id_map: Option<std::cell::RefMut<HashMap<Path, DefId>>>,
    def_id: DefId,
    typ_args: Typs,
    impl_paths: vir::ast::ImplPaths,
) -> TypX {
    TypX::Datatype(
        Dt::Path(def_id_to_vir_path(tcx, verus_items, def_id, path_def_id_map)),
        typ_args,
        impl_paths,
    )
}

pub(crate) fn no_body_param_to_var<'tcx>(ident: &Ident) -> VarIdent {
    str_unique_var(ident.as_str(), vir::ast::VarIdentDisambiguate::NoBodyParam)
}

pub(crate) fn local_to_var<'tcx>(
    ident: &Ident,
    local_id: rustc_hir::hir_id::ItemLocalId,
) -> VarIdent {
    let dis = vir::ast::VarIdentDisambiguate::RustcId(local_id.index());
    str_unique_var(&ident.to_string(), dis)
}

pub(crate) fn qpath_to_ident<'tcx>(
    tcx: TyCtxt<'tcx>,
    qpath: &QPath<'tcx>,
) -> Option<vir::ast::VarIdent> {
    use rustc_hir::def::Res;
    use rustc_hir::{Node, Pat, PatKind};
    if let QPath::Resolved(None, rustc_hir::Path { res: Res::Local(id), .. }) = qpath {
        if let Node::Pat(Pat {
            kind: PatKind::Binding(BindingMode(ByRef::No, Mutability::Not), hir_id, x, None),
            ..
        }) = tcx.hir_node(*id)
        {
            Some(local_to_var(x, hir_id.local_id))
        } else {
            None
        }
    } else {
        None
    }
}

pub(crate) fn clean_all_escaping_bound_vars<
    'tcx,
    T: rustc_middle::ty::TypeFoldable<TyCtxt<'tcx>>,
>(
    tcx: TyCtxt<'tcx>,
    value: T,
    param_env_src: DefId,
) -> T {
    let mut regions = HashMap::new();
    let delegate = rustc_middle::ty::FnMutDelegate {
        regions: &mut |br| {
            *regions.entry(br).or_insert(rustc_middle::ty::Region::new_late_param(
                tcx,
                param_env_src,
                rustc_middle::ty::LateParamRegionKind::from_bound(br.var, br.kind),
            ))
        },
        types: &mut |b| panic!("unexpected bound ty in binder: {:?}", b),
        consts: &mut |b| panic!("unexpected bound ct in binder: {:?}", b),
    };

    replace_all_escaping_bound_vars_uncached(tcx, value, delegate)
}

// This implementation is based off of of the impl of
// replace_escaping_bound_vars with a minor change
// https://doc.rust-lang.org/1.73.0/nightly-rustc/src/rustc_middle/ty/fold.rs.html#296
//
// The reason we need to modify it is this:
// when we move into a binder (via 'skip_binder') we need to
// replace all the vars in the binder. 'replace_escaping_bound_vars_uncached' is meant
// to do this, but it only replaces the vars at one level, the level currently being
// stripped off. However, when we're ready to call this, we might have already
// called skip_binder multiple times before ever even calling get_impl_paths.
//
// This modified version of replace_escaping_bound_vars_uncached will replace ALL
// escaped bound vars, including the ones at higher binding levels.
fn replace_all_escaping_bound_vars_uncached<
    'tcx,
    T: rustc_middle::ty::TypeFoldable<TyCtxt<'tcx>>,
>(
    tcx: TyCtxt<'tcx>,
    value: T,
    delegate: impl BoundVarReplacerDelegate<'tcx>,
) -> T {
    if !value.has_escaping_bound_vars() {
        value
    } else {
        let mut replacer = BoundVarReplacer::new(tcx, delegate);
        value.fold_with(&mut replacer)
    }
}

struct BoundVarReplacer<'tcx, D> {
    tcx: TyCtxt<'tcx>,
    current_index: rustc_middle::ty::DebruijnIndex,
    delegate: D,
}

impl<'tcx, D: BoundVarReplacerDelegate<'tcx>> BoundVarReplacer<'tcx, D> {
    fn new(tcx: TyCtxt<'tcx>, delegate: D) -> Self {
        BoundVarReplacer { tcx, current_index: rustc_middle::ty::INNERMOST, delegate }
    }
}

impl<'tcx, D> TypeFolder<TyCtxt<'tcx>> for BoundVarReplacer<'tcx, D>
where
    D: BoundVarReplacerDelegate<'tcx>,
{
    fn cx(&self) -> TyCtxt<'tcx> {
        self.tcx
    }

    fn fold_binder<T: TypeFoldable<TyCtxt<'tcx>>>(
        &mut self,
        t: rustc_middle::ty::Binder<'tcx, T>,
    ) -> rustc_middle::ty::Binder<'tcx, T> {
        self.current_index.shift_in(1);
        let t = t.super_fold_with(self);
        self.current_index.shift_out(1);
        t
    }

    fn fold_ty(&mut self, t: rustc_middle::ty::Ty<'tcx>) -> rustc_middle::ty::Ty<'tcx> {
        match *t.kind() {
            rustc_middle::ty::Bound(BoundVarIndexKind::Bound(debruijn), bound_ty)
                if debruijn == self.current_index =>
            {
                let ty = self.delegate.replace_ty(bound_ty);
                debug_assert!(!ty.has_vars_bound_above(rustc_middle::ty::INNERMOST));
                rustc_middle::ty::shift_vars(self.tcx, ty, self.current_index.as_u32())
            }
            _ if t.has_vars_bound_at_or_above(self.current_index) => t.super_fold_with(self),
            _ => t,
        }
    }

    fn fold_region(&mut self, r: rustc_middle::ty::Region<'tcx>) -> rustc_middle::ty::Region<'tcx> {
        match r.kind() {
            // NOTE(verus): This is the one change, we replace == with >=
            rustc_middle::ty::ReBound(BoundVarIndexKind::Bound(debruijn), br)
                if debruijn >= self.current_index =>
            {
                let region = self.delegate.replace_region(br);
                if let rustc_middle::ty::ReBound(BoundVarIndexKind::Bound(debruijn1), br) =
                    region.kind()
                {
                    assert_eq!(debruijn1, rustc_middle::ty::INNERMOST);
                    rustc_middle::ty::Region::new_bound(self.tcx, debruijn, br)
                } else {
                    region
                }
            }
            _ => r,
        }
    }

    fn fold_const(&mut self, ct: rustc_middle::ty::Const<'tcx>) -> rustc_middle::ty::Const<'tcx> {
        match ct.kind() {
            ConstKind::Bound(BoundVarIndexKind::Bound(debruijn), bound_const)
                if debruijn == self.current_index =>
            {
                let ct = self.delegate.replace_const(bound_const);
                debug_assert!(!ct.has_vars_bound_above(rustc_middle::ty::INNERMOST));
                rustc_middle::ty::shift_vars(self.tcx, ct, self.current_index.as_u32())
            }
            _ => ct.super_fold_with(self),
        }
    }

    fn fold_predicate(
        &mut self,
        p: rustc_middle::ty::Predicate<'tcx>,
    ) -> rustc_middle::ty::Predicate<'tcx> {
        if p.has_vars_bound_at_or_above(self.current_index) { p.super_fold_with(self) } else { p }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct ClauseFrom<'tcx> {
    clause: Clause<'tcx>,
    is_self_trait_bound: bool,
    source_id: DefId,
    span: Span,
}

fn instantiate_pred_clauses<'tcx>(
    tcx: TyCtxt<'tcx>,
    mut def_id: DefId,
    args: rustc_middle::ty::GenericArgsRef<'tcx>,
) -> Vec<(Option<ClauseFrom<'tcx>>, Clause<'tcx>)> {
    // We could get the information directly like this:
    let direct_clauses = tcx.predicates_of(def_id).instantiate(tcx, args).predicates;
    // but we need a little more information, so we manually reimplement some of instantiate here:
    let mut ancestors: Vec<DefId> = Vec::new();
    loop {
        ancestors.push(def_id);
        let preds = tcx.predicates_of(def_id);
        if let Some(id) = preds.parent {
            def_id = id;
        } else {
            break;
        }
    }
    let mut clauses: Vec<(Option<ClauseFrom<'tcx>>, Clause<'tcx>)> = Vec::new();
    for def_id in ancestors.iter().rev() {
        let preds = tcx.predicates_of(def_id);
        for (clause, span) in preds.predicates {
            // This is based on GenericPredicates.instantiate_into, which is close to what
            // we need but doesn't track the relation between the uninstantiated and
            // instantiated clauses.
            let inst = rustc_middle::ty::EarlyBinder::bind(*clause).instantiate(tcx, args);
            let is_self_trait_bound = *span == rustc_span::DUMMY_SP;
            if is_self_trait_bound {
                if let ClauseKind::Trait(TraitPredicate { trait_ref, .. }) =
                    clause.kind().skip_binder()
                {
                    assert!(trait_ref.def_id == *def_id);
                    assert!(args.len() > 0);
                    match trait_ref.args.types().collect::<Vec<_>>()[0].kind() {
                        TyKind::Param(param) if param.name == kw::SelfUpper => (),
                        _ => panic!("expected Self: Trait bound to have args[0] = Self"),
                    }
                } else {
                    panic!("expected Self: Trait bound to be TraitPredicate");
                }
            }
            let clause_from = ClauseFrom {
                clause: *clause,
                is_self_trait_bound,
                source_id: *def_id,
                span: *span,
            };
            clauses.push((Some(clause_from), inst));
        }
    }
    // just in case, check that the results mach the direct version of instantiate:
    assert!(direct_clauses == clauses.iter().map(|(_, c)| *c).collect::<Vec<_>>());
    clauses
}

pub(crate) fn get_impl_paths<'tcx>(
    tcx: TyCtxt<'tcx>,
    verus_items: &crate::verus_items::VerusItems,
    param_env_src: DefId,
    target_id: DefId,
    node_substs: &'tcx rustc_middle::ty::List<rustc_middle::ty::GenericArg<'tcx>>,
    remove_self_trait_bound: Option<(DefId, &mut Option<vir::ast::ImplPath>)>,
) -> vir::ast::ImplPaths {
    let clauses = instantiate_pred_clauses(tcx, target_id, node_substs);
    get_impl_paths_for_clauses(tcx, verus_items, param_env_src, clauses, remove_self_trait_bound)
}

pub(crate) fn get_impl_paths_for_clauses<'tcx>(
    tcx: TyCtxt<'tcx>,
    verus_items: &crate::verus_items::VerusItems,
    param_env_src: DefId,
    clauses: Vec<(Option<ClauseFrom<'tcx>>, Clause<'tcx>)>,
    mut remove_self_trait_bound: Option<(DefId, &mut Option<vir::ast::ImplPath>)>,
) -> vir::ast::ImplPaths {
    let mut impl_paths = Vec::new();
    let typing_env = TypingEnv::non_body_analysis(tcx, param_env_src);

    // REVIEW: do we need this?
    // let normalized_substs = tcx.normalize_erasing_regions(param_env, node_substs);

    // We traverse all trait bounds that need to be instantiated, and the trait bounds
    // needed to satisfy those trait bounds, and so on. We traverse breadth-first.
    // Our goal is to just to collect all the impl paths, but a generic trait impl
    // might get reached multiple times for different instantiations. We need to process
    // each of these instantiations independently, since each one might lead to different
    // impl instantiatons. Thus, the worklist is over predicates (i.e., specific trait bounds)
    // not impls.

    let mut predicate_worklist: Vec<(Option<ClauseFrom<'tcx>>, Clause<'tcx>)> = clauses;

    let mut idx = 0;
    while idx < predicate_worklist.len() {
        if idx == 100000 {
            panic!("get_impl_paths nesting depth exceeds 1000");
        }

        let (inst_bound, inst_pred) = &predicate_worklist[idx];
        idx += 1;

        if let ClauseKind::Trait(_) = inst_pred.kind().skip_binder() {
            let inst_pred_kind = inst_pred.kind().skip_binder();
            let inst_pred_kind = clean_all_escaping_bound_vars(tcx, inst_pred_kind, param_env_src);

            let trait_refs = if let ClauseKind::Trait(tp) = &inst_pred_kind {
                tp.trait_ref
            } else {
                unreachable!()
            };

            let candidate_query_input = typing_env.as_query_input(trait_refs);
            let candidate = tcx.codegen_select_candidate(candidate_query_input);
            let candidate = candidate.or_else(|_| {
                let trait_refs = tcx.normalize_erasing_regions(typing_env, trait_refs);
                let candidate_query_input = typing_env.as_query_input(trait_refs);
                tcx.codegen_select_candidate(candidate_query_input)
            });
            if let Ok(impl_source) = candidate {
                if let rustc_middle::traits::ImplSource::UserDefined(u) = impl_source {
                    let impl_path = def_id_to_vir_path(tcx, verus_items, u.impl_def_id, None);
                    let impl_path = ImplPath::TraitImplPath(impl_path);
                    match (&mut remove_self_trait_bound, inst_bound) {
                        (Some((expected_id, self_trait_impl_path)), Some(b))
                            if *expected_id == b.source_id && b.is_self_trait_bound =>
                        {
                            assert!(self_trait_impl_path.is_none());
                            **self_trait_impl_path = Some(impl_path);
                        }
                        _ => {
                            impl_paths.push(impl_path);
                        }
                    }

                    let clauses = instantiate_pred_clauses(tcx, u.impl_def_id, u.args);
                    for p in clauses {
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

                    match inst_pred_kind {
                        ClauseKind::Trait(TraitPredicate {
                            trait_ref:
                                rustc_middle::ty::TraitRef {
                                    def_id: trait_def_id,
                                    args: trait_args,
                                    ..
                                },
                            polarity: rustc_middle::ty::PredicatePolarity::Positive,
                        }) => {
                            if Some(trait_def_id) == tcx.lang_items().fn_trait()
                                || Some(trait_def_id) == tcx.lang_items().fn_mut_trait()
                                || Some(trait_def_id) == tcx.lang_items().fn_once_trait()
                            {
                                match trait_args.into_type_list(tcx)[0].kind() {
                                    TyKind::FnDef(fn_def_id, fn_node_substs) => {
                                        let fn_path =
                                            def_id_to_vir_path(tcx, verus_items, *fn_def_id, None);
                                        let fn_fun = Arc::new(vir::ast::FunX { path: fn_path });
                                        impl_paths.push(ImplPath::FnDefImplPath(fn_fun));

                                        let clauses = instantiate_pred_clauses(
                                            tcx,
                                            *fn_def_id,
                                            fn_node_substs,
                                        );
                                        for p in clauses {
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
        Visibility::Restricted(id) => Some(ctxt.def_id_to_vir_path(id)),
    };
    vir::ast::Visibility { restricted_to }
}

pub(crate) fn get_range(typ: &Typ) -> IntRange {
    match &*undecorate_typ(typ) {
        TypX::Int(range) => *range,
        _ => panic!("get_range {:?}", typ),
    }
}

pub(crate) fn bitwidth_and_signedness_of_integer_type<'tcx>(
    verus_items: &crate::verus_items::VerusItems,
    ty: rustc_middle::ty::Ty<'tcx>,
) -> (Option<IntegerTypeBitwidth>, bool) {
    match mk_range(verus_items, &ty) {
        IntRange::U(w) => (Some(IntegerTypeBitwidth::Width(w)), false),
        IntRange::I(w) => (Some(IntegerTypeBitwidth::Width(w)), true),
        IntRange::USize => (Some(IntegerTypeBitwidth::ArchWordSize), false),
        IntRange::ISize => (Some(IntegerTypeBitwidth::ArchWordSize), true),
        IntRange::Nat => (None, false),
        IntRange::Int => (None, true),
        IntRange::Char => panic!("bitwidth_and_signedness_of_integer_type did not expect char"),
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

pub(crate) fn is_integer_ty<'tcx>(
    verus_items: &crate::verus_items::VerusItems,
    ty: &rustc_middle::ty::Ty<'tcx>,
) -> bool {
    match ty.kind() {
        TyKind::Adt(AdtDef(adt_def_data), _) => {
            let did = adt_def_data.did;
            let verus_item = verus_items.id_to_name.get(&did);
            match verus_item {
                Some(VerusItem::BuiltinType(BuiltinTypeItem::Int)) => true,
                Some(VerusItem::BuiltinType(BuiltinTypeItem::Nat)) => true,
                _ => false,
            }
        }
        TyKind::Uint(_) => true,
        TyKind::Int(_) => true,
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
                if let Some(t) = args[0].as_type() {
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

// Return true if we support the type and therefore can use a trait impl that mentions it
// (This is meant to be a quick prefilter; if it incorrectly returns true, we may end up
// dropping the results of trait_impl_to_vir, which is ok.)
pub(crate) fn mid_ty_filter_for_external_impls<'tcx>(
    ctxt: &Context<'tcx>,
    ty: &rustc_middle::ty::Ty<'tcx>,
    external_info: &mut ExternalInfo,
) -> bool {
    match ty.kind() {
        TyKind::Bool => true,
        TyKind::Uint(_) | TyKind::Int(_) => true,
        TyKind::Char => true,
        TyKind::Float(_) => true,
        TyKind::Ref(_, _, rustc_ast::Mutability::Not) => true,
        TyKind::Param(_) => true,
        TyKind::Tuple(_) => true,
        TyKind::Slice(_) => true,
        TyKind::RawPtr(_, _) => true,
        TyKind::Array(..) => true,
        TyKind::Closure(..) => true,
        TyKind::FnDef(..) => true,
        TyKind::Str => true,

        // HACK for now:
        // See https://github.com/rust-lang/rust/issues/64715
        // See https://github.com/rust-lang/rust/blob/master/library/core/src/convert/mod.rs
        // The "impl<T> From<!> for T" causes a real conflict with "impl<T> From<T> for T",
        // so don't auto-import ! for now.
        TyKind::Never => false,

        TyKind::Alias(rustc_middle::ty::AliasTyKind::Opaque, _) => false,
        TyKind::Alias(rustc_middle::ty::AliasTyKind::Free, _) => false,
        TyKind::Foreign(..) => false,
        TyKind::Ref(_, _, rustc_ast::Mutability::Mut) => false,
        TyKind::FnPtr(..) => false,
        TyKind::Dynamic(..) => false,
        TyKind::Coroutine(..) => false,
        TyKind::CoroutineWitness(..) => false,
        TyKind::Bound(..) => false,
        TyKind::Placeholder(..) => false,
        TyKind::Infer(..) => false,
        TyKind::Error(..) => false,

        TyKind::Adt(rustc_middle::ty::AdtDef(adt_def_data), _) => {
            external_info.has_type_id(ctxt, adt_def_data.did)
        }
        TyKind::Alias(
            rustc_middle::ty::AliasTyKind::Projection | rustc_middle::ty::AliasTyKind::Inherent,
            t,
        ) => {
            let trait_def = ctxt.tcx.generics_of(t.def_id).parent;
            let t_args: Vec<_> = t.args.iter().filter(|x| x.as_region().is_none()).collect();
            t_args.iter().find(|x| x.as_type().is_none()).is_none()
                && trait_def.is_some()
                && t_args.len() >= 1
        }

        TyKind::CoroutineClosure(_, _) => false,
        TyKind::Pat(_, _) => false,
        TyKind::UnsafeBinder(_) => false,
    }
}

pub(crate) fn mid_arg_filter_for_external_impls<'tcx>(
    ctxt: &Context<'tcx>,
    type_walker: rustc_middle::ty::walk::TypeWalker<TyCtxt<'tcx>>,
    external_info: &mut ExternalInfo,
) -> bool {
    let mut all_types_supported = true;
    for arg in type_walker {
        if let Some(t) = arg.as_type() {
            let supported = mid_ty_filter_for_external_impls(ctxt, &t, external_info);
            all_types_supported = all_types_supported && supported;
        }
    }
    all_types_supported
}

// Return true if we support the generics and therefore can use a trait impl that mentions it
// (This is meant to be a quick prefilter; if it incorrectly returns true, we may end up
// dropping the results of trait_impl_to_vir, which is ok.)
pub(crate) fn mid_generics_filter_for_external_impls<'tcx>(
    ctxt: &Context<'tcx>,
    def_id: DefId,
    external_info: &mut ExternalInfo,
) -> bool {
    let tcx = ctxt.tcx;
    let generics = tcx.generics_of(def_id);
    for (i, param) in generics.own_params.iter().enumerate() {
        if i == 0 && param.name == kw::SelfUpper {
            continue;
        }
        match &param.kind {
            GenericParamDefKind::Lifetime { .. } => continue,
            GenericParamDefKind::Type { has_default: _, synthetic: _ } => {}
            GenericParamDefKind::Const { .. } => {}
        }
        if param.pure_wrt_drop {
            return false;
        }
    }
    let predicates = tcx.predicates_of(def_id);
    for (predicate, _span) in predicates.predicates.iter() {
        match predicate.kind().skip_binder() {
            ClauseKind::RegionOutlives(_) | ClauseKind::TypeOutlives(_) => {}
            ClauseKind::Trait(TraitPredicate {
                trait_ref,
                polarity: rustc_middle::ty::PredicatePolarity::Positive,
            }) => {
                let trait_def_id = trait_ref.def_id;
                if Some(trait_def_id) == tcx.lang_items().fn_trait()
                    || Some(trait_def_id) == tcx.lang_items().fn_mut_trait()
                    || Some(trait_def_id) == tcx.lang_items().fn_once_trait()
                {
                    continue;
                }
                if !external_info.trait_id_set.contains(&trait_def_id) {
                    return false;
                }
                for arg in trait_ref.args.types() {
                    if !mid_arg_filter_for_external_impls(ctxt, arg.walk(), external_info) {
                        return false;
                    }
                }
            }
            ClauseKind::Projection(pred) => {
                if Some(pred.projection_term.def_id) == tcx.lang_items().fn_once_output() {
                    continue;
                }
                let Some(_ty) = pred.term.as_type() else {
                    return false;
                };
                let trait_def_id = pred.projection_term.trait_def_id(tcx);
                if !external_info.trait_id_set.contains(&trait_def_id) {
                    return false;
                }
                for arg in pred.projection_term.args.types() {
                    if !mid_arg_filter_for_external_impls(ctxt, arg.walk(), external_info) {
                        return false;
                    }
                }
            }
            ClauseKind::ConstArgHasType(..) => {}
            _ => {
                return false;
            }
        }
    }
    true
}

// returns VIR Typ and whether Ghost/Tracked was erased from around the outside of the VIR Typ
pub(crate) fn mid_ty_to_vir_ghost<'tcx>(
    tcx: TyCtxt<'tcx>,
    verus_items: &crate::verus_items::VerusItems,
    path_def_id_map: Option<std::cell::RefMut<HashMap<Path, DefId>>>,
    param_env_src: DefId,
    span: Span,
    ty: &rustc_middle::ty::Ty<'tcx>,
    allow_mut_ref: bool,
) -> Result<(Typ, bool), VirErr> {
    use rustc_middle::ty::GenericArgs;
    use vir::ast::TypDecoration;
    let t_rec = |t: &rustc_middle::ty::Ty<'tcx>| {
        mid_ty_to_vir_ghost(tcx, verus_items, None, param_env_src, span, t, allow_mut_ref)
    };
    let t_rec_flags = |t: &rustc_middle::ty::Ty<'tcx>, allow_mut_ref: bool| {
        mid_ty_to_vir_ghost(tcx, verus_items, None, param_env_src, span, t, allow_mut_ref)
    };
    let mk_typ_args = |args: &GenericArgs<'tcx>| -> Result<Vec<(Typ, bool)>, VirErr> {
        let mut typ_args: Vec<(Typ, bool)> = Vec::new();
        for arg in args.iter() {
            match arg.kind() {
                rustc_middle::ty::GenericArgKind::Type(t) => {
                    typ_args.push(t_rec(&t)?);
                }
                rustc_middle::ty::GenericArgKind::Lifetime(_) => {}
                rustc_middle::ty::GenericArgKind::Const(cnst) => {
                    typ_args.push((mid_ty_const_to_vir(tcx, Some(span), &cnst)?, false));
                }
            }
        }
        Ok(typ_args)
    };
    let t = match ty.kind() {
        TyKind::Bool => (Arc::new(TypX::Bool), false),
        TyKind::Uint(_) | TyKind::Int(_) => (Arc::new(TypX::Int(mk_range(verus_items, ty))), false),
        TyKind::Char => (Arc::new(TypX::Int(IntRange::Char)), false),
        TyKind::Float(f) => match f {
            rustc_middle::ty::FloatTy::F16 => (Arc::new(TypX::Float(16)), false),
            rustc_middle::ty::FloatTy::F32 => (Arc::new(TypX::Float(32)), false),
            rustc_middle::ty::FloatTy::F64 => (Arc::new(TypX::Float(64)), false),
            rustc_middle::ty::FloatTy::F128 => (Arc::new(TypX::Float(128)), false),
        },
        TyKind::Ref(_, tys, rustc_ast::Mutability::Not) => {
            let (t0, ghost) = t_rec(tys)?;
            (Arc::new(TypX::Decorate(TypDecoration::Ref, None, t0.clone())), ghost)
        }
        TyKind::Ref(_, tys, rustc_ast::Mutability::Mut) if new_mut_ref() => {
            let (t0, ghost) = t_rec(tys)?;
            (Arc::new(TypX::MutRef(t0.clone())), ghost)
        }
        TyKind::Ref(_, tys, rustc_ast::Mutability::Mut) if allow_mut_ref => {
            let (t0, ghost) = t_rec(tys)?;
            (Arc::new(TypX::Decorate(TypDecoration::MutRef, None, t0.clone())), ghost)
        }
        TyKind::Param(param) if param.name == kw::SelfUpper => {
            (Arc::new(TypX::TypParam(vir::def::trait_self_type_param())), false)
        }
        TyKind::Param(param) => {
            (Arc::new(TypX::TypParam(Arc::new(param_ty_to_vir_name(param)))), false)
        }
        TyKind::Never => {
            // All types are inhabited in SMT; we pick an arbitrary inhabited type for Never
            let tuple0 = vir::ast_util::unit_typ();
            (Arc::new(TypX::Decorate(TypDecoration::Never, None, tuple0)), false)
        }
        TyKind::Tuple(_) => {
            let mut typs: Vec<Typ> = Vec::new();
            for t in ty.tuple_fields().iter() {
                typs.push(t_rec(&t)?.0);
            }
            (vir::ast_util::mk_tuple_typ(&Arc::new(typs)), false)
        }
        TyKind::Slice(ty) => {
            let typ = t_rec(ty)?.0;
            let typs = Arc::new(vec![typ]);
            (Arc::new(TypX::Primitive(Primitive::Slice, typs)), false)
        }
        TyKind::Str => (Arc::new(TypX::Primitive(Primitive::StrSlice, Arc::new(vec![]))), false),
        TyKind::RawPtr(ty, mutbl) => {
            let typ = t_rec(ty)?.0;
            let typs = Arc::new(vec![typ]);

            let typ = Arc::new(TypX::Primitive(Primitive::Ptr, typs));
            let dec_typ = match mutbl {
                Mutability::Not => Arc::new(TypX::Decorate(TypDecoration::ConstPtr, None, typ)),
                Mutability::Mut => typ,
            };
            (dec_typ, false)
        }
        TyKind::Array(ty, const_len) => {
            let typ = mid_ty_to_vir_ghost(
                tcx,
                verus_items,
                None,
                param_env_src,
                span,
                ty,
                allow_mut_ref,
            )?
            .0;
            let len = mid_ty_const_to_vir(tcx, Some(span), const_len)?;
            let typs = Arc::new(vec![typ, len]);
            (Arc::new(TypX::Primitive(Primitive::Array, typs)), false)
        }
        TyKind::Adt(AdtDef(adt_def_data), args) => {
            let did = adt_def_data.did;
            let verus_item = verus_items.id_to_name.get(&did);
            if let Some(VerusItem::BuiltinType(BuiltinTypeItem::Int)) = verus_item {
                (Arc::new(TypX::Int(IntRange::Int)), false)
            } else if let Some(VerusItem::BuiltinType(BuiltinTypeItem::Nat)) = verus_item {
                (Arc::new(TypX::Int(IntRange::Nat)), false)
            } else if let Some(VerusItem::BuiltinType(BuiltinTypeItem::Real)) = verus_item {
                (Arc::new(TypX::Real), false)
            } else {
                let rust_item = verus_items::get_rust_item(tcx, did);

                if let Some(RustItem::AllocGlobal) = rust_item {
                    return Ok((
                        Arc::new(TypX::Primitive(Primitive::Global, Arc::new(vec![]))),
                        false,
                    ));
                }

                let typ_args = mk_typ_args(&args)?;
                if Some(did) == tcx.lang_items().owned_box() && typ_args.len() == 2 {
                    let (t0, ghost) = &typ_args[0];
                    let alloc_dec = Some(TypDecorationArg { allocator_typ: typ_args[1].0.clone() });
                    return Ok((
                        Arc::new(TypX::Decorate(TypDecoration::Box, alloc_dec, t0.clone())),
                        *ghost,
                    ));
                }
                if typ_args.len() >= 1 {
                    let (t0, ghost) = &typ_args[0];
                    let decorate = |d: TypDecoration, darg, ghost: bool| {
                        Ok((Arc::new(TypX::Decorate(d, darg, t0.clone())), ghost))
                    };
                    let verus_item = verus_items.id_to_name.get(&did);
                    match (verus_item, rust_item) {
                        (Some(VerusItem::BuiltinType(BuiltinTypeItem::Ghost)), _) => {
                            assert!(typ_args.len() == 1);
                            return decorate(TypDecoration::Ghost, None, true);
                        }
                        (Some(VerusItem::BuiltinType(BuiltinTypeItem::Tracked)), _) => {
                            assert!(typ_args.len() == 1);
                            return decorate(TypDecoration::Tracked, None, true);
                        }
                        (_, Some(RustItem::Rc)) => {
                            assert!(typ_args.len() == 2);
                            let alloc_dec =
                                Some(TypDecorationArg { allocator_typ: typ_args[1].0.clone() });
                            return decorate(TypDecoration::Rc, alloc_dec, *ghost);
                        }
                        (_, Some(RustItem::Arc)) => {
                            assert!(typ_args.len() == 2);
                            let alloc_dec =
                                Some(TypDecorationArg { allocator_typ: typ_args[1].0.clone() });
                            return decorate(TypDecoration::Arc, alloc_dec, *ghost);
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
                        TypX::Datatype(Dt::Tuple(_), typs, _) => typs.clone(),
                        _ => {
                            // TODO proper user-facing error msg here
                            panic!("expected first type argument of spec_fn to be a tuple");
                        }
                    };
                    return Ok((Arc::new(TypX::SpecFn(param_typs, ret_typ)), false));
                }
                let typ_args = typ_args.into_iter().map(|(t, _)| t).collect();
                let impl_paths = get_impl_paths(tcx, verus_items, param_env_src, did, args, None);
                let datatypex = def_id_to_datatype(
                    tcx,
                    verus_items,
                    path_def_id_map,
                    did,
                    Arc::new(typ_args),
                    impl_paths,
                );
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
                TypX::Datatype(Dt::Tuple(_), typs, _) => typs.clone(),
                _ => panic!("expected tuple type"),
            };

            let ret = t_rec(&sig.output().skip_binder())?.0;
            let id = def.as_local().unwrap().local_def_index.index();
            (Arc::new(TypX::AnonymousClosure(args, ret, id)), false)
        }
        TyKind::Alias(
            rustc_middle::ty::AliasTyKind::Projection | rustc_middle::ty::AliasTyKind::Inherent,
            t,
        ) => {
            // First, try to normalize to a non-projection type.
            // This can enable concrete operations on the type (e.g.
            // arithmetic if the normalized type is int) that
            // wouldn't be allowed if the type were left in an unnormalized form.
            use crate::rustc_trait_selection::traits::NormalizeExt;
            let param_env = tcx.param_env(param_env_src);
            let infcx =
                tcx.infer_ctxt().ignoring_regions().build(rustc_type_ir::TypingMode::Analysis {
                    defining_opaque_types_and_generators: Default::default(),
                });
            let cause = rustc_infer::traits::ObligationCause::dummy();
            let at = infcx.at(&cause, param_env);
            let ty = &clean_all_escaping_bound_vars(tcx, *ty, param_env_src);
            let norm = at.normalize(*ty);
            if norm.value != *ty {
                for arg in norm.value.walk().into_iter() {
                    if let Some(t) = arg.as_type() {
                        assert!(!matches!(t.kind(), TyKind::Infer(..)));
                    }
                }
                return t_rec(&norm.value);
            }
            // If normalization isn't possible, return a projection type:
            let assoc_item = tcx.associated_item(t.def_id);
            let name = Arc::new(assoc_item.name().to_string());
            // Note: this looks like it would work, but trait_item_def_id is sometimes None:
            //   use crate::rustc_middle::ty::DefIdTree;
            //   let trait_def = tcx.parent(assoc_item.trait_item_def_id.expect("..."));
            let trait_def = tcx.generics_of(t.def_id).parent;
            let t_args: Vec<_> = t.args.iter().filter(|x| x.as_region().is_none()).collect();
            match trait_def {
                Some(trait_def) if t_args.len() >= 1 => {
                    let trait_path = def_id_to_vir_path(tcx, verus_items, trait_def, None);
                    // In rustc, see create_substs_for_ast_path and create_substs_for_generic_args
                    let mut trait_typ_args = Vec::new();

                    for arg in t_args.iter() {
                        match arg.kind() {
                            rustc_middle::ty::GenericArgKind::Type(t) => {
                                trait_typ_args.push(t_rec_flags(&t, false)?.0);
                            }
                            rustc_middle::ty::GenericArgKind::Lifetime(_) => {
                                panic!("already filtered out lifetimes");
                            }
                            rustc_middle::ty::GenericArgKind::Const(cnst) => {
                                trait_typ_args.push(mid_ty_const_to_vir(tcx, Some(span), &cnst)?);
                            }
                        }
                    }

                    if Some(trait_def) == tcx.lang_items().pointee_trait()
                        && name.as_str() == "Metadata"
                    {
                        assert!(trait_typ_args.len() == 1);
                        let proj = TypX::PointeeMetadata(trait_typ_args[0].clone());
                        return Ok((Arc::new(proj), false));
                    } else {
                        let trait_typ_args = Arc::new(trait_typ_args);
                        let proj = TypX::Projection { trait_typ_args, trait_path, name };
                        return Ok((Arc::new(proj), false));
                    }
                }
                _ => {
                    unsupported_err!(span, "projection type")
                }
            }
        }
        TyKind::Alias(rustc_middle::ty::AliasTyKind::Opaque, al_ty) => {
            let mut args = Vec::new();
            for arg in al_ty.args {
                match arg.kind() {
                    rustc_type_ir::GenericArgKind::Lifetime(_) => {}
                    rustc_type_ir::GenericArgKind::Type(ty) => {
                        args.push(mid_ty_to_vir(
                            tcx,
                            verus_items,
                            None,
                            param_env_src,
                            span,
                            &ty,
                            false,
                        )?);
                    }
                    rustc_type_ir::GenericArgKind::Const(cnst) => {
                        args.push(crate::rust_to_vir_base::mid_ty_const_to_vir(
                            tcx,
                            Some(span),
                            &cnst,
                        )?);
                    }
                }
            }
            (
                Arc::new(TypX::Opaque {
                    def_path: def_id_to_vir_path(tcx, verus_items, al_ty.def_id, None),
                    args: Arc::new(args),
                }),
                false,
            )
        }
        TyKind::Alias(rustc_middle::ty::AliasTyKind::Free, _) => {
            unsupported_err!(span, "opaque type")
        }
        TyKind::FnDef(def_id, args) => {
            let resolved = if tcx.trait_of_assoc(*def_id).is_none() {
                None
            } else {
                let typing_env = TypingEnv::post_analysis(tcx, param_env_src);
                let resolution_result = crate::resolve_traits::resolve_trait_item(
                    span, tcx, typing_env, *def_id, args,
                )?;
                match resolution_result {
                    ResolutionResult::Unresolved => None,
                    ResolutionResult::Resolved {
                        resolved_item: ResolvedItem::FromImpl(did, _args),
                        ..
                    } => {
                        let path = def_id_to_vir_path(tcx, verus_items, did, None);
                        let fun = Arc::new(vir::ast::FunX { path });
                        Some(fun)
                    }
                    ResolutionResult::Resolved {
                        resolved_item: ResolvedItem::FromTrait(..),
                        ..
                    } => None,
                    ResolutionResult::Builtin(b) => {
                        unsupported_err!(span, format!("built-in instance {:?}", b));
                    }
                }
            };

            let typ_args = mk_typ_args(&args)?;
            let typ_args = typ_args.into_iter().map(|(t, _)| t).collect();
            let path = def_id_to_vir_path(tcx, verus_items, *def_id, None);
            let fun = Arc::new(vir::ast::FunX { path });

            let typx = TypX::FnDef(fun, Arc::new(typ_args), resolved);
            (Arc::new(typx), false)
        }
        TyKind::Dynamic(preds, _) => {
            use rustc_middle::ty::ExistentialPredicate;
            if preds.len() != 1 {
                unsupported_err!(span, "dyn with more that one trait");
            }
            match preds[0].skip_binder() {
                ExistentialPredicate::Trait(trait_ref) => {
                    let trait_did = trait_ref.def_id;
                    let args = trait_ref.args;
                    let trait_path = def_id_to_vir_path(tcx, verus_items, trait_did, None);
                    let self_arg = GenericArg::from(*ty);
                    let mut ty_args_with_self = vec![self_arg];
                    ty_args_with_self.extend(args.into_iter());
                    let args_with_self = tcx.mk_args(&ty_args_with_self);
                    let typ_args = mk_typ_args(&args)?;
                    let typ_args = typ_args.into_iter().map(|(t, _)| t).collect();
                    let impl_paths = get_impl_paths(
                        tcx,
                        verus_items,
                        param_env_src,
                        trait_did,
                        args_with_self,
                        None,
                    );
                    let typx = TypX::Dyn(trait_path, Arc::new(typ_args), impl_paths);
                    (Arc::new(typx), false)
                }
                ExistentialPredicate::Projection(_) => {
                    unsupported_err!(span, "dyn with projections");
                }
                ExistentialPredicate::AutoTrait(_def_id) => {
                    unsupported_err!(span, "dyn with auto-traits");
                }
            }
        }
        TyKind::Foreign(..) => unsupported_err!(span, "foreign types"),
        TyKind::Ref(_, _, rustc_ast::Mutability::Mut) => {
            unsupported_err!(span, "&mut types, except in special cases")
        }
        TyKind::FnPtr(..) => unsupported_err!(span, "function pointer types"),
        TyKind::Coroutine(..) => unsupported_err!(span, "generator types"),
        TyKind::CoroutineWitness(..) => unsupported_err!(span, "generator witness types"),
        TyKind::Bound(..) => unsupported_err!(span, "for<'a> types"),
        TyKind::Placeholder(..) => unsupported_err!(span, "type inference Placeholder types"),
        TyKind::Infer(..) => unsupported_err!(span, "type inference Infer types"),
        TyKind::Error(..) => unsupported_err!(span, "type inference error types"),
        TyKind::CoroutineClosure(_, _) => unsupported_err!(span, "coroutine closure types"),
        TyKind::Pat(_, _) => unsupported_err!(span, "pattern types"),
        TyKind::UnsafeBinder(_) => unsupported_err!(span, "unsafe binder types"),
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

pub(crate) fn mid_ty_to_vir<'tcx>(
    tcx: TyCtxt<'tcx>,
    verus_items: &crate::verus_items::VerusItems,
    path_def_id_map: Option<std::cell::RefMut<HashMap<Path, DefId>>>,
    param_env_src: DefId,
    span: Span,
    ty: &rustc_middle::ty::Ty<'tcx>,
    allow_mut_ref: bool,
) -> Result<Typ, VirErr> {
    Ok(mid_ty_to_vir_ghost(
        tcx,
        verus_items,
        path_def_id_map,
        param_env_src,
        span,
        ty,
        allow_mut_ref,
    )?
    .0)
}

pub(crate) fn mid_ty_const_to_vir<'tcx>(
    tcx: TyCtxt<'tcx>,
    span: Option<Span>,
    cnst: &rustc_middle::ty::Const<'tcx>,
) -> Result<Typ, VirErr> {
    let cnst = match cnst.kind() {
        ConstKind::Unevaluated(unevaluated) => {
            let typing_env = TypingEnv {
                param_env: tcx.param_env(unevaluated.def),
                typing_mode: TypingMode::PostAnalysis,
            };
            &tcx.normalize_erasing_regions(typing_env, cnst.clone())
        }
        _ => cnst,
    };

    match cnst.kind() {
        ConstKind::Param(param) => Ok(Arc::new(TypX::TypParam(Arc::new(param.name.to_string())))),
        ConstKind::Value(Value { ty, valtree }) => {
            let ValTreeKind::Leaf(i) = *valtree else {
                unsupported_err!(span.expect("span"), format!("const type argument {:?}", cnst));
            };
            match ty.kind() {
                TyKind::Uint(_) | TyKind::Int(_) => {
                    let c = num_bigint::BigInt::from(i.to_bits(i.size()));
                    Ok(Arc::new(TypX::ConstInt(c)))
                }
                TyKind::Bool => Ok(Arc::new(TypX::ConstBool(i.to_bits(i.size()) != 0))),
                _ => {
                    unsupported_err!(span.expect("span"), format!("const type argument {:?}", cnst))
                }
            }
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
        None,
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
        mid_ty_to_vir(bctx.ctxt.tcx, &bctx.ctxt.verus_items, None, bctx.fun_id, span, &ty, true)
    } else {
        err_span(span, "a mutable reference is expected here")
    }
}

pub(crate) fn implements_structural<'tcx>(
    bctx: &BodyCtxt<'tcx>,
    ty: rustc_middle::ty::Ty<'tcx>,
) -> bool {
    let ctxt = &bctx.ctxt;
    let structural_def_id = ctxt
        .verus_items
        .name_to_id
        .get(&VerusItem::Marker(crate::verus_items::MarkerItem::Structural))
        .expect("structural trait is not defined");

    let infcx = ctxt.tcx.infer_ctxt().build(TypingMode::PostAnalysis);
    let ty = ctxt.tcx.erase_and_anonymize_regions(ty);
    if ty.has_escaping_bound_vars() {
        return false;
    }
    let ty_impls_structural = infcx
        .type_implements_trait(
            *structural_def_id,
            vec![ty].into_iter(),
            ctxt.tcx.param_env(bctx.fun_id),
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
        (TypX::Datatype(..), TypX::Datatype(..)) if types_equal(&t1, &t2) => {
            let ty = bctx.types.node_type(*id1);
            Ok(implements_structural(&bctx, ty))
        }
        (TypX::TypParam(_), TypX::TypParam(_)) if types_equal(&t1, &t2) => {
            let ty = bctx.types.node_type(*id1);
            Ok(implements_structural(&bctx, ty))
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
        (TypX::Real, TypX::Real) => Ok(true),
        _ => Ok(false),
    }
}

fn get_proof_fn_one_mode<'tcx>(
    ctxt: &Context<'tcx>,
    span: Span,
    ty: &rustc_middle::ty::Ty<'tcx>,
) -> Result<Mode, VirErr> {
    match &ty.kind() {
        TyKind::Tuple(_) if ty.tuple_fields().len() == 0 => {
            return Ok(Mode::Spec);
        }
        TyKind::Adt(AdtDef(adt_def_data), _args) => {
            let verus_item = ctxt.verus_items.id_to_name.get(&adt_def_data.did);
            match verus_item {
                Some(VerusItem::External(crate::verus_items::ExternalItem::Trk)) => {
                    return Ok(Mode::Proof);
                }
                _ => {}
            }
        }
        _ => {}
    }
    err_span(span, "could not read mode annotations from proof_fn type")
}

pub(crate) fn try_get_proof_fn_modes<'tcx>(
    ctxt: &Context<'tcx>,
    span: Span,
    fun_ty: &rustc_middle::ty::Ty<'tcx>,
) -> Result<Option<(Vec<Mode>, Mode)>, VirErr> {
    match &fun_ty.kind() {
        TyKind::Ref(_, t, _) => try_get_proof_fn_modes(ctxt, span, t),
        TyKind::Adt(AdtDef(adt_def_data), args) => {
            let verus_item = ctxt.verus_items.id_to_name.get(&adt_def_data.did);
            if verus_item == Some(&VerusItem::External(crate::verus_items::ExternalItem::FnProof)) {
                assert!(args.len() == 6);
                let arg_mode_tuple = &args[2];
                let ret_mode_typ = &args[3];
                let ret_mode = if let Some(ty) = ret_mode_typ.as_type() {
                    get_proof_fn_one_mode(ctxt, span, &ty)?
                } else {
                    panic!("unexpected FnProof argument")
                };
                let arg_modes = if let Some(ty) = arg_mode_tuple.as_type() {
                    if let TyKind::Tuple(_) = ty.kind() {
                        let mut modes: Vec<Mode> = Vec::new();
                        for t in ty.tuple_fields().iter() {
                            modes.push(get_proof_fn_one_mode(ctxt, span, &t)?);
                        }
                        modes
                    } else {
                        panic!("unexpected FnProof argument")
                    }
                } else {
                    panic!("unexpected FnProof argument")
                };
                return Ok(Some((arg_modes, ret_mode)));
            }
            Ok(None)
        }
        _ => Ok(None),
    }
}

pub(crate) fn check_generic_bound<'tcx>(
    tcx: TyCtxt<'tcx>,
    verus_items: &crate::verus_items::VerusItems,
    param_env_src: DefId,
    span: Span,
    trait_def_id: DefId,
    args: &[GenericArg<'tcx>],
) -> Result<Option<vir::ast::GenericBound>, VirErr> {
    if Some(trait_def_id) == tcx.lang_items().copy_trait()
        || Some(trait_def_id) == tcx.lang_items().unpin_trait()
        || Some(trait_def_id) == tcx.lang_items().sync_trait()
        || Some(trait_def_id) == tcx.lang_items().tuple_trait()
        || Some(trait_def_id) == tcx.get_diagnostic_item(rustc_span::sym::Send)
    {
        // Rust language marker traits are ignored in VIR
        // TODO: these should not be ignored in VIR
        Ok(None)
    } else {
        let mut vir_args = vec![];
        for arg in args.iter() {
            match arg.kind() {
                GenericArgKind::Lifetime(_) => {}
                GenericArgKind::Type(ty) => {
                    vir_args.push(mid_ty_to_vir(
                        tcx,
                        verus_items,
                        None,
                        param_env_src,
                        span,
                        &ty,
                        false,
                    )?);
                }
                GenericArgKind::Const(cnst) => {
                    vir_args.push(mid_ty_const_to_vir(tcx, Some(span), &cnst)?);
                }
            }
        }
        let trait_name = if Some(trait_def_id) == tcx.lang_items().sized_trait() {
            TraitId::Sizedness(Sizedness::Sized)
        } else if Some(trait_def_id) == tcx.lang_items().meta_sized_trait() {
            TraitId::Sizedness(Sizedness::MetaSized)
        } else if Some(trait_def_id) == tcx.lang_items().pointee_sized_trait() {
            TraitId::Sizedness(Sizedness::PointeeSized)
        } else {
            TraitId::Path(def_id_to_vir_path(tcx, verus_items, trait_def_id, None))
        };
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
    predicates: impl Iterator<Item = &'a (Clause<'tcx>, Span)>,
    _generics: &'tcx rustc_middle::ty::Generics,
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
            ClauseKind::Trait(TraitPredicate {
                trait_ref,
                polarity: rustc_middle::ty::PredicatePolarity::Positive,
            }) => {
                let substs = trait_ref.args;

                // For a bound like `T: SomeTrait<X, Y, Z>`, then:
                // T should be index 0,
                // X, Y, Z, should be the rest
                // The SomeTrait is given by the def_id

                // Note that
                // T, X, Y, Z are actually all handled symmetrically
                // in the formal theory of Rust's traits;
                // i.e., the `Self` of a trait is actually the same as any of the other
                // type parameters, it's just special in the notation for convenience.

                let trait_def_id = trait_ref.def_id;

                if Some(trait_def_id) == tcx.lang_items().fn_trait()
                    || Some(trait_def_id) == tcx.lang_items().fn_mut_trait()
                    || Some(trait_def_id) == tcx.lang_items().fn_once_trait()
                {
                    // Ignore Fn bounds
                    continue;
                }

                let generic_bound = check_generic_bound(
                    tcx,
                    verus_items,
                    param_env_src,
                    *span,
                    trait_def_id,
                    substs,
                )?;
                if let Some(bound) = generic_bound {
                    bounds.push(bound);
                }
            }
            ClauseKind::Projection(pred) => {
                let item_def_id = pred.projection_term.def_id;

                if Some(item_def_id) == tcx.lang_items().fn_once_output() {
                    // The trait bound `F: Fn(A) -> B`
                    // is really more like a trait bound `F: Fn<A, Output=B>`
                    // The trait bounds that use = are called projections.
                    // When Rust sees a trait bound like this, it actually creates *two*
                    // bounds, a Trait bound for `F: Fn<A>` and a Projection for `Output=B`.
                    //
                    // Do nothing
                    // (What Verus actually cares about is the verus_builtin 'FnWithSpecification'
                    // trait which Fn/FnMut/FnOnce all get automatically.)
                    continue;
                }
                let typ = if let Some(ty) = pred.term.as_type() {
                    mid_ty_to_vir(tcx, verus_items, None, param_env_src, *span, &ty, false)?
                } else {
                    return err_span(*span, "Verus does not yet support this type of bound");
                };
                let substs = pred.projection_term.args;
                let trait_def_id = pred.projection_term.trait_def_id(tcx);
                let assoc_item = tcx.associated_item(item_def_id);
                let name = Arc::new(assoc_item.name().to_string());
                let generic_bound = check_generic_bound(
                    tcx,
                    verus_items,
                    param_env_src,
                    *span,
                    trait_def_id,
                    substs,
                )?;
                if let Some(generic_bound) = generic_bound {
                    if let GenericBoundX::Trait(TraitId::Path(path), typs) = &*generic_bound {
                        let bound = GenericBoundX::TypEquality(
                            path.clone(),
                            typs.clone(),
                            name.clone(),
                            typ.clone(),
                        );
                        bounds.push(Arc::new(bound));
                    } else {
                        return err_span(*span, "Verus does not yet support this type of bound");
                    }
                } else {
                    panic!("internal error: generic_bound should return GenericBoundX::Trait")
                }
            }
            ClauseKind::ConstArgHasType(cnst, ty) => {
                let t1 = mid_ty_const_to_vir(tcx, Some(*span), &cnst)?;
                let t2 = mid_ty_to_vir(tcx, verus_items, None, param_env_src, *span, &ty, false)?;
                let bound = GenericBoundX::ConstTyp(t1, t2);
                bounds.push(Arc::new(bound));
            }
            _ => {
                return err_span(*span, "Verus does not yet support this type of bound");
            }
        }
    }
    Ok(bounds)
}

// REVIEW: Consider using rustc_middle generics instead of hir generics
pub(crate) fn check_item_external_generics<'tcx>(
    tcx: TyCtxt<'tcx>,
    self_generics: Option<(&'tcx Generics, DefId)>,
    generics: &'tcx Generics<'tcx>,
    skip_implicit_lifetimes: bool,
    substs_ref: &rustc_middle::ty::GenericArgs<'tcx>,
    skip_self: bool,
    span: Span,
) -> Result<(), VirErr> {
    let mut generics_params: Vec<GenericParam> = vec![];
    if let Some((gen, _)) = self_generics {
        generics_params.extend(gen.params.iter().cloned());
    }
    generics_params.extend(generics.params.iter().cloned());

    if skip_implicit_lifetimes {
        generics_params = generics_params
            .into_iter()
            .filter(|gp| {
                !matches!(
                    gp.kind,
                    GenericParamKind::Lifetime { kind: LifetimeParamKind::Elided(_) }
                )
            })
            .collect();
    }

    use rustc_middle::ty::ScalarInt;
    // Check that the generics match (important because we do the substitution to get
    // the types from the external definition)
    let n_skip = if skip_self { 1 } else { 0 };
    let mut substs_ref: Vec<_> = substs_ref.iter().skip(n_skip).collect();
    substs_ref.retain(|arg| match arg.kind() {
        GenericArgKind::Const(cnst) => {
            if let ConstKind::Value(Value { ty, valtree }) = cnst.kind() {
                if let ValTreeKind::Leaf(ScalarInt::TRUE) = *valtree {
                    match ty.kind() {
                        TyKind::Bool => false,
                        _ => true,
                    }
                } else {
                    true
                }
            } else {
                true
            }
        }
        _ => true,
    });
    let err = || {
        err_span(
            span,
            format!(
                "expected generics to match: \n expected {}\n found {}",
                generics_params
                    .iter()
                    .map(|x| x.name.ident().to_string())
                    .collect::<Vec<_>>()
                    .join(", "),
                substs_ref.iter().map(|x| x.to_string()).collect::<Vec<_>>().join(", "),
            ),
        )
    };

    if substs_ref.len() != generics_params.len() {
        return err();
    }
    for (generic_arg, generic_param) in substs_ref.iter().zip(generics_params.iter()) {
        // So if we have like
        //    struct ProxyName<X, 'a>(External<X, 'a>);
        // We need to check the <X, 'a> line up
        // The 'generic_param' (hir) is from ProxyName<X, 'a>
        // and the 'generic_arg' (middle) is from the External<X, 'a>
        let param_name = match generic_param.name {
            rustc_hir::ParamName::Plain(ident) => ident.as_str().to_string(),
            _ => {
                return err();
            }
        };

        match (generic_arg.kind(), &generic_param.kind) {
            (
                GenericArgKind::Lifetime(region),
                GenericParamKind::Lifetime { kind: LifetimeParamKind::Explicit },
            ) => {
                // I guess this check doesn't really matter since we ignore lifetimes anyway
                match region.get_name(tcx) {
                    Some(name) if name.as_str() == param_name => { /* okay */ }
                    _ => {
                        return err();
                    }
                }
            }
            (GenericArgKind::Type(ty), GenericParamKind::Type { default: _, synthetic: false }) => {
                match ty.kind() {
                    TyKind::Param(param) if param.name.as_str() == param_name => { /* okay */ }
                    _ => {
                        return err();
                    }
                }
            }
            (GenericArgKind::Const(c), GenericParamKind::Const { ty: _, default: _ }) => {
                match c.kind() {
                    ConstKind::Param(param) if param.name.as_str() == param_name => {
                        // okay
                        // Rust's type checking already checks us that c's type matches ty,
                        // so we don't have to check that here.
                    }
                    _ => {
                        return err();
                    }
                }
            }
            _ => {
                return err();
            }
        }
    }
    Ok(())
}

fn check_generics_bounds_main<'tcx>(
    tcx: TyCtxt<'tcx>,
    verus_items: &crate::verus_items::VerusItems,
    span: Span,
    hir_generics: Option<&'tcx Generics<'tcx>>,
    check_that_external_body_datatype_declares_positivity: bool,
    error_on_polarity: bool,
    def_id: DefId,
    vattrs: Option<&crate::attributes::VerifierAttrs>,
    mut diagnostics: Option<&mut Vec<vir::ast::VirErrAs>>,
) -> Result<(vir::ast::TypPositives, vir::ast::GenericBounds), VirErr> {
    use vir::ast::AcceptRecursiveType;
    let mut accept_recs: HashMap<String, AcceptRecursiveType> = HashMap::new();

    if let Some(hir_generics) = hir_generics {
        for hir_param in hir_generics.params.iter() {
            let GenericParam {
                hir_id: _,
                name: _,
                span,
                pure_wrt_drop: _,
                kind: _,
                def_id: _,
                colon_span: _,
                source: _,
            } = hir_param;

            let vattrs = get_verifier_attrs(
                tcx.hir_attrs(hir_param.hir_id),
                if let Some(diagnostics) = &mut diagnostics { Some(diagnostics) } else { None },
            )?;
            if vattrs.reject_recursive_types
                || vattrs.reject_recursive_types_in_ground_variants
                || vattrs.accept_recursive_types
            {
                let (attr_name, attr) = if vattrs.reject_recursive_types {
                    ("reject_recursive_types", AcceptRecursiveType::Reject)
                } else if vattrs.reject_recursive_types_in_ground_variants {
                    (
                        "reject_recursive_types_in_ground_variants",
                        AcceptRecursiveType::RejectInGround,
                    )
                } else {
                    ("accept_recursive_types", AcceptRecursiveType::Accept)
                };
                let ident = hir_param.name.ident();
                let name = ident.as_str();

                // TODO stop supporthing this entirely
                //return err_span(
                //    *span,
                //    format!("use the attribute style `#[{attr_name:}({name:})]` at the item level"),
                //);

                accept_recs.insert(name.to_string(), attr);

                if let Some(diagnostics) = &mut diagnostics {
                    diagnostics.push(VirErrAs::Warning(crate::util::err_span_bare(
                        *span,
                        format!(
                            "use the attribute style `#[{attr_name:}({name:})]` at the item level"
                        ),
                    )));
                }
            }
        }
    }

    let generics = tcx.generics_of(def_id);

    let mut mid_params: Vec<&rustc_middle::ty::GenericParamDef> = vec![];
    for param in generics.own_params.iter() {
        match &param.kind {
            GenericParamDefKind::Lifetime { .. } => {} // ignore
            GenericParamDefKind::Type { .. } | GenericParamDefKind::Const { .. } => {
                mid_params.push(param);
            }
        }
    }

    let mut typ_params: Vec<(vir::ast::Ident, vir::ast::AcceptRecursiveType)> = Vec::new();

    // Process all trait bounds.
    let predicates = tcx.predicates_of(def_id);
    let bounds =
        process_predicate_bounds(tcx, def_id, verus_items, predicates.predicates.iter(), generics)?;

    // In traits, the first type param is Self. This is handled specially,
    // so we skip it here.
    // (Skipping it also allows the HIR type params and middle type params to line up.)
    let first_param_is_self = mid_params.len() > 0 && mid_params[0].name == kw::SelfUpper;
    let skip_n = if first_param_is_self { 1 } else { 0 };

    if let Some(vattrs) = vattrs {
        for (x, acc) in &vattrs.accept_recursive_type_list {
            if accept_recs.contains_key(x) {
                return err_span(span, format!("duplicate parameter attribute {x}"));
            }
            accept_recs.insert(x.clone(), *acc);
        }
    }

    for mid_param in mid_params.iter().skip(skip_n) {
        unsupported_err_unless!(!mid_param.pure_wrt_drop, span, "may_dangle attribute");

        match mid_param.kind {
            GenericParamDefKind::Type { .. } | GenericParamDefKind::Const { .. } => {}
            _ => {
                continue;
            }
        }

        let mut neg = false;
        let mut pos_some = false;
        let mut pos_all = false;
        let param_name = generic_param_def_to_vir_name(mid_param);
        match accept_recs.get(&param_name) {
            None => {}
            Some(AcceptRecursiveType::Reject) => neg = true,
            Some(AcceptRecursiveType::RejectInGround) => pos_some = true,
            Some(AcceptRecursiveType::Accept) => pos_all = true,
        }
        if accept_recs.contains_key(&param_name) {
            if error_on_polarity {
                return err_span(
                    span,
                    "the accept_recursive_type/reject_recursive_type attributes are not expected for this kind of item",
                );
            }
            accept_recs.remove(&param_name);
        }
        let accept_rec = match (neg, pos_some, pos_all) {
            (true, false, false) => AcceptRecursiveType::Reject,
            // RejectInGround is the default
            (false, true, false) | (false, false, false) => AcceptRecursiveType::RejectInGround,
            (false, false, true) => AcceptRecursiveType::Accept,
            _ => {
                return err_span(
                    span,
                    "type parameter can only have one of reject_recursive_types, reject_recursive_types_in_ground_variants, accept_recursive_types",
                );
            }
        };

        if let GenericParamDefKind::Type { .. } = &mid_param.kind {
            if check_that_external_body_datatype_declares_positivity
                && !neg
                && !pos_some
                && !pos_all
            {
                return err_span(
                    span,
                    "in external_body datatype, each type parameter must be one of: #[verifier::reject_recursive_types], #[verifier::reject_recursive_types_in_ground_variants], #[verifier::accept_recursive_types] (reject_recursive_types is always safe to use)",
                );
            }
        }

        match &mid_param.kind {
            GenericParamDefKind::Const { .. }
            | GenericParamDefKind::Type { has_default: _, synthetic: _ } => {
                // trait/function bounds
                typ_params.push((Arc::new(param_name), accept_rec));
            }
            _ => {
                unsupported_err!(span, "this kind of generic param");
            }
        }
    }
    for x in accept_recs.keys() {
        return err_span(span, format!("unused parameter attribute {x}"));
    }
    Ok((Arc::new(typ_params), Arc::new(bounds)))
}

pub(crate) fn check_generics_bounds_no_polarity<'tcx>(
    tcx: TyCtxt<'tcx>,
    verus_items: &crate::verus_items::VerusItems,
    span: Span,
    hir_generics: Option<&'tcx Generics<'tcx>>,
    def_id: DefId,
    diagnostics: Option<&mut Vec<vir::ast::VirErrAs>>,
) -> Result<(Idents, vir::ast::GenericBounds), VirErr> {
    let (typ_params, typ_bounds) = check_generics_bounds_main(
        tcx,
        verus_items,
        span,
        hir_generics,
        false,
        true,
        def_id,
        None,
        diagnostics,
    )?;
    let typ_params = typ_params.iter().map(|(x, _)| x.clone()).collect();
    Ok((Arc::new(typ_params), typ_bounds))
}

pub(crate) fn check_generics_bounds_with_polarity<'tcx>(
    tcx: TyCtxt<'tcx>,
    verus_items: &crate::verus_items::VerusItems,
    span: Span,
    hir_generics: Option<&'tcx Generics<'tcx>>,
    check_that_external_body_datatype_declares_positivity: bool,
    def_id: DefId,
    vattrs: Option<&crate::attributes::VerifierAttrs>,
    diagnostics: Option<&mut Vec<vir::ast::VirErrAs>>,
) -> Result<(vir::ast::TypPositives, vir::ast::GenericBounds), VirErr> {
    check_generics_bounds_main(
        tcx,
        verus_items,
        span,
        hir_generics,
        check_that_external_body_datatype_declares_positivity,
        false,
        def_id,
        vattrs,
        diagnostics,
    )
}

/// Returns if auto-dereferencing is supported for the given type.
///
/// Currently, this checks if the type is a `Box`, `Rc`, or `Arc`. Also, a
/// reference of a `Box`, `Rc`, or `Arc` is supported since it should be the
/// argument to the `deref` call.
pub(crate) fn auto_deref_supported_for_ty<'tcx>(
    tcx: TyCtxt<'tcx>,
    ty: &rustc_middle::ty::Ty<'tcx>,
) -> bool {
    fn is_supported_adt<'tcx>(tcx: TyCtxt<'tcx>, adt_def: &rustc_middle::ty::AdtDefData) -> bool {
        let did = adt_def.did;
        matches!(
            verus_items::get_rust_item(tcx, did),
            Some(RustItem::Box | RustItem::Rc | RustItem::Arc)
        )
    }

    match ty.kind() {
        TyKind::Adt(AdtDef(adt_def), _args) => is_supported_adt(tcx, adt_def),
        TyKind::Ref(_, t, _) => {
            // Only one-level of recursion.
            match t.kind() {
                TyKind::Adt(AdtDef(adt_def), _args) => is_supported_adt(tcx, adt_def),
                _ => false,
            }
        }
        _ => false,
    }
}

pub(crate) fn ty_is_vec<'tcx>(tcx: TyCtxt<'tcx>, ty: rustc_middle::ty::Ty<'tcx>) -> bool {
    match ty.kind() {
        TyKind::Adt(adt, _) => {
            let rust_item = verus_items::get_rust_item(tcx, adt.did());
            matches!(rust_item, Some(verus_items::RustItem::Vec))
        }
        _ => false,
    }
}

pub(crate) fn ty_remove_references<'tcx>(
    ty: &'tcx rustc_middle::ty::Ty<'tcx>,
) -> &'tcx rustc_middle::ty::Ty<'tcx> {
    match ty.kind() {
        TyKind::Ref(_, t, Mutability::Not) => ty_remove_references(&t),
        _ => ty,
    }
}

/// Add the OpaqueDef to vir if the function returns an opaque type.
pub(crate) fn check_fn_opaque_ty<'tcx>(
    ctxt: &Context<'tcx>,
    vir: &mut vir::ast::KrateX,
    fn_def_id: &DefId,
) -> Result<Vec<Path>, VirErr> {
    let ty = ctxt.tcx.fn_sig(fn_def_id).skip_binder().output().skip_binder();
    opaque_def_to_vir(ctxt, vir, fn_def_id, &ty)
}

pub(crate) fn opaque_def_to_vir<'tcx>(
    ctxt: &Context<'tcx>,
    vir: &mut vir::ast::KrateX,
    fn_def_id: &DefId,
    ty: &rustc_middle::ty::Ty<'tcx>,
) -> Result<Vec<Path>, VirErr> {
    let mut defined_opaque_types = vec![];
    match ty.kind() {
        rustc_middle::ty::TyKind::Alias(rustc_middle::ty::AliasTyKind::Opaque, al_ty) => {
            let span = ctxt.tcx.def_span(al_ty.def_id);
            let opaque_type_path =
                def_id_to_vir_path(ctxt.tcx, &ctxt.verus_items, al_ty.def_id.into(), None);
            let mut trait_bounds = Vec::new();
            let mut args = Vec::new();
            for arg in al_ty.args {
                match arg.kind() {
                    rustc_type_ir::GenericArgKind::Lifetime(_) => {}
                    rustc_type_ir::GenericArgKind::Type(ty) => {
                        args.push(mid_ty_to_vir(
                            ctxt.tcx,
                            &ctxt.verus_items,
                            None,
                            al_ty.def_id.into(),
                            span,
                            &ty,
                            false,
                        )?);
                    }
                    rustc_type_ir::GenericArgKind::Const(cnst) => {
                        args.push(crate::rust_to_vir_base::mid_ty_const_to_vir(
                            ctxt.tcx,
                            Some(span),
                            &cnst,
                        )?);
                    }
                }
            }

            let instantiated_bounds =
                ctxt.tcx.item_bounds(al_ty.def_id).instantiate(ctxt.tcx, al_ty.args);
            for bound in instantiated_bounds {
                match bound.kind().skip_binder() {
                    ClauseKind::Trait(TraitPredicate {
                        trait_ref,
                        polarity: rustc_middle::ty::PredicatePolarity::Positive,
                    }) => {
                        let substs = trait_ref.args;
                        let trait_def_id = trait_ref.def_id;
                        let generic_bound = check_generic_bound(
                            ctxt.tcx,
                            &ctxt.verus_items,
                            al_ty.def_id,
                            span,
                            trait_def_id,
                            substs,
                        )?
                        .unwrap();
                        trait_bounds.push(generic_bound);
                    }
                    ClauseKind::Projection(pred) => {
                        let item_def_id = pred.projection_term.def_id;

                        if Some(item_def_id) == ctxt.tcx.lang_items().fn_once_output() {
                            continue;
                        }
                        let typ = if let TermKind::Ty(ty) = pred.term.kind() {
                            opaque_def_to_vir(ctxt, vir, fn_def_id, &ty)?;
                            mid_ty_to_vir(
                                ctxt.tcx,
                                &ctxt.verus_items,
                                None,
                                al_ty.def_id.into(),
                                span,
                                &ty,
                                false,
                            )?
                        } else {
                            return err_span(span, "Verus does not yet support this type of bound");
                        };
                        let substs = pred.projection_term.args;
                        let trait_def_id = pred.projection_term.trait_def_id(ctxt.tcx);
                        let assoc_item = ctxt.tcx.associated_item(item_def_id);
                        let name = Arc::new(assoc_item.name().to_string());
                        let generic_bound = check_generic_bound(
                            ctxt.tcx,
                            &ctxt.verus_items,
                            al_ty.def_id.into(),
                            span,
                            trait_def_id,
                            substs,
                        )?;
                        if let Some(generic_bound) = generic_bound {
                            if let GenericBoundX::Trait(TraitId::Path(path), typs) = &*generic_bound
                            {
                                let bound = GenericBoundX::TypEquality(
                                    path.clone(),
                                    typs.clone(),
                                    name.clone(),
                                    typ.clone(),
                                );
                                trait_bounds.push(Arc::new(bound));
                            } else {
                                return err_span(
                                    span,
                                    "Verus does not yet support this type of bound",
                                );
                            }
                        } else {
                            panic!(
                                "internal error: generic_bound should return GenericBoundX::Trait"
                            )
                        }
                    }
                    _ => {}
                }
            }
            let opaque_ty_vir = ctxt.spanned_new(
                span,
                OpaqueTypeX {
                    def_fun: Arc::new(vir::ast::FunX {
                        path: def_id_to_vir_path(ctxt.tcx, &ctxt.verus_items, *fn_def_id, None),
                    }),
                    name: opaque_type_path.clone(),
                    typ_params: Arc::new(args),
                    typ_bounds: Arc::new(trait_bounds),
                },
            );

            vir.opaque_types.push(opaque_ty_vir);
            defined_opaque_types.push(opaque_type_path.clone());
        }
        rustc_middle::ty::TyKind::Tuple(tys) => {
            for ty in tys.iter() {
                defined_opaque_types.extend(opaque_def_to_vir(ctxt, vir, fn_def_id, &ty)?);
            }
        }
        rustc_middle::ty::TyKind::Array(ty, _) => {
            defined_opaque_types.extend(opaque_def_to_vir(ctxt, vir, fn_def_id, &ty)?)
        }
        rustc_middle::ty::TyKind::Pat(ty, _) => {
            defined_opaque_types.extend(opaque_def_to_vir(ctxt, vir, fn_def_id, &ty)?)
        }
        rustc_middle::ty::TyKind::Slice(ty) => {
            defined_opaque_types.extend(opaque_def_to_vir(ctxt, vir, fn_def_id, &ty)?)
        }
        _ => {}
    }
    Ok(defined_opaque_types)
}
