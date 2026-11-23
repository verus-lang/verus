//! Redirects `proof_with!` calls to verified counterparts before type checking.
//!
//! `proof_with!` emits `proof_with_callee(f(args, extras), f(args))`. After name
//! resolution and before HIR lowering ([`rewrite_crate`]), only the first call is
//! redirected to the `_VERUS_VERIFIED_` counterpart of `f`. All checks run after type
//! checking (`crate::rust_to_vir_expr::check_proof_with_callee`, `crate::proof_with_check`).
//!
//! The counterpart is found from the resolved `DefId`
//! ([`ProofWithCtx::find_verified_counterpart`]):
//! - free function or inherent method: its `_VERUS_VERIFIED_` sibling;
//! - external function: the counterpart of its local `assume_specification`;
//! - trait method: the method of a companion trait, which has the trait as a supertrait.
//!
//! The callee is rewritten according to what name resolution knows:
//! - resolved path (`f(..)`, `Tr::m(..)`, `<S as Tr>::m(..)`): its resolution is
//!   replaced ([`ProofWithRewriter::redirect_path`]);
//! - receiver call (`x.m(..)`) or type-relative path (`T::m(..)`): the method is renamed
//!   to `_VERUS_VERIFIED_m`, and its companion traits are added to the traits in scope
//!   ([`ProofWithRewriter::rewrite_method`]).
//!
//! HIR does not exist yet, so local items are read from the AST, and `tcx` is used only
//! for `def_key`-based queries and the metadata of other crates.

use crate::attributes::{Attr, is_unverified_stub, is_verified_counterpart, parse_attrs_opt};
use rustc_ast::mut_visit::{self, MutVisitor};
use rustc_ast::visit::{self, AssocCtxt, Visitor};
use rustc_ast::{
    AssocItem, AssocItemKind, AttrKind, Attribute, Block, Expr, ExprKind, GenericBound, Item,
    ItemKind, LocalKind, NodeId, Path, PathSegment, StmtKind,
};
use rustc_data_structures::fx::{FxIndexMap, FxIndexSet};
use rustc_data_structures::sync::{MappedReadGuard, MappedWriteGuard};
use rustc_hir::TraitCandidate;
use rustc_hir::def::{DefKind, Res};
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_middle::middle::resolve::{PartialRes, ResolverAstLowering};
use rustc_middle::ty::{AssocTag, TyCtxt};
use rustc_span::symbol::{Ident, Symbol};
use std::collections::{HashMap, HashSet};
use std::sync::Arc;
use vir::ast::VirErr;

/// This prefix must match `builtin_macros::attr_rewrite::WITH`.
const VERIFIED_PREFIX: &str = "_VERUS_VERIFIED";

const PROOF_WITH_CALLEE: &str = "verus::verus_builtin::proof_with_callee";

#[inline]
fn with_name(name: Symbol) -> Symbol {
    Symbol::intern(&format!("{VERIFIED_PREFIX}_{name}"))
}

/// Rewrites the `proof_with!` calls of the crate and returns the index used to check
/// them after type checking. Must run before HIR lowering takes the AST and the
/// resolver; `imported` are the VIR crates of the dependencies.
pub(crate) fn rewrite_crate(
    tcx: TyCtxt<'_>,
    imported: &[vir::ast::Krate],
) -> Result<Arc<ProofWithCtx>, VirErr> {
    // Early lints see the AST as written before our rewrite.
    tcx.ensure_done().early_lint_checks(());
    // Instead of intercepting providers.queries.resolver_for_lowering_raw,
    // we mutate the AST in place before HIR lowering steals it.
    let (resolver, krate) = tcx.resolver_for_lowering();
    assert!(!krate.is_stolen());
    assert!(!resolver.is_stolen());
    let mut krate = krate.risky_hack_borrow_mut();
    let ctxt = build_ctxt(tcx, &krate, imported)?;
    let mut rewriter = ProofWithRewriter { tcx, ctxt: &ctxt, error: None };
    rewriter.visit_crate(&mut krate);
    match rewriter.error {
        Some(err) => Err(err),
        None => Ok(ctxt),
    }
}

/// The crate-wide index for `proof_with!` rewriting and conformance checks, built
/// from the AST of the current crate and the metadata of the others.
#[derive(Default)]
pub(crate) struct ProofWithCtx {
    /// `proof_with_callee`, which may be a local item when the builtins are a module.
    marker: Option<DefId>,
    verified_with: HashSet<LocalDefId>,
    unverified_stubs: HashSet<LocalDefId>,
    /// Local functions by parent and name.
    local_fns: HashMap<(LocalDefId, Symbol), LocalDefId>,
    /// External functions are indexed through their local `assume_specification`.
    external_targets: HashMap<DefId, DefId>,
    imported_external_targets: HashMap<vir::ast::Path, DefId>,
    /// The companion traits of each trait, which are generated with it as a supertrait.
    companions: FxIndexMap<DefId, Vec<DefId>>,
    /// The names of the counterparts of inherent `with` methods.
    inherent_counterparts: HashSet<Symbol>,
}

fn imported_external_proxies(
    crates: &[vir::ast::Krate],
) -> impl Iterator<Item = (&vir::ast::Path, &vir::ast::Path)> {
    crates.iter().flat_map(|krate| {
        // A proxy declared with `with ..` has its verified counterpart as a sibling.
        let names: HashSet<&vir::ast::Path> =
            krate.functions.iter().map(|function| &function.x.name.path).collect();
        krate.functions.iter().filter_map(move |function| {
            let proxy = function.x.proxy.as_ref()?;
            let last = proxy.x.last_segment();
            let name = last.name()?;
            let counterpart = proxy.x.replace_last(vir::ast::Segment::V(
                Arc::new(format!("{VERIFIED_PREFIX}_{name}")),
                0,
            ));
            names.contains(&counterpart).then_some((&function.x.name.path, &proxy.x))
        })
    })
}

/// Whether `attrs` contain `#[verus::internal(name)]`, or `#[verifier::name]` if
/// `verifier` is set. Verus' attribute parser only reads HIR attributes.
fn has_ast_attr(attrs: &[Attribute], name: &str, verifier: bool) -> bool {
    attrs.iter().any(|attr| {
        let AttrKind::Normal(normal) = &attr.kind else {
            return false;
        };
        let path: Vec<&str> =
            normal.item.path.segments.iter().map(|s| s.ident.name.as_str()).collect();
        match path[..] {
            ["verifier", n] => verifier && n == name,
            ["verus", "internal"] => attr.meta_item_list().is_some_and(|list| {
                matches!(&list[..], [item] if item.is_word()
                    && item.ident().is_some_and(|i| i.name.as_str() == name))
            }),
            _ => false,
        }
    })
}

fn is_proof_block(expr: &Expr) -> bool {
    matches!(expr.kind, ExprKind::Block(..)) && has_ast_attr(&expr.attrs, "proof_block", true)
}

fn is_diagnostic_item(attrs: &[Attribute], name: &str) -> bool {
    attrs.iter().any(|attr| {
        attr.has_name(rustc_span::sym::rustc_diagnostic_item)
            && attr.value_str().is_some_and(|v| v.as_str() == name)
    })
}

fn unparen(mut expr: &Expr) -> &Expr {
    while let ExprKind::Paren(inner) = &expr.kind {
        expr = inner;
    }
    expr
}

/// The trailing expression of a block, if any.
fn block_tail(block: &Block) -> Option<&Expr> {
    match &block.stmts.last()?.kind {
        StmtKind::Expr(e) => Some(e),
        _ => None,
    }
}

/// Borrows the resolver for reading. Drop the guard before calling `resolver_mut`.
fn resolver<'tcx>(tcx: TyCtxt<'tcx>) -> MappedReadGuard<'tcx, ResolverAstLowering<'tcx>> {
    tcx.resolver_for_lowering().0.borrow()
}

/// Borrows the resolver for writing. Drop the guard before borrowing it again.
fn resolver_mut<'tcx>(tcx: TyCtxt<'tcx>) -> MappedWriteGuard<'tcx, ResolverAstLowering<'tcx>> {
    let resolver = tcx.resolver_for_lowering().0;
    resolver.risky_hack_borrow_mut()
}

fn full_res(tcx: TyCtxt<'_>, id: NodeId) -> Option<Res<NodeId>> {
    resolver(tcx).partial_res_map.get(&id)?.full_res()
}

fn build_ctxt<'tcx>(
    tcx: TyCtxt<'tcx>,
    krate: &rustc_ast::Crate,
    imported: &[vir::ast::Krate],
) -> Result<Arc<ProofWithCtx>, VirErr> {
    let mut builder = ProofWithCtxBuilder { tcx, ctxt: ProofWithCtx::default(), stubs: Vec::new() };
    builder.visit_crate(krate);
    let ProofWithCtxBuilder { mut ctxt, stubs, .. } = builder;
    if ctxt.marker.is_none() {
        let name = Symbol::intern(PROOF_WITH_CALLEE);
        ctxt.marker = tcx
            .crates(())
            .iter()
            .find_map(|cnum| tcx.diagnostic_items(*cnum).name_to_id.get(&name))
            .copied();
    }
    external_companion_traits(tcx, &mut ctxt);
    for (stub, target) in stubs {
        if let Some(verified) = ctxt.counterpart_of(tcx, stub.to_def_id()) {
            ctxt.external_targets.insert(target, verified);
        }
    }
    ctxt.imported_external_targets = imported_external_target_map(tcx, &ctxt, imported)?;
    Ok(Arc::new(ctxt))
}

/// Collects the local items that `proof_with!` rewriting needs into a [`ProofWithCtx`].
struct ProofWithCtxBuilder<'tcx> {
    tcx: TyCtxt<'tcx>,
    ctxt: ProofWithCtx,
    /// `assume_specification` stubs and the external functions they specify.
    stubs: Vec<(LocalDefId, DefId)>,
}

impl ProofWithCtxBuilder<'_> {
    fn def_id(&self, id: NodeId) -> Option<LocalDefId> {
        Some(resolver(self.tcx).owners.get(&id)?.def_id)
    }

    fn index_item(&mut self, id: NodeId, attrs: &[Attribute], ident: Option<Ident>) {
        let Some(def_id) = self.def_id(id) else {
            return;
        };
        if has_ast_attr(attrs, "verified_with", false) {
            self.ctxt.verified_with.insert(def_id);
        }
        if has_ast_attr(attrs, "unverified_stub", false) {
            self.ctxt.unverified_stubs.insert(def_id);
        }
        if let Some(ident) = ident
            && let Some(parent) = self.tcx.opt_local_parent(def_id)
        {
            self.ctxt.local_fns.insert((parent, ident.name), def_id);
        }
    }

    /// An external function belongs to a crate that cannot carry a Verus attribute
    /// naming its counterpart. The link therefore lives on the local
    /// `assume_specification`, whose trailing body call names the external target.
    ///
    /// Unlike `get_external_def_id`, which runs after type checking, this supports only
    /// a plain path callee.
    fn index_external_fn_spec(&mut self, item: &Item, body: Option<&Block>) {
        if !has_ast_attr(&item.attrs, "external_fn_specification", true)
            || !has_ast_attr(&item.attrs, "unverified_stub", false)
        {
            return;
        }
        let (Some(def_id), Some(body)) = (self.def_id(item.id), body) else {
            return;
        };
        let mut expr = block_tail(body);
        while let Some(e) = expr.map(unparen) {
            match &e.kind {
                ExprKind::Block(block, _) => expr = block_tail(block),
                ExprKind::Call(callee, _) => {
                    let callee = unparen(callee);
                    if let ExprKind::Path(..) = callee.kind
                        && let Some(target) =
                            full_res(self.tcx, callee.id).and_then(|res| res.opt_def_id())
                    {
                        self.stubs.push((def_id, target));
                    }
                    return;
                }
                _ => return,
            }
        }
    }
}

impl<'ast> Visitor<'ast> for ProofWithCtxBuilder<'_> {
    fn visit_item(&mut self, item: &'ast Item) {
        match &item.kind {
            ItemKind::Fn(f) => {
                self.index_item(item.id, &item.attrs, Some(f.ident));
                self.index_external_fn_spec(item, f.body.as_deref());
                if is_diagnostic_item(&item.attrs, PROOF_WITH_CALLEE) {
                    self.ctxt.marker = self.def_id(item.id).map(LocalDefId::to_def_id);
                }
            }
            ItemKind::Trait(tr) => {
                if let Some(def_id) = self.def_id(item.id)
                    && has_ast_attr(&item.attrs, "verified_trait", false)
                {
                    let supertraits = tr.bounds.iter().filter_map(|bound| match bound {
                        GenericBound::Trait(poly) => {
                            full_res(self.tcx, poly.trait_ref.ref_id)?.opt_def_id()
                        }
                        _ => None,
                    });
                    self.ctxt.add_companion(def_id.to_def_id(), supertraits);
                }
            }
            ItemKind::Impl(impl_) if impl_.of_trait.is_none() => {
                for assoc in &impl_.items {
                    if let AssocItemKind::Fn(f) = &assoc.kind
                        && has_ast_attr(&assoc.attrs, "verified_with", false)
                    {
                        self.ctxt.inherent_counterparts.insert(f.ident.name);
                    }
                }
            }
            _ => {}
        }
        visit::walk_item(self, item);
    }

    fn visit_assoc_item(&mut self, item: &'ast AssocItem, ctxt: AssocCtxt) {
        if let AssocItemKind::Fn(f) = &item.kind {
            self.index_item(item.id, &item.attrs, Some(f.ident));
        }
        visit::walk_assoc_item(self, item, ctxt);
    }
}

fn is_companion_trait(attrs: &[rustc_hir::Attribute]) -> bool {
    parse_attrs_opt(attrs, None).into_iter().any(|a| matches!(a, Attr::VerifiedTrait))
}

fn external_companion_traits(tcx: TyCtxt<'_>, ctxt: &mut ProofWithCtx) {
    for cnum in tcx.crates(()) {
        for trait_def_id in tcx.traits(*cnum) {
            // The reserved prefix avoids decoding attributes for almost every trait.
            if !tcx.item_name(*trait_def_id).as_str().starts_with(VERIFIED_PREFIX) {
                continue;
            }
            // Verus attributes are `Unparsed`, for which the deprecation note permits
            // `get_all_attrs`.
            #[allow(deprecated)]
            let attrs = tcx.get_all_attrs(*trait_def_id);
            if !is_companion_trait(attrs) {
                continue;
            }
            let supertraits = tcx.explicit_super_clauses_of(*trait_def_id).skip_binder();
            let supertraits = supertraits
                .iter()
                .filter_map(|(clause, _)| Some(clause.as_trait_clause()?.def_id()));
            ctxt.add_companion(*trait_def_id, supertraits);
        }
    }
}

fn imported_external_target_map(
    tcx: TyCtxt<'_>,
    ctxt: &ProofWithCtx,
    crates: &[vir::ast::Krate],
) -> Result<HashMap<vir::ast::Path, DefId>, VirErr> {
    let mut map = HashMap::new();
    for (target, proxy_path) in imported_external_proxies(crates) {
        let counterpart = imported_proxy(tcx, proxy_path).and_then(|proxy| {
            if !ctxt.is_stub(tcx, proxy) {
                return None;
            }
            let counterpart = ctxt.counterpart_of(tcx, proxy)?;
            ctxt.is_verified_with(tcx, counterpart).then_some(counterpart)
        });
        let Some(counterpart) = counterpart else {
            return Err(vir::messages::error_bare(format!(
                "could not resolve the imported `proof_with!` counterpart for `{}`; \
                 make sure the specification crate is referenced by Rust \
                 (for example, `use spec_crate as _;`) and has been rebuilt",
                vir::ast_util::path_as_friendly_rust_name(target),
            )));
        };
        // Duplicate specifications are reported when VIR crates are merged.
        map.insert(target.clone(), counterpart);
    }
    Ok(map)
}

fn imported_proxy(tcx: TyCtxt<'_>, path: &vir::ast::Path) -> Option<DefId> {
    let krate = tcx
        .crates(())
        .iter()
        .find(|krate| crate::rust_to_vir_path::mk_crate_id(tcx, **krate) == path.krate)?;
    let mut module = krate.as_def_id();
    let (last, modules) = path.segments.split_last()?;
    let name = last.name()?.as_str();
    for segment in modules {
        module = tcx.module_children(module).iter().find_map(|child| match child.res {
            Res::Def(DefKind::Mod, id)
                if segment.name().is_some_and(|n| child.ident.name.as_str() == n.as_str()) =>
            {
                Some(id)
            }
            _ => None,
        })?;
    }
    tcx.module_children(module).iter().find_map(|child| match child.res {
        Res::Def(DefKind::Fn, id) if child.ident.name.as_str() == name => Some(id),
        _ => None,
    })
}

impl ProofWithCtx {
    /// Finds the candidate counterpart for an independently resolved executable call.
    /// The call is checked by `crate::rust_to_vir_expr::check_proof_with_callee`.
    pub(crate) fn find_verified_counterpart(
        &self,
        tcx: TyCtxt<'_>,
        original: DefId,
    ) -> Option<DefId> {
        // Trait calls may resolve to an implementation method, but counterpart lookup
        // uses the trait declaration's companion traits. Inherent methods keep their DefId.
        let original = if tcx.def_kind(original) == DefKind::AssocFn {
            tcx.associated_item(original).trait_item_def_id().unwrap_or(original)
        } else {
            original
        };
        self.lookup_counterpart(tcx, original)
    }

    /// Whether `def_id` is marked `#[verus::internal(verified_with)]`.
    fn is_verified_with(&self, tcx: TyCtxt<'_>, def_id: DefId) -> bool {
        match def_id.as_local() {
            Some(local) => self.verified_with.contains(&local),
            None => is_verified_counterpart(tcx.attrs_for_def(def_id)),
        }
    }

    /// Whether `def_id` is marked `#[verus::internal(unverified_stub)]`.
    fn is_stub(&self, tcx: TyCtxt<'_>, def_id: DefId) -> bool {
        match def_id.as_local() {
            Some(local) => self.unverified_stubs.contains(&local),
            None => is_unverified_stub(tcx.attrs_for_def(def_id)),
        }
    }

    /// Looks up a candidate using local stubs, specification maps, or companion traits.
    /// The candidate's `verified_with` marker and call conformance are checked separately.
    fn lookup_counterpart(&self, tcx: TyCtxt<'_>, def_id: DefId) -> Option<DefId> {
        let name = with_name(tcx.item_name(def_id));
        if !self.is_stub(tcx, def_id) {
            // Non-stubs may be linked through an `assume_specification` or an
            // external trait proxy.
            if let Some(found) = self.external_targets.get(&def_id) {
                return Some(*found);
            }
            if !def_id.is_local()
                && let Some(found) =
                    crate::rust_to_vir_path::def_path_to_vir_path(tcx, tcx.def_path(def_id))
                        .and_then(|path| self.imported_external_targets.get(&path))
            {
                return Some(*found);
            }
            let parent = tcx.opt_parent(def_id)?;
            return self.companion_method(tcx, parent, name);
        }
        self.counterpart_of(tcx, def_id)
            .or_else(|| self.companion_method(tcx, tcx.opt_parent(def_id)?, name))
    }

    fn counterpart_of(&self, tcx: TyCtxt<'_>, def_id: DefId) -> Option<DefId> {
        let parent = tcx.opt_parent(def_id)?;
        self.child_fn(tcx, parent, with_name(tcx.item_name(def_id)))
    }

    /// Finds a function by name among the items of a module, implementation or trait.
    fn child_fn(&self, tcx: TyCtxt<'_>, parent: DefId, name: Symbol) -> Option<DefId> {
        if let Some(parent) = parent.as_local() {
            // `module_children` and `associated_items` would lower the local HIR.
            return self.local_fns.get(&(parent, name)).map(|f| f.to_def_id());
        }
        match tcx.def_kind(parent) {
            DefKind::Mod => tcx
                .module_children(parent)
                .iter()
                .find(|child| child.ident.name == name)
                .and_then(|child| child.res.opt_def_id()),
            DefKind::Impl { .. } | DefKind::Trait => tcx
                .associated_items(parent)
                .filter_by_name_unhygienic_and_kind(name, AssocTag::Fn)
                .next()
                .map(|assoc| assoc.def_id),
            _ => None,
        }
    }

    /// Finds a trait method's counterpart by its generated name in a companion
    /// trait whose supertraits include `trait_def_id`, rather than an inherent impl.
    fn companion_method(
        &self,
        tcx: TyCtxt<'_>,
        trait_def_id: DefId,
        name: Symbol,
    ) -> Option<DefId> {
        self.companions_of_trait(trait_def_id)
            .iter()
            .find_map(|companion| self.child_fn(tcx, *companion, name))
    }

    /// The companion traits generated for `trait_def_id`.
    fn companions_of_trait(&self, trait_def_id: DefId) -> &[DefId] {
        self.companions.get(&trait_def_id).map(Vec::as_slice).unwrap_or_default()
    }

    fn add_companion(&mut self, companion: DefId, supertraits: impl Iterator<Item = DefId>) {
        for supertrait in supertraits {
            self.companions.entry(supertrait).or_default().push(companion);
        }
    }
}

/// The `proof_with_callee` argument holding the call to the verified counterpart, as
/// generated by `proof_with!`: the call, possibly wrapped by
/// `{ let (tmp, outputs) = call; proof!{..} tmp }` (for `=>`) and then `(_, follows)`
/// (for `|=`). `crate::rust_to_vir_expr::proof_with_verified_call` checks the exact
/// shape after type checking.
fn verified_call(expr: &mut Expr) -> Option<&mut Expr> {
    let mut expr = expr;
    if matches!(&expr.kind, ExprKind::Tup(es) if es.len() == 2) {
        let ExprKind::Tup(es) = &mut expr.kind else { unreachable!() };
        expr = &mut es[0];
    }
    let is_wrapped = |block: &Block| {
        let [first, proofs @ .., tail] = &block.stmts[..] else {
            return false;
        };
        matches!(&first.kind, StmtKind::Let(l) if matches!(l.kind, LocalKind::Init(_)))
            && matches!(&tail.kind, StmtKind::Expr(e) if matches!(e.kind, ExprKind::Path(None, _)))
            && proofs.iter().all(
                |s| matches!(&s.kind, StmtKind::Expr(b) | StmtKind::Semi(b) if is_proof_block(b)),
            )
    };
    if matches!(&expr.kind, ExprKind::Block(b, None) if is_wrapped(b)) {
        let ExprKind::Block(block, _) = &mut expr.kind else { unreachable!() };
        let StmtKind::Let(local) = &mut block.stmts[0].kind else { unreachable!() };
        let LocalKind::Init(init) = &mut local.kind else { unreachable!() };
        expr = init;
    }
    matches!(expr.kind, ExprKind::Call(..) | ExprKind::MethodCall(..)).then_some(expr)
}

struct ProofWithRewriter<'a, 'tcx> {
    tcx: TyCtxt<'tcx>,
    ctxt: &'a ProofWithCtx,
    error: Option<VirErr>,
}

impl MutVisitor for ProofWithRewriter<'_, '_> {
    fn visit_expr(&mut self, expr: &mut Expr) {
        if self.error.is_none()
            && let Err(err) = self.try_visit_expr(expr)
        {
            self.error = Some(err);
        }
    }
}

impl<'tcx> ProofWithRewriter<'_, 'tcx> {
    fn try_visit_expr(&mut self, expr: &mut Expr) -> Result<(), VirErr> {
        let is_proof_with = self.check_proof_with(expr)?;
        mut_visit::walk_expr(self, expr);
        if is_proof_with && self.error.is_none() {
            let ExprKind::Call(_, args) = &mut expr.kind else { unreachable!() };
            let call = verified_call(&mut args[0]).expect("checked by check_proof_with");
            self.redirect(call)?;
        }
        Ok(())
    }

    /// `proof_with!` generates `proof_with_callee(verified, compiled)`, where `verified`
    /// is the call `f(args, extra_args)`, possibly wrapped to bind the outputs, and
    /// `compiled` is `f(args)`. Returns whether `expr` is such a marker call, whose
    /// verified call is then redirected to the counterpart of the function the call
    /// resolves to.
    /// After type checking, `check_proof_with_callee` checks that `compiled` is the same
    /// call and resolves to the function whose counterpart is called.
    fn check_proof_with(&self, expr: &mut Expr) -> Result<bool, VirErr> {
        let ExprKind::Call(marker, args) = &mut expr.kind else {
            return Ok(false);
        };
        let marker = unparen(marker);
        let is_marker = self.ctxt.marker.is_some()
            && matches!(marker.kind, ExprKind::Path(None, _))
            && full_res(self.tcx, marker.id).and_then(|res| res.opt_def_id()) == self.ctxt.marker;
        if !is_marker {
            return Ok(false);
        }
        if args.len() != 2 || verified_call(&mut args[0]).is_none() {
            return crate::util::err_span(expr.span, "ill-formed `proof_with!` call");
        }
        Ok(true)
    }

    /// Redirects the verified call of a `proof_with_callee` marker.
    fn redirect(&mut self, call: &mut Expr) -> Result<(), VirErr> {
        let call_id = call.id;
        match &mut call.kind {
            // Ordinary function paths are already resolved; type-relative qualified
            // paths may still need type checking.
            ExprKind::Call(callee, _) => self.rewrite_callee(callee)?,
            // Receiver methods remain unresolved until type checking.
            ExprKind::MethodCall(method) => self.rewrite_method(call_id, &mut method.seg, false),
            _ => unreachable!("checked by verified_call"),
        }
        Ok(())
    }

    /// Rewrites the callee of the verified call.
    fn rewrite_callee(&mut self, callee: &mut Expr) -> Result<(), VirErr> {
        let callee_id = callee.id;
        let span = callee.span;
        let ExprKind::Path(qself, path) = &mut callee.kind else {
            return crate::util::err_span(span, "`with` ghost inputs/outputs: unsupported callee");
        };

        // Get the partial resolution for the callee.
        let cannot_redirect =
            || crate::util::err_span_bare(span, "`proof_with!` cannot redirect this call");
        let partial = resolver(self.tcx)
            .partial_res_map
            .get(&callee_id)
            .copied()
            .ok_or_else(cannot_redirect)?;
        match partial.full_res() {
            Some(Res::Def(_, def_id)) => {
                let Some(verified) = self.ctxt.lookup_counterpart(self.tcx, def_id) else {
                    let name = path.segments.last().map(|s| s.ident.to_string());
                    let name = name.unwrap_or_else(|| "function".to_owned());
                    // The local `def_span` query lowers HIR.
                    let def_span = match def_id.as_local() {
                        Some(local) => self.tcx.source_span(local),
                        None => self.tcx.def_span(def_id),
                    };
                    return Err(crate::util::err_span_bare(
                        span,
                        format!(
                            "`{name}` does not accept extra ghost/tracked arguments: \
                             it is not declared with `#[verus_spec(with ..)]`"
                        ),
                    )
                    .primary_span(&crate::spans::err_air_span(def_span)));
                };
                self.redirect_path(callee_id, qself, path, def_id, verified);
            }
            // The qualifying type resolves later (e.g. `T::m` or `T::Assoc::m`), so
            // every companion declaring the renamed method is offered.
            None => {
                let seg = path.segments.last_mut().expect("path segment");
                self.rewrite_method(callee_id, seg, true);
            }
            _ => return Err(cannot_redirect()),
        }
        Ok(())
    }

    /// A qualified trait call must also name the companion trait that declares the
    /// counterpart. An external specification may use a different item name.
    fn redirect_path(
        &mut self,
        renamed_id: NodeId,
        qself: &mut Option<Box<rustc_ast::QSelf>>,
        path: &mut Path,
        original: DefId,
        verified: DefId,
    ) {
        let tcx = self.tcx;
        let kind = tcx.def_kind(verified);
        let res = Res::Def(kind, verified);
        resolver_mut(tcx).partial_res_map.insert(renamed_id, PartialRes::new(res));
        if kind == DefKind::Fn && tcx.def_kind(original) != DefKind::Fn {
            // The counterpart of an external method's `assume_specification` is a free
            // function, which the method's type or trait cannot qualify. Its generic
            // arguments are inferred, and checked against the executable call's.
            *qself = None;
            let n = path.segments.len();
            path.segments.drain(..n - 1);
        }
        let declares = tcx.opt_parent(verified);
        if let Some(companion) = declares
            && declares != tcx.opt_parent(original)
            && matches!(tcx.def_kind(companion), DefKind::Trait)
        {
            if path.segments.len() == 1 {
                // `use Tr::m; m(..)` has no trait segment to rename, so add one.
                let mut seg = PathSegment::from_ident(path.segments[0].ident);
                seg.id = resolver(tcx).next_node_id;
                resolver_mut(tcx).next_node_id = NodeId::from_u32(seg.id.as_u32() + 1);
                path.segments.insert(0, seg);
            }

            let i = path.segments.len() - 2;
            self.rename(&mut path.segments[i], Res::Def(DefKind::Trait, companion));
        }
        let last = path.segments.last_mut().expect("path segment");
        self.rename(last, res);
    }

    /// Renames a method segment and records matching companion traits.
    /// `is_type_relative` is true for a type-relative path `T::m(..)` and false for a
    /// receiver call `x.m(..)`; `id` identifies the callee path or the call.
    fn rewrite_method(&mut self, id: NodeId, seg: &mut PathSegment, is_type_relative: bool) {
        let tcx = self.tcx;
        let verified_name = with_name(seg.ident.name);
        seg.ident = Ident::new(verified_name, seg.ident.span);

        // The resolver records candidates for every method call and type-relative path
        // in the trait map of the enclosing owner.
        let owner = (resolver(tcx).owners.items())
            .filter_map(|(owner, info)| Some((*owner, *info.trait_map.get(&id)?)))
            .get_only();
        let candidates: &'tcx [TraitCandidate<'tcx>] =
            owner.map(|(_, candidates)| candidates).unwrap_or_default();

        let ctxt = self.ctxt;
        let declares = |companion: &DefId| ctxt.child_fn(tcx, *companion, verified_name);
        // The trait of a type-relative path is unknown until type checking.
        let companions: FxIndexSet<&DefId> = if is_type_relative {
            Box::new(ctxt.companions.values().flatten()) as Box<dyn Iterator<Item = &DefId>>
        } else {
            Box::new(candidates.iter().flat_map(|c| ctxt.companions_of_trait(c.def_id)))
        }
        .filter(|c| declares(c).is_some())
        .collect();

        // Reusing the recorded imports prevents the source trait import from being
        // reported as unused.
        let import_ids: &'tcx [LocalDefId] =
            candidates.first().map(|c| c.import_ids).unwrap_or(&[]);
        // The companion traits are usually not imported; without them in scope, type
        // checking cannot resolve `_VERUS_VERIFIED_m` from the companion that declares it.
        // Method probing skips duplicate traits, so companions already in scope can be
        // appended again.
        let added = companions.iter().map(|companion| TraitCandidate {
            def_id: **companion,
            import_ids,
            lint_ambiguous: false,
        });
        let extended = tcx.hir_arena.alloc_from_iter(candidates.iter().cloned().chain(added));
        if let Some((owner, _)) = owner
            && let Some(info) = resolver_mut(tcx).owners.get_mut(&owner)
        {
            info.trait_map.insert(id, extended);
        }

        // Not exactly one companion
        if is_type_relative || companions.len() != 1 {
            return;
        }
        // If there is a inherent method and trait method with verified counterparts, we should not resolve it.
        // e.g., trait T {#[verus_spec(with ...) fn m();} impl S { #[verus_spec(with ...) fn m() { } } impl T for S { #[verus_spec(with ...) fn m() {}}
        if ctxt.inherent_counterparts.contains(&verified_name) {
            return;
        }
        // The verified method is resolved directly from the companion trait if there is exactly one companion.
        if let Some(method_defid) = companions.first().map(|c| *c).and_then(declares) {
            resolver_mut(tcx)
                .partial_res_map
                .insert(seg.id, PartialRes::new(Res::Def(DefKind::AssocFn, method_defid)));
        }
    }

    fn rename(&mut self, seg: &mut PathSegment, res: Res<NodeId>) {
        seg.ident = Ident::new(self.tcx.item_name(res.def_id()), seg.ident.span);
        resolver_mut(self.tcx).partial_res_map.insert(seg.id, PartialRes::new(res));
    }
}
