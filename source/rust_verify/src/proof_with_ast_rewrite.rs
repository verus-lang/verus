//! Redirects `proof_with!` calls to verified counterparts before type checking.
//!
//! `proof_with!` emits `proof_with_callee(f(args, extras), f(args))`. After name
//! resolution and before HIR lowering ([`rewrite_crate`]), only the first call is
//! redirected to the `_VERUS_VERIFIED_` counterpart of `f`. All checks run after type
//! checking (`crate::rust_to_vir_expr::check_proof_with_callee`).
//!
//! The counterpart is found from the resolved `DefId`
//! ([`ProofWithCtx::find_verified_counterpart`]):
//! - free function or inherent method: its `_VERUS_VERIFIED_` sibling;
//!
//! The callee is rewritten according to what name resolution knows:
//! - resolved path (`f(..)`, `Tr::m(..)`, `<S as Tr>::m(..)`): its resolution is
//!   replaced ([`ProofWithRewriter::redirect_path`]);
//! - type-relative path (`T::m(..)`): the method is renamed before probing;
//! - receiver call (`x.m(..)`): the macro retains the existing method rename.
//!
//! HIR does not exist yet, so local items are read from the AST, and `tcx` is used only
//! for `def_key`-based queries and the metadata of other crates.

use crate::attributes::is_unverified_stub;
use rustc_ast::mut_visit::{self, MutVisitor};
use rustc_ast::visit::{self, AssocCtxt, Visitor};
use rustc_ast::{
    AssocItem, AssocItemKind, AttrKind, Attribute, Block, Expr, ExprKind, Item, ItemKind,
    LocalKind, NodeId, Path, PathSegment, StmtKind,
};
use rustc_data_structures::sync::{MappedReadGuard, MappedWriteGuard};
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
/// resolver.
pub(crate) fn rewrite_crate(tcx: TyCtxt<'_>) -> Result<Arc<ProofWithCtx>, VirErr> {
    // Early lints see the AST as written before our rewrite.
    tcx.ensure_done().early_lint_checks(());
    // Instead of intercepting providers.queries.resolver_for_lowering_raw,
    // we mutate the AST in place before HIR lowering steals it.
    let (resolver, krate) = tcx.resolver_for_lowering();
    assert!(!krate.is_stolen());
    assert!(!resolver.is_stolen());
    let mut krate = krate.risky_hack_borrow_mut();
    let ctxt = build_ctxt(tcx, &krate);
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
    unverified_stubs: HashSet<LocalDefId>,
    /// Local functions by parent and name.
    local_fns: HashMap<(LocalDefId, Symbol), LocalDefId>,
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

fn build_ctxt<'tcx>(tcx: TyCtxt<'tcx>, krate: &rustc_ast::Crate) -> Arc<ProofWithCtx> {
    let mut builder = ProofWithCtxBuilder { tcx, ctxt: ProofWithCtx::default() };
    builder.visit_crate(krate);
    let ProofWithCtxBuilder { mut ctxt, .. } = builder;
    if ctxt.marker.is_none() {
        let name = Symbol::intern(PROOF_WITH_CALLEE);
        ctxt.marker = tcx
            .crates(())
            .iter()
            .find_map(|cnum| tcx.diagnostic_items(*cnum).name_to_id.get(&name))
            .copied();
    }
    Arc::new(ctxt)
}

/// Collects the local items that `proof_with!` rewriting needs into a [`ProofWithCtx`].
struct ProofWithCtxBuilder<'tcx> {
    tcx: TyCtxt<'tcx>,
    ctxt: ProofWithCtx,
}

impl ProofWithCtxBuilder<'_> {
    fn def_id(&self, id: NodeId) -> Option<LocalDefId> {
        Some(resolver(self.tcx).owners.get(&id)?.def_id)
    }

    fn index_item(&mut self, id: NodeId, attrs: &[Attribute], ident: Option<Ident>) {
        let Some(def_id) = self.def_id(id) else {
            return;
        };
        if has_ast_attr(attrs, "unverified_stub", false) {
            self.ctxt.unverified_stubs.insert(def_id);
        }
        if let Some(ident) = ident
            && let Some(parent) = self.tcx.opt_local_parent(def_id)
        {
            self.ctxt.local_fns.insert((parent, ident.name), def_id);
        }
    }
}

impl<'ast> Visitor<'ast> for ProofWithCtxBuilder<'_> {
    fn visit_item(&mut self, item: &'ast Item) {
        match &item.kind {
            ItemKind::Fn(f) => {
                self.index_item(item.id, &item.attrs, Some(f.ident));
                if is_diagnostic_item(&item.attrs, PROOF_WITH_CALLEE) {
                    self.ctxt.marker = self.def_id(item.id).map(LocalDefId::to_def_id);
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

impl ProofWithCtx {
    /// Finds the candidate counterpart for an independently resolved executable call.
    /// The call is checked by `crate::rust_to_vir_expr::check_proof_with_callee`.
    pub(crate) fn find_verified_counterpart(
        &self,
        tcx: TyCtxt<'_>,
        original: DefId,
    ) -> Option<DefId> {
        // Legacy trait counterparts are declared next to the trait method.
        let original = if tcx.def_kind(original) == DefKind::AssocFn {
            tcx.associated_item(original).trait_item_def_id().unwrap_or(original)
        } else {
            original
        };
        self.lookup_counterpart(tcx, original)
    }

    /// Whether `def_id` is marked `#[verus::internal(unverified_stub)]`.
    fn is_stub(&self, tcx: TyCtxt<'_>, def_id: DefId) -> bool {
        match def_id.as_local() {
            Some(local) => self.unverified_stubs.contains(&local),
            None => is_unverified_stub(tcx.attrs_for_def(def_id)),
        }
    }

    /// Looks up a candidate using the stub.
    /// The candidate's `verified_with` marker and call conformance are checked separately.
    fn lookup_counterpart(&self, tcx: TyCtxt<'_>, def_id: DefId) -> Option<DefId> {
        self.is_stub(tcx, def_id).then(|| self.counterpart_of(tcx, def_id)).flatten()
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
        match &mut call.kind {
            // Ordinary function paths are already resolved; type-relative qualified
            // paths may still need type checking.
            ExprKind::Call(callee, _) => self.rewrite_callee(callee)?,
            // The macro has already renamed a receiver method.
            ExprKind::MethodCall(_) => {}
            _ => unreachable!("checked by verified_call"),
        }
        Ok(())
    }

    /// Rewrites the callee of the verified call.
    fn rewrite_callee(&mut self, callee: &mut Expr) -> Result<(), VirErr> {
        let callee_id = callee.id;
        let span = callee.span;
        let ExprKind::Path(_, path) = &mut callee.kind else {
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
                self.redirect_path(callee_id, path, verified);
            }
            // The qualifying type (e.g. `T::Assoc`) resolves during type checking.
            None => {
                let seg = path.segments.last_mut().expect("path segment");
                self.rewrite_method(seg);
            }
            _ => return Err(cannot_redirect()),
        }
        Ok(())
    }

    fn redirect_path(&mut self, renamed_id: NodeId, path: &mut Path, verified: DefId) {
        let tcx = self.tcx;
        let kind = tcx.def_kind(verified);
        let res = Res::Def(kind, verified);
        resolver_mut(tcx).partial_res_map.insert(renamed_id, PartialRes::new(res));
        let last = path.segments.last_mut().expect("path segment");
        self.rename(last, res);
    }

    fn rewrite_method(&self, seg: &mut PathSegment) {
        seg.ident = Ident::new(with_name(seg.ident.name), seg.ident.span);
    }

    fn rename(&mut self, seg: &mut PathSegment, res: Res<NodeId>) {
        seg.ident = Ident::new(self.tcx.item_name(res.def_id()), seg.ident.span);
        resolver_mut(self.tcx).partial_res_map.insert(seg.id, PartialRes::new(res));
    }
}
