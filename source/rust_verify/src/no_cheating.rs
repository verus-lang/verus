//! Structural checks for the `--no-cheating` trust policy.
//!
//! Code is untrusted by default. `#[verus::trusted]` permits assumptions and is inherited by
//! child items. `#[verus::untrusted]` overrides inherited trust and permanently prevents child
//! items from opting back into trust. `#[verus::trusted(spec)]` trusts a function's type-level
//! signature and Verus specification for reference closure while leaving its body untrusted.

use crate::attributes::{TrustAttribute, get_trust_attributes};
use crate::context::ContextX;
use crate::util::vir_err_span_str;
use crate::verus_items::{DirectiveItem, SpecItem, VerusItem};
use rustc_hir::def::Res;
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_hir::intravisit::{FnKind, Visitor};
use rustc_hir::{
    BodyId, Expr, ExprKind, FnDecl, ForeignItem, ForeignItemKind, HirId, ImplItem, ImplItemKind,
    Item, ItemKind, OwnerId, TraitItem, TraitItemKind,
};
use rustc_middle::hir::nested_filter;
use rustc_middle::ty::TyCtxt;
use rustc_span::Span;
use std::collections::HashMap;
use vir::ast::VirErr;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum EffectiveTrust {
    Untrusted,
    Trusted,
    TrustedSpec,
}

impl EffectiveTrust {
    pub(crate) fn permits_assumptions(self) -> bool {
        self == Self::Trusted
    }

    fn in_trusted_closure(self) -> bool {
        matches!(self, Self::Trusted | Self::TrustedSpec)
    }
}

#[derive(Clone, Copy)]
struct InheritedPolicy {
    trusted: bool,
    untrusted_locked: bool,
}

fn apply_trust_attribute(
    inherited: &mut InheritedPolicy,
    local: Option<TrustAttribute>,
    trusted_spec_allowed: bool,
) -> EffectiveTrust {
    let effective = match local {
        Some(TrustAttribute::Untrusted) => {
            inherited.untrusted_locked = true;
            EffectiveTrust::Untrusted
        }
        Some(TrustAttribute::TrustedSpec)
            if trusted_spec_allowed && !inherited.untrusted_locked =>
        {
            EffectiveTrust::TrustedSpec
        }
        Some(TrustAttribute::Trusted) if !inherited.untrusted_locked => EffectiveTrust::Trusted,
        Some(TrustAttribute::Trusted | TrustAttribute::TrustedSpec) => EffectiveTrust::Untrusted,
        None if inherited.untrusted_locked => EffectiveTrust::Untrusted,
        None if inherited.trusted => EffectiveTrust::Trusted,
        None => EffectiveTrust::Untrusted,
    };
    inherited.trusted = effective.permits_assumptions();
    effective
}

fn local_trust_attribute(
    attrs: &[rustc_hir::Attribute],
) -> Result<Option<(TrustAttribute, Span)>, VirErr> {
    let trust_attrs = get_trust_attributes(attrs)?;
    if trust_attrs.len() > 1 {
        return Err(vir_err_span_str(
            trust_attrs[1].1,
            "an item may have at most one of `#[verus::trusted]`, `#[verus::trusted(spec)]`, and `#[verus::untrusted]`",
        ));
    }
    Ok(trust_attrs.into_iter().next())
}

fn attrs_for_local_def_id<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: LocalDefId,
) -> &'tcx [rustc_hir::Attribute] {
    if def_id == rustc_hir::CRATE_OWNER_ID.def_id {
        tcx.hir_attrs(rustc_hir::CRATE_HIR_ID)
    } else {
        tcx.hir_attrs(tcx.local_def_id_to_hir_id(def_id))
    }
}

/// Compute the effective trust of an item. The validation pass reports malformed combinations;
/// this helper is also used while constructing VIR functions.
pub(crate) fn effective_trust<'tcx>(
    tcx: TyCtxt<'tcx>,
    def_id: DefId,
) -> Result<EffectiveTrust, VirErr> {
    let Some(mut local_def_id) = def_id.as_local() else {
        return Ok(EffectiveTrust::Untrusted);
    };
    let mut chain = Vec::new();
    loop {
        chain.push(local_def_id);
        if local_def_id == rustc_hir::CRATE_OWNER_ID.def_id {
            break;
        }
        let parent = tcx.parent(local_def_id.to_def_id());
        let Some(parent) = parent.as_local() else {
            break;
        };
        local_def_id = parent;
    }
    chain.reverse();

    let mut inherited = InheritedPolicy { trusted: false, untrusted_locked: false };
    let mut effective = EffectiveTrust::Untrusted;
    for local_def_id in chain {
        let local = local_trust_attribute(attrs_for_local_def_id(tcx, local_def_id))?;
        effective = apply_trust_attribute(&mut inherited, local.map(|(attr, _)| attr), true);
    }
    Ok(effective)
}

/// Validate trust attributes and check that trusted local code is closed under references.
pub(crate) fn check_trust<'tcx>(ctxt: &ContextX<'tcx>) -> Vec<VirErr> {
    let tcx = ctxt.tcx;
    let root_module = tcx.hir_root_module();
    let root_owner = tcx.hir_owner_node(rustc_hir::CRATE_OWNER_ID);
    let mut collector = PolicyCollector {
        tcx,
        inherited: InheritedPolicy { trusted: false, untrusted_locked: false },
        policies: HashMap::new(),
        errors: Vec::new(),
    };
    let saved = collector.enter(rustc_hir::CRATE_HIR_ID, rustc_hir::CRATE_OWNER_ID, false);
    collector.visit_mod(root_module, root_owner.span(), rustc_hir::CRATE_HIR_ID);
    collector.inherited = saved;

    let mut errors = collector.errors;
    let policies = collector.policies;
    let mut scanner = TrustedItemScanner { ctxt, policies: &policies, errors: Vec::new() };
    scanner.visit_mod(root_module, root_owner.span(), rustc_hir::CRATE_HIR_ID);
    errors.append(&mut scanner.errors);
    errors
}

struct PolicyCollector<'tcx> {
    tcx: TyCtxt<'tcx>,
    inherited: InheritedPolicy,
    policies: HashMap<LocalDefId, EffectiveTrust>,
    errors: Vec<VirErr>,
}

impl<'tcx> PolicyCollector<'tcx> {
    fn enter(
        &mut self,
        hir_id: HirId,
        owner_id: OwnerId,
        trusted_spec_allowed: bool,
    ) -> InheritedPolicy {
        let saved = self.inherited;
        let local = match local_trust_attribute(self.tcx.hir_attrs(hir_id)) {
            Ok(local) => local,
            Err(err) => {
                self.errors.push(err);
                None
            }
        };

        if let Some((TrustAttribute::TrustedSpec, span)) = local
            && !trusted_spec_allowed
        {
            self.errors.push(vir_err_span_str(
                span,
                "`#[verus::trusted(spec)]` may only be applied to a function",
            ));
        }
        if let Some((TrustAttribute::Trusted | TrustAttribute::TrustedSpec, span)) = local
            && self.inherited.untrusted_locked
        {
            self.errors.push(vir_err_span_str(
                span,
                "a child of an item marked `#[verus::untrusted]` cannot be marked trusted",
            ));
        }

        let effective = apply_trust_attribute(
            &mut self.inherited,
            local.map(|(attr, _)| attr),
            trusted_spec_allowed,
        );
        self.policies.insert(owner_id.def_id, effective);
        saved
    }
}

impl<'tcx> Visitor<'tcx> for PolicyCollector<'tcx> {
    type NestedFilter = nested_filter::All;

    fn maybe_tcx(&mut self) -> TyCtxt<'tcx> {
        self.tcx
    }

    fn visit_item(&mut self, item: &'tcx Item<'tcx>) {
        let saved =
            self.enter(item.hir_id(), item.owner_id, matches!(item.kind, ItemKind::Fn { .. }));
        rustc_hir::intravisit::walk_item(self, item);
        self.inherited = saved;
    }

    fn visit_impl_item(&mut self, item: &'tcx ImplItem<'tcx>) {
        let saved =
            self.enter(item.hir_id(), item.owner_id, matches!(item.kind, ImplItemKind::Fn(..)));
        rustc_hir::intravisit::walk_impl_item(self, item);
        self.inherited = saved;
    }

    fn visit_trait_item(&mut self, item: &'tcx TraitItem<'tcx>) {
        let saved =
            self.enter(item.hir_id(), item.owner_id, matches!(item.kind, TraitItemKind::Fn(..)));
        rustc_hir::intravisit::walk_trait_item(self, item);
        self.inherited = saved;
    }

    fn visit_foreign_item(&mut self, item: &'tcx ForeignItem<'tcx>) {
        let saved =
            self.enter(item.hir_id(), item.owner_id, matches!(item.kind, ForeignItemKind::Fn(..)));
        rustc_hir::intravisit::walk_foreign_item(self, item);
        self.inherited = saved;
    }
}

struct TrustedItemScanner<'a, 'tcx> {
    ctxt: &'a ContextX<'tcx>,
    policies: &'a HashMap<LocalDefId, EffectiveTrust>,
    errors: Vec<VirErr>,
}

impl<'a, 'tcx> TrustedItemScanner<'a, 'tcx> {
    fn scan_item(&mut self, item: &'tcx Item<'tcx>) {
        let Some(policy) = self.policies.get(&item.owner_id.def_id).copied() else {
            return;
        };
        if !policy.in_trusted_closure() {
            return;
        }
        if matches!(item.kind, ItemKind::Use(..))
            && self.ctxt.tcx.parent_module_from_def_id(item.owner_id.def_id).to_local_def_id()
                == rustc_hir::CRATE_OWNER_ID.def_id
        {
            return;
        }
        let mut checker = RefChecker::new(
            self.ctxt,
            self.policies,
            item.owner_id,
            policy == EffectiveTrust::TrustedSpec,
        );
        checker.visit_item(item);
        self.errors.append(&mut checker.errors);
    }

    fn scan_impl_item(&mut self, item: &'tcx ImplItem<'tcx>) {
        let Some(policy) = self.policies.get(&item.owner_id.def_id).copied() else {
            return;
        };
        if !policy.in_trusted_closure() {
            return;
        }
        let mut checker = RefChecker::new(
            self.ctxt,
            self.policies,
            item.owner_id,
            policy == EffectiveTrust::TrustedSpec,
        );
        checker.visit_impl_item(item);
        self.errors.append(&mut checker.errors);
    }

    fn scan_trait_item(&mut self, item: &'tcx TraitItem<'tcx>) {
        let Some(policy) = self.policies.get(&item.owner_id.def_id).copied() else {
            return;
        };
        if !policy.in_trusted_closure() {
            return;
        }
        let mut checker = RefChecker::new(
            self.ctxt,
            self.policies,
            item.owner_id,
            policy == EffectiveTrust::TrustedSpec,
        );
        checker.visit_trait_item(item);
        self.errors.append(&mut checker.errors);
    }

    fn scan_foreign_item(&mut self, item: &'tcx ForeignItem<'tcx>) {
        let Some(policy) = self.policies.get(&item.owner_id.def_id).copied() else {
            return;
        };
        if !policy.in_trusted_closure() {
            return;
        }
        let mut checker = RefChecker::new(
            self.ctxt,
            self.policies,
            item.owner_id,
            policy == EffectiveTrust::TrustedSpec,
        );
        checker.visit_foreign_item(item);
        self.errors.append(&mut checker.errors);
    }
}

impl<'a, 'tcx> Visitor<'tcx> for TrustedItemScanner<'a, 'tcx> {
    type NestedFilter = nested_filter::All;

    fn maybe_tcx(&mut self) -> TyCtxt<'tcx> {
        self.ctxt.tcx
    }

    fn visit_item(&mut self, item: &'tcx Item<'tcx>) {
        self.scan_item(item);
        rustc_hir::intravisit::walk_item(self, item);
    }

    fn visit_impl_item(&mut self, item: &'tcx ImplItem<'tcx>) {
        self.scan_impl_item(item);
        rustc_hir::intravisit::walk_impl_item(self, item);
    }

    fn visit_trait_item(&mut self, item: &'tcx TraitItem<'tcx>) {
        self.scan_trait_item(item);
        rustc_hir::intravisit::walk_trait_item(self, item);
    }

    fn visit_foreign_item(&mut self, item: &'tcx ForeignItem<'tcx>) {
        self.scan_foreign_item(item);
        rustc_hir::intravisit::walk_foreign_item(self, item);
    }
}

struct RefChecker<'a, 'tcx> {
    ctxt: &'a ContextX<'tcx>,
    policies: &'a HashMap<LocalDefId, EffectiveTrust>,
    root_owner: OwnerId,
    signature_only: bool,
    errors: Vec<VirErr>,
}

impl<'a, 'tcx> RefChecker<'a, 'tcx> {
    fn new(
        ctxt: &'a ContextX<'tcx>,
        policies: &'a HashMap<LocalDefId, EffectiveTrust>,
        root_owner: OwnerId,
        signature_only: bool,
    ) -> Self {
        Self { ctxt, policies, root_owner, signature_only, errors: Vec::new() }
    }

    fn target_is_trusted(&self, def_id: DefId) -> bool {
        let Some(mut local) = def_id.as_local() else {
            return true;
        };
        loop {
            if let Some(policy) = self.policies.get(&local) {
                return policy.in_trusted_closure();
            }
            if local == rustc_hir::CRATE_OWNER_ID.def_id {
                return false;
            }
            let parent = self.ctxt.tcx.parent(local.to_def_id());
            let Some(parent) = parent.as_local() else {
                return true;
            };
            local = parent;
        }
    }

    fn check_ref(&mut self, def_id: DefId, span: Span) {
        if self.target_is_trusted(def_id) {
            return;
        }
        self.errors.push(vir_err_span_str(
            span,
            "trusted code may not reference an untrusted item in the same crate; trusted code must be transitively closed",
        ));
    }

    fn scan_signature_headers(&mut self, body_id: BodyId) {
        let body = self.ctxt.tcx.hir_body(body_id);
        let mut finder =
            HeaderFinder { ctxt: self.ctxt, root_owner: self.root_owner, header_exprs: Vec::new() };
        finder.visit_expr(body.value);
        for expr in finder.header_exprs {
            self.visit_expr(expr);
        }
    }
}

impl<'a, 'tcx> Visitor<'tcx> for RefChecker<'a, 'tcx> {
    type NestedFilter = nested_filter::All;

    fn maybe_tcx(&mut self) -> TyCtxt<'tcx> {
        self.ctxt.tcx
    }

    fn visit_item(&mut self, item: &'tcx Item<'tcx>) {
        if item.owner_id == self.root_owner {
            rustc_hir::intravisit::walk_item(self, item);
        }
    }

    fn visit_impl_item(&mut self, item: &'tcx ImplItem<'tcx>) {
        if item.owner_id == self.root_owner {
            rustc_hir::intravisit::walk_impl_item(self, item);
        }
    }

    fn visit_trait_item(&mut self, item: &'tcx TraitItem<'tcx>) {
        if item.owner_id == self.root_owner {
            rustc_hir::intravisit::walk_trait_item(self, item);
        }
    }

    fn visit_foreign_item(&mut self, item: &'tcx ForeignItem<'tcx>) {
        if item.owner_id == self.root_owner {
            rustc_hir::intravisit::walk_foreign_item(self, item);
        }
    }

    fn visit_fn(
        &mut self,
        kind: FnKind<'tcx>,
        decl: &'tcx FnDecl<'tcx>,
        body_id: BodyId,
        _span: Span,
        def_id: LocalDefId,
    ) {
        if self.signature_only && def_id == self.root_owner.def_id {
            rustc_hir::intravisit::walk_fn_kind(self, kind);
            rustc_hir::intravisit::walk_fn_decl(self, decl);
            self.scan_signature_headers(body_id);
        } else {
            rustc_hir::intravisit::walk_fn(self, kind, decl, body_id, def_id);
        }
    }

    fn visit_path(&mut self, path: &rustc_hir::Path<'tcx>, _id: HirId) {
        if let Res::Def(_, def_id) = path.res {
            self.check_ref(def_id, path.span);
        }
        rustc_hir::intravisit::walk_path(self, path);
    }

    fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
        if let ExprKind::MethodCall(..) = expr.kind {
            let owner = expr.hir_id.owner.def_id;
            if let Some(def_id) = self.ctxt.tcx.typeck(owner).type_dependent_def_id(expr.hir_id) {
                self.check_ref(def_id, expr.span);
            }
        }
        rustc_hir::intravisit::walk_expr(self, expr);
    }
}

struct HeaderFinder<'a, 'tcx> {
    ctxt: &'a ContextX<'tcx>,
    root_owner: OwnerId,
    header_exprs: Vec<&'tcx Expr<'tcx>>,
}

impl<'a, 'tcx> HeaderFinder<'a, 'tcx> {
    fn is_specification_header(&self, def_id: DefId) -> bool {
        matches!(
            self.ctxt.get_verus_item(def_id),
            Some(VerusItem::Spec(
                SpecItem::Requires
                    | SpecItem::Recommends
                    | SpecItem::Ensures
                    | SpecItem::Returns
                    | SpecItem::Decreases
                    | SpecItem::DecreasesWhen
                    | SpecItem::DecreasesBy
                    | SpecItem::RecommendsBy
                    | SpecItem::OpensInvariantMask
                    | SpecItem::NoUnwind
                    | SpecItem::NoUnwindWhen
                    | SpecItem::AtomicSpec
            )) | Some(VerusItem::Directive(DirectiveItem::ExtraDependency))
        )
    }
}

impl<'a, 'tcx> Visitor<'tcx> for HeaderFinder<'a, 'tcx> {
    type NestedFilter = nested_filter::All;

    fn maybe_tcx(&mut self) -> TyCtxt<'tcx> {
        self.ctxt.tcx
    }

    fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
        if expr.hir_id.owner != self.root_owner {
            return;
        }
        if let ExprKind::Call(callee, args) = expr.kind
            && let ExprKind::Path(qpath) = callee.kind
            && let Res::Def(_, def_id) =
                self.ctxt.tcx.typeck(self.root_owner.def_id).qpath_res(&qpath, callee.hir_id)
            && self.is_specification_header(def_id)
        {
            self.header_exprs.extend(args);
            return;
        }
        rustc_hir::intravisit::walk_expr(self, expr);
    }
}
