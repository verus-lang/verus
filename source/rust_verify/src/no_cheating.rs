//! Structural checks for the `--no-cheating` trust policy.
//!
//! Code is untrusted by default. `#[verus::trusted]` permits assumptions and is inherited by
//! child items. `#[verus::untrusted]` overrides inherited trust and permanently prevents child
//! items from opting back into trust. `#[verus::trusted(spec)]` trusts a function's type-level
//! signature and Verus specification for reference closure while leaving its body untrusted;
//! like `#[verus::untrusted]`, it prevents items nested in that body from opting back into trust.

use crate::attributes::{TrustAttribute, get_trust_attributes};
use crate::config::Vstd;
use crate::context::ContextX;
use crate::util::vir_err_span_str;
use crate::verus_items::{DirectiveItem, SpecItem, VerusItem};
use rustc_hir::def::{DefKind, Res};
use rustc_hir::def_id::{DefId, LocalDefId};
use rustc_hir::intravisit::{FnKind, Visitor};
use rustc_hir::{
    AmbigArg, BodyId, Expr, ExprKind, FnDecl, ForeignItem, ForeignItemKind, HirId, ImplItem,
    ImplItemKind, Item, ItemKind, OwnerId, PatExpr, PatExprKind, QPath, TraitItem, TraitItemKind,
    TyKind,
};
use rustc_middle::hir::nested_filter;
use rustc_middle::traits::ImplSource;
use rustc_middle::ty::adjustment::{Adjust, DerefAdjustKind};
use rustc_middle::ty::{
    self, GenericArgsRef, TraitRef, Ty, TyCtxt, TypeVisitableExt, TypeckResults, TypingEnv,
};
use rustc_span::Span;
use std::collections::{HashMap, HashSet};
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
    /// Set by `#[verus::untrusted]` and `#[verus::trusted(spec)]`: no descendant may be trusted.
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
            // The body of the function is untrusted, so items nested in it must be untrusted too
            inherited.untrusted_locked = true;
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
    collector.visit_mod(root_module, root_owner.span(), rustc_span::def_id::CRATE_MOD_ID);
    collector.inherited = saved;

    let mut errors = collector.errors;
    let policies = collector.policies;
    let mut scanner = TrustedItemScanner { ctxt, policies: &policies, errors: Vec::new() };
    scanner.visit_mod(root_module, root_owner.span(), rustc_span::def_id::CRATE_MOD_ID);
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
                "a child of an item marked `#[verus::untrusted]` or `#[verus::trusted(spec)]` cannot be marked trusted",
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
        if matches!(item.kind, ItemKind::Use(..)) {
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

/// Bound on how deeply `check_trait_ref` follows the nested obligations of selected impls.
const MAX_IMPL_DEPTH: usize = 16;

struct RefChecker<'a, 'tcx> {
    ctxt: &'a ContextX<'tcx>,
    policies: &'a HashMap<LocalDefId, EffectiveTrust>,
    root_owner: OwnerId,
    signature_only: bool,
    /// Typeck results for the body currently being visited (`None` outside of bodies)
    typeck: Option<&'tcx TypeckResults<'tcx>>,
    /// Trait references whose impls have already been checked
    checked_trait_refs: HashSet<TraitRef<'tcx>>,
    /// Items already reported, to avoid repeating the same error at every use
    reported: HashSet<DefId>,
    errors: Vec<VirErr>,
}

impl<'a, 'tcx> RefChecker<'a, 'tcx> {
    fn new(
        ctxt: &'a ContextX<'tcx>,
        policies: &'a HashMap<LocalDefId, EffectiveTrust>,
        root_owner: OwnerId,
        signature_only: bool,
    ) -> Self {
        Self {
            ctxt,
            policies,
            root_owner,
            signature_only,
            typeck: None,
            checked_trait_refs: HashSet::new(),
            reported: HashSet::new(),
            errors: Vec::new(),
        }
    }

    fn target_is_trusted(&self, def_id: DefId) -> bool {
        let Some(mut local) = def_id.as_local() else {
            return true;
        };
        let tcx = self.ctxt.tcx;
        // generic parameters carry no code
        if matches!(
            tcx.def_kind(def_id),
            DefKind::TyParam | DefKind::ConstParam | DefKind::LifetimeParam
        ) {
            return true;
        }
        // vstd embedded in core
        if self.ctxt.cmd_line_args.vstd == Vstd::IsCore
            && matches!(
                tcx.def_path(def_id).data.first().and_then(|d| d.data.get_opt_name()),
                Some(name) if matches!(name.as_str(), "vstd" | "verus_builtin")
            )
        {
            return true;
        }
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

    /// An impl is trusted if it is in the trusted closure, or if it is derived (by
    /// `#[derive]`) for a type that is in the trusted closure.
    fn impl_is_trusted(&self, impl_def_id: DefId) -> bool {
        if self.target_is_trusted(impl_def_id) {
            return true;
        }
        let tcx = self.ctxt.tcx;
        tcx.is_automatically_derived(impl_def_id)
            && match tcx.type_of(impl_def_id).instantiate_identity().skip_norm_wip().kind() {
                ty::Adt(adt, _) => self.target_is_trusted(adt.did()),
                _ => false,
            }
    }

    /// An impl item is trusted if it is in the trusted closure or belongs to a trusted derived impl.
    fn impl_item_is_trusted(&self, item_def_id: DefId) -> bool {
        if self.target_is_trusted(item_def_id) {
            return true;
        }
        let tcx = self.ctxt.tcx;
        let impl_def_id = tcx.parent(item_def_id);
        tcx.is_automatically_derived(impl_def_id) && self.impl_is_trusted(impl_def_id)
    }

    fn report_untrusted_impl(&mut self, def_id: DefId, span: Span, what: &str) {
        if !self.reported.insert(def_id) {
            return;
        }
        let name = self.ctxt.tcx.def_path_str(def_id);
        self.errors.push(vir_err_span_str(
            span,
            &format!(
                "trusted code may not depend on the untrusted {what} `{name}` in the same crate; trusted code must be transitively closed"
            ),
        ));
    }

    fn typing_env(&self) -> TypingEnv<'tcx> {
        TypingEnv::post_analysis(self.ctxt.tcx, self.root_owner.def_id)
    }

    /// Select the impl that satisfies `trait_ref`, and require it (and every impl it in turn
    /// relies on) to be trusted if it is local.  References to trait items resolve to the trait,
    /// not the impl, so without this check trusted code could silently depend on untrusted
    /// impls (e.g., an untrusted `impl View for S` giving meaning to `s@` in a trusted spec).
    fn check_trait_ref(&mut self, trait_ref: TraitRef<'tcx>, span: Span, depth: usize) {
        let tcx = self.ctxt.tcx;
        if depth > MAX_IMPL_DEPTH || trait_ref.references_error() {
            return;
        }
        let typing_env = self.typing_env();
        let Ok(trait_ref) = tcx.try_normalize_erasing_regions(
            typing_env,
            rustc_middle::ty::Unnormalized::new_wip(trait_ref),
        ) else {
            return;
        };
        if !self.checked_trait_refs.insert(trait_ref) {
            return;
        }
        let Ok(ImplSource::UserDefined(impl_data)) =
            tcx.codegen_select_candidate(typing_env.as_query_input(trait_ref))
        else {
            // Builtin impls carry no user code; `Param` means the obligation is discharged by a
            // where-clause of the trusted item, which is itself checked at each use.
            return;
        };
        let impl_def_id = impl_data.impl_def_id;
        if impl_def_id.is_local() && !self.impl_is_trusted(impl_def_id) {
            self.report_untrusted_impl(impl_def_id, span, "impl");
        }
        let predicates = tcx.clauses_of(impl_def_id).instantiate(tcx, impl_data.args);
        self.check_clauses(
            predicates.clauses.into_iter().map(|c| c.skip_norm_wip()),
            span,
            depth + 1,
        );
    }

    fn check_clauses(
        &mut self,
        clauses: impl IntoIterator<Item = ty::Clause<'tcx>>,
        span: Span,
        depth: usize,
    ) {
        let tcx = self.ctxt.tcx;
        for clause in clauses {
            if let Some(trait_clause) = clause.as_trait_clause() {
                let trait_ref = tcx.instantiate_bound_regions_with_erased(trait_clause).trait_ref;
                self.check_trait_ref(trait_ref, span, depth);
            }
        }
    }

    /// Check a use of `def_id` instantiated with `args`: every trait bound of `def_id` must be
    /// satisfied by trusted impls, and a trait item must resolve to a trusted impl item.
    fn check_instantiation(&mut self, def_id: DefId, args: GenericArgsRef<'tcx>, span: Span) {
        let tcx = self.ctxt.tcx;
        if args.references_error()
            || !matches!(
                tcx.def_kind(def_id),
                DefKind::Fn
                    | DefKind::AssocFn
                    | DefKind::AssocConst { .. }
                    | DefKind::AssocTy
                    | DefKind::Const { .. }
                    | DefKind::Struct
                    | DefKind::Enum
                    | DefKind::Union
                    | DefKind::Ctor(..)
                    | DefKind::Variant
                    | DefKind::TyAlias
            )
        {
            return;
        }
        if args.len() != tcx.generics_of(def_id).count() {
            return;
        }
        let predicates = tcx.clauses_of(def_id).instantiate(tcx, args);
        self.check_clauses(predicates.clauses.into_iter().map(|c| c.skip_norm_wip()), span, 0);
        if tcx.trait_of_assoc(def_id).is_some()
            && let Ok(crate::resolve_traits::ResolutionResult::Resolved {
                resolved_item: crate::resolve_traits::ResolvedItem::FromImpl(item_def_id, _),
                ..
            }) = crate::resolve_traits::resolve_trait_item(
                span,
                tcx,
                self.typing_env(),
                def_id,
                args,
            )
            && item_def_id.is_local()
            && !self.impl_item_is_trusted(item_def_id)
        {
            self.report_untrusted_impl(item_def_id, span, "impl item");
        }
    }

    /// Trusted code that drops a value runs the value's `Drop` impl.
    fn check_drop_ty(&mut self, ty: Ty<'tcx>, span: Span, depth: usize) {
        if depth > MAX_IMPL_DEPTH {
            return;
        }
        match ty.kind() {
            ty::Adt(adt, args) => {
                if adt.is_phantom_data() {
                    return;
                }
                if let Some(destructor) = self.ctxt.tcx.adt_destructor(adt.did())
                    && destructor.did.is_local()
                    && !self.impl_item_is_trusted(destructor.did)
                {
                    self.report_untrusted_impl(destructor.did, span, "destructor");
                }
                for arg_ty in args.types() {
                    self.check_drop_ty(arg_ty, span, depth + 1);
                }
            }
            ty::Tuple(tys) => {
                for t in tys.iter() {
                    self.check_drop_ty(t, span, depth + 1);
                }
            }
            ty::Array(t, _) | ty::Slice(t) => self.check_drop_ty(*t, span, depth + 1),
            _ => {}
        }
    }

    /// Check the def that typeck resolved for a type-dependent node (method calls, overloaded
    /// operators, and type-relative paths such as `S::f` or `Self::C`).
    fn check_type_dependent(&mut self, hir_id: HirId, span: Span) {
        let Some(typeck) = self.typeck else { return };
        if let Some((_, def_id)) = typeck.type_dependent_def(hir_id) {
            self.check_ref(def_id, span);
            self.check_instantiation(def_id, typeck.node_args(hir_id), span);
        }
    }

    fn check_adjustments(&mut self, expr: &'tcx Expr<'tcx>) {
        let Some(typeck) = self.typeck else { return };
        let tcx = self.ctxt.tcx;
        let mut source = typeck.expr_ty(expr);
        for adjustment in typeck.expr_adjustments(expr) {
            if let Adjust::Deref(DerefAdjustKind::Overloaded(overloaded)) = adjustment.kind {
                let method = overloaded.method_call(tcx);
                let args = tcx.mk_args(&[source.into()]);
                self.check_ref(method, expr.span);
                self.check_instantiation(method, args, expr.span);
            }
            source = adjustment.target;
        }
    }

    /// Projections written in types (`<S as Tr>::Out`, `Self::Out`) are resolved through impls.
    fn check_ty_projections(&mut self, hir_ty: &'tcx rustc_hir::Ty<'tcx>) {
        let tcx = self.ctxt.tcx;
        let ty = rustc_hir_analysis::lower_ty(tcx, hir_ty);
        for arg in ty.walk() {
            if let ty::GenericArgKind::Type(t) = arg.kind()
                && let ty::Alias(_, alias_ty) = t.kind()
                && let ty::AliasTyKind::Projection { def_id } = alias_ty.kind
            {
                self.check_instantiation(def_id, alias_ty.args, hir_ty.span);
            }
        }
    }

    fn scan_signature_headers(&mut self, body_id: BodyId) {
        let body = self.ctxt.tcx.hir_body(body_id);
        let mut finder =
            HeaderFinder { ctxt: self.ctxt, root_owner: self.root_owner, header_exprs: Vec::new() };
        finder.visit_expr(body.value);
        let saved = self.typeck.replace(self.ctxt.tcx.typeck_body(body_id));
        for expr in finder.header_exprs {
            self.visit_expr(expr);
        }
        self.typeck = saved;
    }
}

impl<'a, 'tcx> Visitor<'tcx> for RefChecker<'a, 'tcx> {
    type NestedFilter = nested_filter::All;

    fn maybe_tcx(&mut self) -> TyCtxt<'tcx> {
        self.ctxt.tcx
    }

    fn visit_nested_body(&mut self, body_id: BodyId) {
        let saved = self.typeck.replace(self.ctxt.tcx.typeck_body(body_id));
        self.visit_body(self.ctxt.tcx.hir_body(body_id));
        self.typeck = saved;
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

    fn visit_ty(&mut self, t: &'tcx rustc_hir::Ty<'tcx, AmbigArg>) {
        if matches!(
            t.kind,
            TyKind::Path(QPath::TypeRelative(..)) | TyKind::Path(QPath::Resolved(Some(_), _))
        ) {
            self.check_ty_projections(t.as_unambig_ty());
        }
        rustc_hir::intravisit::walk_ty(self, t);
    }

    fn visit_pat(&mut self, pat: &'tcx rustc_hir::Pat<'tcx>) {
        if let Some(typeck) = self.typeck
            && let Some(ty) = typeck.node_type_opt(pat.hir_id)
            && matches!(pat.kind, rustc_hir::PatKind::Binding(..))
        {
            self.check_drop_ty(ty, pat.span, 0);
        }
        rustc_hir::intravisit::walk_pat(self, pat);
    }

    fn visit_pat_expr(&mut self, expr: &'tcx PatExpr<'tcx>) {
        if let PatExprKind::Path(_) = expr.kind {
            self.check_type_dependent(expr.hir_id, expr.span);
        }
        rustc_hir::intravisit::walk_pat_expr(self, expr);
    }

    fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
        // Method calls, overloaded operators, and type-relative paths (`S::f`)
        self.check_type_dependent(expr.hir_id, expr.span);
        if let Some(typeck) = self.typeck {
            if let ExprKind::Path(qpath) = &expr.kind
                && let Res::Def(_, def_id) = typeck.qpath_res(qpath, expr.hir_id)
                && typeck.type_dependent_def(expr.hir_id).is_none()
            {
                // Paths resolved directly (`f::<S>`, `<S as Tr>::f`, lang items like
                // `IntoIterator::into_iter` in `for` loops)
                self.check_ref(def_id, expr.span);
                self.check_instantiation(def_id, typeck.node_args(expr.hir_id), expr.span);
            }
            if let Some(ty) = typeck.node_type_opt(expr.hir_id)
                && !matches!(expr.kind, ExprKind::Path(..))
            {
                // Temporaries are dropped by the trusted code
                self.check_drop_ty(ty, expr.span, 0);
            }
            self.check_adjustments(expr);
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
