//! `--no-cheating` structural checks for `#[allow(verus::assumptions)]`
//! (the actual `assume`/`external_body`/... checks live in `well_formed.rs`):
//! 1. the crate root must contain `#![deny(verus::assumptions)]`;
//! 2. `#[allow(verus::assumptions)]` may only appear in the crate root, on a `mod` item;
//! 3. that `mod` must be a file-level module (`mod name;`);
//! 4. an allow-module subtree may only reference other allow-modules, `vstd`, external crates,
//!    and crate-root items (not non-allow modules of this crate).

use crate::attributes::{LintLevel, get_assumptions_lint_level};
use crate::context::ContextX;
use crate::util::vir_err_span_str;
use rustc_hir::def::{DefKind, Res};
use rustc_hir::def_id::DefId;
use rustc_hir::intravisit::Visitor;
use rustc_hir::{Expr, ExprKind, HirId, ItemKind, MaybeOwner, OwnerNode};
use rustc_middle::hir::nested_filter;
use rustc_span::Span;
use std::collections::HashSet;
use vir::ast::{Path, VirErr};

/// True if `module_path` is at or under one of the `allow_roots` file-modules.
fn in_allow_subtree(allow_roots: &[Path], module_path: &Path) -> bool {
    allow_roots.iter().any(|root| module_path.matches_prefix(root))
}

/// Run the `--no-cheating` structural checks, returning the allow-module paths (used by the
/// caller to mark VIR `ModuleX`es) and any errors found.
pub(crate) fn check_assumptions<'tcx>(ctxt: &ContextX<'tcx>) -> (Vec<Path>, Vec<VirErr>) {
    let tcx = ctxt.tcx;
    let mut errors: Vec<VirErr> = Vec::new();

    // (1) The crate root must contain `#![deny(verus::assumptions)]` (`forbid` also accepted).
    let root_attrs = tcx.hir_attrs(rustc_hir::CRATE_HIR_ID);
    let root_has_deny = root_attrs
        .iter()
        .filter_map(get_assumptions_lint_level)
        .any(|(level, _)| matches!(level, LintLevel::Deny | LintLevel::Forbid));
    if !root_has_deny {
        let span = tcx.def_span(rustc_hir::CRATE_OWNER_ID.to_def_id());
        errors.push(vir_err_span_str(
            span,
            "with --no-cheating, the crate root must contain `#![deny(verus::assumptions)]`",
        ));
    }

    // Record allow-modules: file-level `mod`s in the crate root marked
    // `#[allow(verus::assumptions)]`. Misplaced `allow`s are reported in the scan below.
    let mut allow_roots: Vec<Path> = Vec::new();
    let mut allow_root_owners: HashSet<rustc_hir::OwnerId> = HashSet::new();
    let root_module = tcx.hir_root_module();
    for item_id in root_module.item_ids {
        let item = tcx.hir_item(*item_id);
        let is_allow = tcx
            .hir_attrs(item.hir_id())
            .iter()
            .filter_map(get_assumptions_lint_level)
            .any(|(level, _)| level == LintLevel::Allow);
        if !is_allow {
            continue;
        }
        if let ItemKind::Mod(_, module) = item.kind {
            let sm = tcx.sess.source_map();
            let is_file_level =
                sm.span_to_filename(item.span) != sm.span_to_filename(module.spans.inner_span);
            if is_file_level {
                allow_roots.push(ctxt.def_id_to_vir_path(item.owner_id.to_def_id()));
                allow_root_owners.insert(item.owner_id);
            }
        }
    }

    // Report misplaced `verus::assumptions` lint attributes: `allow` anywhere but a
    // recorded crate-root file-module, or any other level anywhere but the crate root.
    for owner in crate::util::iter_crate_owners(ctxt.krate, tcx) {
        let MaybeOwner::Owner(owner_info) = owner else {
            continue;
        };
        let (hir_id, owner_id, is_crate_root) = match owner_info.node() {
            OwnerNode::Crate(_) => (rustc_hir::CRATE_HIR_ID, rustc_hir::CRATE_OWNER_ID, true),
            OwnerNode::Item(i) => (i.hir_id(), i.owner_id, false),
            OwnerNode::ImplItem(i) => (i.hir_id(), i.owner_id, false),
            OwnerNode::TraitItem(i) => (i.hir_id(), i.owner_id, false),
            OwnerNode::ForeignItem(i) => (i.hir_id(), i.owner_id, false),
            OwnerNode::Synthetic => continue,
        };
        for attr in tcx.hir_attrs(hir_id) {
            let Some((level, span)) = get_assumptions_lint_level(attr) else {
                continue;
            };
            match level {
                LintLevel::Allow => {
                    if !allow_root_owners.contains(&owner_id) {
                        errors.push(vir_err_span_str(
                            span,
                            "#[allow(verus::assumptions)] may only be placed on a file-level module (`mod name;`) declared in the crate root",
                        ));
                    }
                }
                LintLevel::Warn | LintLevel::Deny | LintLevel::Forbid => {
                    if !is_crate_root {
                        errors.push(vir_err_span_str(
                            span,
                            "the verus::assumptions lint level may only be set as `#![deny(verus::assumptions)]` in the crate root",
                        ));
                    }
                }
            }
        }
    }

    // (4) The allow-module subtrees must be closed under references.
    errors.extend(check_reference_closure(ctxt, &allow_roots));

    (allow_roots, errors)
}

/// No item in an allow-module subtree may reference a non-allow module of this
/// crate. References to allow-modules, `vstd`, external crates, and crate-root items are fine.
fn check_reference_closure<'tcx>(ctxt: &ContextX<'tcx>, allow_roots: &[Path]) -> Vec<VirErr> {
    if allow_roots.is_empty() {
        return Vec::new();
    }
    let tcx = ctxt.tcx;
    let mut checker = RefChecker {
        ctxt,
        allow_roots,
        root_module_path: crate::rust_to_vir::get_root_module_path(ctxt),
        errors: Vec::new(),
    };
    for owner in crate::util::iter_crate_owners(ctxt.krate, tcx) {
        let MaybeOwner::Owner(owner_info) = owner else {
            continue;
        };
        let node = owner_info.node();
        let owner_def_id = match node {
            OwnerNode::Item(i) => i.owner_id.def_id,
            OwnerNode::ImplItem(i) => i.owner_id.def_id,
            OwnerNode::TraitItem(i) => i.owner_id.def_id,
            OwnerNode::ForeignItem(i) => i.owner_id.def_id,
            OwnerNode::Crate(_) | OwnerNode::Synthetic => continue,
        };
        // The module this item lives in (a `mod` item reports its parent, which is harmless).
        let containing_module =
            tcx.parent_module_from_def_id(owner_def_id).to_local_def_id().to_def_id();
        let module_path = ctxt.def_id_to_vir_path(containing_module);
        if !in_allow_subtree(allow_roots, &module_path) {
            continue;
        }
        match node {
            OwnerNode::Item(i) => checker.visit_item(i),
            OwnerNode::ImplItem(i) => checker.visit_impl_item(i),
            OwnerNode::TraitItem(i) => checker.visit_trait_item(i),
            OwnerNode::ForeignItem(i) => checker.visit_foreign_item(i),
            OwnerNode::Crate(_) | OwnerNode::Synthetic => {}
        }
    }
    checker.errors
}

struct RefChecker<'a, 'tcx> {
    ctxt: &'a ContextX<'tcx>,
    allow_roots: &'a [Path],
    root_module_path: Path,
    errors: Vec<VirErr>,
}

impl<'a, 'tcx> RefChecker<'a, 'tcx> {
    /// Check a single reference (to `def_id`) made from within an allow-module subtree.
    fn check_ref(&mut self, def_id: DefId, span: Span) {
        // References to other crates (vstd, core/alloc/std, dependencies) are always fine.
        let Some(local) = def_id.as_local() else {
            return;
        };
        let tcx = self.ctxt.tcx;
        // The module this reference lands in (a reference to a `mod` counts as that module).
        let module_def_id = if tcx.def_kind(def_id) == DefKind::Mod {
            def_id
        } else {
            tcx.parent_module_from_def_id(local).to_local_def_id().to_def_id()
        };
        let module_path = self.ctxt.def_id_to_vir_path(module_def_id);
        // Crate-root items are the audit anchor and are always allowed.
        if module_path == self.root_module_path {
            return;
        }
        if in_allow_subtree(self.allow_roots, &module_path) {
            return;
        }
        self.errors.push(vir_err_span_str(
            span,
            "a module marked `#[allow(verus::assumptions)]` may not reference items in non-allow modules of this crate; the allow set must be transitively closed (only `vstd`, other external crates, crate-root items, and other `#[allow(verus::assumptions)]` modules may be referenced)",
        ));
    }
}

impl<'a, 'tcx> Visitor<'tcx> for RefChecker<'a, 'tcx> {
    // Visit nested bodies, but not nested items (which are visited as their own owners above).
    type NestedFilter = nested_filter::OnlyBodies;

    fn maybe_tcx(&mut self) -> rustc_middle::ty::TyCtxt<'tcx> {
        self.ctxt.tcx
    }

    fn visit_path(&mut self, path: &rustc_hir::Path<'tcx>, _id: HirId) {
        if let Res::Def(_, def_id) = path.res {
            self.check_ref(def_id, path.span);
        }
        rustc_hir::intravisit::walk_path(self, path);
    }

    fn visit_expr(&mut self, expr: &'tcx Expr<'tcx>) {
        // Method calls are type-dependent (not resolved `Path`s), so use the typeck results.
        if let ExprKind::MethodCall(..) = expr.kind {
            let owner = expr.hir_id.owner.def_id;
            if let Some(def_id) = self.ctxt.tcx.typeck(owner).type_dependent_def_id(expr.hir_id) {
                self.check_ref(def_id, expr.span);
            }
        }
        rustc_hir::intravisit::walk_expr(self, expr);
    }
}
