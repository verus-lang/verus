//! VIR-level verification observer.
//!
//! Defines `VirObserver` — callbacks fired during VIR→AIR lowering (havoc,
//! assign, branch/break merges, loops, quantifier binders, reveals, and
//! function/krate lifecycle).
//!
//! This trait is independent: it does **not** require `AirObserver` or
//! `QueryResultObserver`. A consumer implements only the traits it needs; the
//! verifier wires each implemented trait to its own callbacks (see the observer
//! handle registry in `rust_verify/src/verifier.rs`).

use crate::ast::{Krate, Typ, VarIdent};
use crate::sst::{Exp, Stm};
use air::ast::AssertId;
use std::any::Any;

// Re-export for convenience (used by `VersionCorrelator::resolve`).
pub use air::air_observer::VersionOrigin;

/// What kind of assertion is being assigned an ID.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum AssertIdKind {
    Ensures,
    LoopInvariant,
    DecreasesCheck,
}

/// Observer for the VIR-level verification pipeline.
///
/// Callbacks fire during VIR→AIR lowering. All methods have default no-op
/// implementations except `as_any`/`as_any_mut` (trivially: `self`).
pub trait VirObserver: Any {
    /// Fired once per module in `Ctx::new`. The `NameCtxt` is the same instance
    /// used by lowering, so AIR names computed by the observer are consistent
    /// with the names lowering will produce. `current_crate` identifies the
    /// crate under verification, so observers can strip its prefix from
    /// friendly names (e.g. render `double(x)` not `test_crate::double(x)`).
    fn on_krate(
        &mut self,
        _krate: &Krate,
        _name_ctxt: &crate::def::NameCtxt,
        _current_crate: &crate::ast::CrateId,
    ) {
    }
    fn on_havoc(&mut self, _stm: &Stm, _var: &VarIdent) {}
    fn on_assign(&mut self, _stm: &Stm, _var: &VarIdent) {}
    fn on_variable_def(&mut self, _stm: &Stm, _var: &VarIdent) {}
    fn on_branch_merge(&mut self, _stm: &Stm) {}
    fn on_break_merge(&mut self, _stm: &Stm) {}
    fn on_for_loop(&mut self, _stm: &Stm) {}
    fn on_quantifier_binder(&mut self, _binder: &crate::ast::VarBinder<Typ>, _exp: &Exp) {}
    fn on_reveal_string(&mut self, _lit: &std::sync::Arc<String>) {}
    fn make_assert_id(
        &mut self,
        _kind: &AssertIdKind,
        _index: usize,
        parent: &Option<AssertId>,
    ) -> Option<AssertId> {
        parent.clone()
    }
    /// A quantifier binder local declaration was processed.
    /// Fires for each QuantBinder in local_decls after body lowering,
    /// including Skolemized copies (e.g., i$0, i$1). The observer can
    /// correlate with the original binder's line via prefix matching
    /// on suffix_local_unique_id(var).
    /// Fires for choose binders as well as quantifier binders.
    fn on_quantifier_binder_decl(&mut self, _var: &VarIdent) {}
    /// Called at the start of function body lowering (body_stm_to_air).
    /// Binders recorded after this point are body-level binders.
    /// Observers should clear any pre-body binder accumulation here.
    fn on_body_lowering_start(&mut self) {}
    fn on_function_lowered(&mut self) {}

    fn as_any(&self) -> &dyn Any;
    fn as_any_mut(&mut self) -> &mut dyn Any;
}

/// Registry of per-trait observer handles: independent trait-object views of
/// (up to) one shared observer object. Each field is `Some` only if the observer
/// implements that trait, so a consumer couples nothing it does not use. All
/// populated fields point at the same underlying `RefCell` (via `Rc` unsizing
/// coercion at the factory), so callbacks mutate one shared object.
#[derive(Clone, Default)]
pub struct Observers {
    pub vir: Option<std::rc::Rc<std::cell::RefCell<dyn VirObserver>>>,
    pub air: Option<std::rc::Rc<std::cell::RefCell<dyn air::air_observer::AirObserver>>>,
    pub query_result: Option<
        std::rc::Rc<std::cell::RefCell<dyn air::query_result_observer::QueryResultObserver>>,
    >,
}

use std::collections::{HashMap, VecDeque};
use std::sync::Arc;

/// Extract line number from a VIR span's string representation ("file:line:col:...").
pub fn line_from_span(span: &crate::messages::Span) -> Option<u32> {
    span.as_string.split(':').nth(1)?.trim().parse().ok()
}

/// Strip the version suffix from a versioned WP constant name.
/// `"x@2"` → `"x@"`, `"foo!@3"` → `"foo!@"`
fn strip_version_suffix(name: &str) -> &str {
    if let Some(pos) = name.rfind('@') { &name[..=pos] } else { name }
}

/// Helper for observers that need to correlate VIR-level
/// `on_havoc`/`on_assign` callbacks with AIR-level WP versioned
/// constants created during `lower_query`.
///
/// # Ordering invariant
///
/// For each variable `x`, the Nth `record_havoc_or_assign` call
/// corresponds to the Nth `resolve` call with a `Havoc` or `Assign`
/// origin. This ordering is guaranteed because VIR emits
/// Havoc/Assign statements in the same order that `lower_query`
/// processes them. No AIR pass reorders these statements.
///
/// Enforced via `debug_assert!` in `resolve`.
pub struct VersionCorrelator {
    /// Per-base-variable queue of VIR statements (Havoc/Assign).
    queues: HashMap<Arc<String>, VecDeque<Stm>>,
    /// Most recent branch merge stm.
    last_branch_merge: Option<Stm>,
    /// Most recent break merge stm.
    last_break_merge: Option<Stm>,
}

impl VersionCorrelator {
    pub fn new() -> Self {
        Self { queues: HashMap::new(), last_branch_merge: None, last_break_merge: None }
    }

    /// Record a VIR-level Havoc or Assign for a variable.
    /// `base` is the AIR base name (e.g., `"x@"` from `suffix_local_unique_id`).
    pub fn record_havoc_or_assign(&mut self, base: &air::ast::Ident, stm: &Stm) {
        self.queues.entry(base.clone()).or_default().push_back(stm.clone());
    }

    /// Record a branch merge point (from `on_branch_merge`).
    pub fn record_branch_merge(&mut self, stm: &Stm) {
        self.last_branch_merge = Some(stm.clone());
    }

    /// Record a break merge point (from `on_break_merge`).
    pub fn record_break_merge(&mut self, stm: &Stm) {
        self.last_break_merge = Some(stm.clone());
    }

    /// Resolve an AIR versioned constant to its VIR origin.
    /// Returns the VIR `Stm` that caused this version to exist.
    pub fn resolve(&mut self, versioned: &air::ast::Ident, kind: VersionOrigin) -> Option<Stm> {
        match kind {
            VersionOrigin::Havoc | VersionOrigin::Assign => {
                let base = strip_version_suffix(versioned);
                let base_key = Arc::new(base.to_string());
                let queue = self.queues.get_mut(&base_key)?;
                debug_assert!(
                    !queue.is_empty(),
                    "VIR/AIR ordering invariant violated for {}: \
                     no VIR record available (queue empty)",
                    versioned
                );
                queue.pop_front()
            }
            VersionOrigin::BranchMerge => self.last_branch_merge.clone(),
            VersionOrigin::BreakMerge => self.last_break_merge.clone(),
        }
    }

    /// Reset between functions.
    pub fn reset(&mut self) {
        self.queues.clear();
        self.last_branch_merge = None;
        self.last_break_merge = None;
    }
}
