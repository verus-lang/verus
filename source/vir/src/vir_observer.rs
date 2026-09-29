//! Observer for the SST→AIR lowering.
//!
//! Defines `VirObserver` — callbacks fired during SST→AIR lowering (havoc,
//! assign, variable definitions, for-loops, quantifier binders, reveals,
//! assertion ids, and function/krate lifecycle).

use crate::ast::{Krate, Typ, VarIdent};
use crate::sst::{Exp, Stm};
use air::ast::AssertId;
use std::any::Any;

// Re-export for convenience (used by `VersionCorrelator::resolve`).
pub use air::air_observer::VersionOrigin;

/// The assertions whose ids an observer may supply through `make_assert_id`.
///
/// This is not every kind of assertion the lowering emits. Preconditions at call sites and
/// user `assert`s already carry a unique id from the SST and are not offered to the observer.
/// The three kinds here are the ones where the lowering's own id is not enough for a
/// consumer to tell assertions apart: loop invariants and decreases checks are emitted
/// without an id, and a function's postconditions all share the id of the enclosing return.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AssertIdKind {
    /// One of a function's `ensures` clauses; `index` is its position among them.
    Ensures,
    /// A loop invariant, checked at loop entry and at the end of the body; `index` is its
    /// position among the loop's invariants.
    LoopInvariant,
    /// A loop's decreases check.
    DecreasesCheck,
}

/// Callbacks fire during SST→AIR lowering. All methods have default no-op
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
    fn on_for_loop(&mut self, _stm: &Stm) {}
    fn on_quantifier_binder(&mut self, _binder: &crate::ast::VarBinder<Typ>, _exp: &Exp) {}
    fn on_reveal_string(&mut self, _lit: &std::sync::Arc<String>) {}
    /// Return the id the lowering should attach to this assertion, or keep `parent`
    /// (the lowering's own choice) by returning it unchanged, as the default does.
    fn make_assert_id(
        &mut self,
        _kind: AssertIdKind,
        _index: usize,
        parent: &Option<AssertId>,
    ) -> Option<AssertId> {
        parent.clone()
    }
    /// A binder-originated local declaration was processed: a quantifier binder or a
    /// choose binder (`decl.kind` says which), with its type. Fires for each such local
    /// after body lowering, including Skolemized copies (e.g. `i$0`, `i$1`); the observer
    /// can correlate with the original binder's line via prefix matching on
    /// `suffix_local_unique_id(&decl.ident)`.
    fn on_binder_decl(&mut self, _decl: &crate::sst::LocalDecl) {}
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

/// Extract the line number from a span's string representation ("file:line:col:...").
pub fn line_from_span(span: &crate::messages::Span) -> Option<u32> {
    span.as_string.split(':').nth(1)?.trim().parse().ok()
}

/// Strip the version suffix from a versioned WP constant name.
/// `"x@2"` → `"x@"`, `"foo!@3"` → `"foo!@"`
fn strip_version_suffix(name: &str) -> &str {
    if let Some(pos) = name.rfind('@') { &name[..=pos] } else { name }
}

/// Pairs `VirObserver::on_havoc`/`on_assign` callbacks with the versioned
/// constants that `lower_query` later creates for the same statements.
///
/// # Ordering invariant
///
/// For each variable `x`, the Nth `record_havoc_or_assign` call
/// corresponds to the Nth `resolve` call with a `Havoc` or `Assign`
/// origin. This holds because `sst_to_air` emits the AIR for SST
/// Havoc/Assign statements in the order `lower_query` walks them, and
/// no AIR pass in between reorders statements.
///
/// Enforced via `debug_assert!` in `resolve`.
pub struct VersionCorrelator {
    /// Per-base-variable queue of SST statements (Havoc/Assign).
    queues: HashMap<Arc<String>, VecDeque<Stm>>,
}

impl VersionCorrelator {
    pub fn new() -> Self {
        Self { queues: HashMap::new() }
    }

    /// Record an SST Havoc or Assign for a variable.
    /// `base` is the AIR base name (e.g., `"x@"` from `suffix_local_unique_id`).
    pub fn record_havoc_or_assign(&mut self, base: &air::ast::Ident, stm: &Stm) {
        self.queues.entry(base.clone()).or_default().push_back(stm.clone());
    }

    /// Resolve an AIR versioned constant to the SST statement that created it.
    pub fn resolve(&mut self, versioned: &air::ast::Ident, kind: VersionOrigin) -> Option<Stm> {
        match kind {
            VersionOrigin::Havoc | VersionOrigin::Assign => {
                let base = strip_version_suffix(versioned);
                let base_key = Arc::new(base.to_string());
                let queue = self.queues.get_mut(&base_key)?;
                debug_assert!(
                    !queue.is_empty(),
                    "SST/AIR ordering invariant violated for {}: \
                     no SST record available (queue empty)",
                    versioned
                );
                queue.pop_front()
            }
        }
    }

    /// Reset between functions.
    pub fn reset(&mut self) {
        self.queues.clear();
    }
}
