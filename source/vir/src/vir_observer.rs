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
    Ensures,
    LoopInvariant,
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
    // Havoc and Assign create new versions; `air_stmt`, the AIR statement `stm` lowers to,
    // lets an observer pair each version with `stm` (see `VersionCorrelator`).
    fn on_havoc(&mut self, _stm: &Stm, _var: &VarIdent, _air_stmt: &air::ast::Stmt) {}
    fn on_assign(&mut self, _stm: &Stm, _var: &VarIdent, _air_stmt: &air::ast::Stmt) {}
    fn on_variable_def(&mut self, _stm: &Stm, _var: &VarIdent) {}
    fn on_for_loop(&mut self, _stm: &Stm) {}
    fn on_quantifier_binder(&mut self, _binder: &crate::ast::VarBinder<Typ>, _exp: &Exp) {}
    fn on_reveal_string(&mut self, _lit: &std::sync::Arc<String>) {}
    fn on_span_resolver(&mut self, _resolver: &SpanResolver) {}
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
    pub span_resolver: Option<SpanResolver>,
}

use std::collections::{HashMap, VecDeque};
use std::sync::Arc;

/// The file and 1-based line where a span starts.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SourceLocation {
    pub file: Arc<String>,
    pub line: u32,
}

/// Where a span starts, from the compiler's source map; `None` if it has no position or its
/// file was not loaded when verification began.
pub type SpanResolver = Arc<
    dyn Fn(&crate::messages::Span) -> Option<SourceLocation>
        + Send
        + Sync
        + std::panic::RefUnwindSafe,
>;

/// Pairs each AIR versioned constant with the SST statement that created it.
///
/// A statement can appear in several queries of one lowering (statements before a loop are
/// copied into the loop's query), so pairing is per query: `record` maps each AIR
/// `Havoc`/`Assign` to its SST statement, `begin_query` lists the query's version-creating
/// statements in `lower_query` order, and `resolve` takes the next one. A version created in
/// several branch arms is resolved once per arm.
///
/// Records are released when the next lowering starts recording.
pub struct VersionCorrelator {
    sources: HashMap<usize, (air::ast::Stmt, Stm)>,
    current: VecDeque<(air::ast::Ident, VersionOrigin, Option<Stm>)>,
    checking: bool,
}

impl VersionCorrelator {
    pub fn new() -> Self {
        Self { sources: HashMap::new(), current: VecDeque::new(), checking: false }
    }

    /// Record that `air_stmt` (an AIR `Havoc` or `Assign`) was lowered from `stm`.
    pub fn record(&mut self, air_stmt: &air::ast::Stmt, stm: &Stm) {
        if self.checking {
            self.sources.clear();
            self.checking = false;
        }
        self.sources.insert(Arc::as_ptr(air_stmt) as usize, (air_stmt.clone(), stm.clone()));
    }

    /// Prepare to resolve the versions created while lowering `query`.
    pub fn begin_query(&mut self, query: &air::ast::Query) {
        self.checking = true;
        self.current.clear();
        self.collect(&query.assertion);
    }

    fn collect(&mut self, stmt: &air::ast::Stmt) {
        use air::ast::StmtX;
        match &**stmt {
            StmtX::Havoc(x) | StmtX::Assign(x, _) => {
                let kind = if matches!(&**stmt, StmtX::Havoc(_)) {
                    VersionOrigin::Havoc
                } else {
                    VersionOrigin::Assign
                };
                let src = self.sources.get(&(Arc::as_ptr(stmt) as usize)).map(|(_, s)| s.clone());
                self.current.push_back((x.clone(), kind, src));
            }
            StmtX::Block(ss) | StmtX::Switch(ss) => ss.iter().for_each(|s| self.collect(s)),
            StmtX::DeadEnd(s) | StmtX::Breakable(_, s) => self.collect(s),
            StmtX::Assume(_) | StmtX::Assert(..) | StmtX::Snapshot(_) | StmtX::Break(_) => {}
        }
    }

    /// The SST statement that created the version of `base` being reported; call once per
    /// `on_wp_version_created`. `None` for an `Initial` version, for AIR not produced by the SST
    /// lowering, and, after a `base` or `kind` that does not match the next statement, for the
    /// rest of the query.
    pub fn resolve(&mut self, base: &air::ast::Ident, kind: VersionOrigin) -> Option<Stm> {
        if kind == VersionOrigin::Initial {
            return None;
        }
        let (var, expected_kind, src) = self.current.pop_front()?;
        if base != &var || kind != expected_kind {
            self.current.clear();
            return None;
        }
        src
    }
}
