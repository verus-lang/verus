//! AIR-level verification pipeline observer.
//!
//! Defines `AirObserver` — the interface for observing the AIR-level
//! verification pipeline: query lowering, WP version creation, and lambda /
//! choose / axiom declarations.  Implementing this trait allows for recording
//! the results of AIR-level passes that are used to prepare a verification query
//! for the solver.

use crate::ast::{Binders, Decl, Expr, Ident, Query, Snapshots, Triggers, Typ};
use std::any::Any;

/// Origin of a WP versioned constant created during `lower_query`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VersionOrigin {
    /// Version 0 of a local, at the start of the query.
    Initial,
    /// From a `StmtX::Havoc` — unconstrained new version (loop entry).
    Havoc,
    /// From a `StmtX::Assign` — constrained new version (= rhs).
    Assign,
}

/// Observer for the AIR-level verification pipeline.
///
/// All methods have default no-op implementations except `as_any`
/// and `as_any_mut` which must be implemented (trivially: `self`).
pub trait AirObserver: Any {
    /// A query is about to be checked; `query` is the query as the caller constructed it,
    /// before any AIR pass.
    fn on_query_start(&mut self, _query: &Query) {}
    /// A verification query has been lowered (variables → versioned constants).
    /// `snapshots` maps each snapshot name to the variable versions current at that point;
    /// `local_vars` are the versioned-constant declarations this lowering introduced (the
    /// query's own pre-existing locals are in `query.local`).
    fn on_query_lowered(&mut self, _query: &Query, _snapshots: &Snapshots, _local_vars: &[Decl]) {}

    /// `lower_query` created version `version` of `base` (its AIR name, e.g. `x@` or `p!`) as the
    /// constant `versioned`. Versions are numbered per query: version 0 of each local is
    /// `Initial`; later versions come from a `Havoc` or `Assign`, reported once per creating
    /// statement (so once per branch arm that assigns). See `VersionCorrelator`.
    fn on_wp_version_created(
        &mut self,
        _versioned: &Ident,
        _base: &Ident,
        _version: u32,
        _kind: VersionOrigin,
    ) {
    }

    /// A lambda was lowered to the uninterpreted function `name`. `binders` are the lambda's
    /// parameters with their types and `body` is its body.
    fn on_lambda_decl(&mut self, _name: &Ident, _binders: &Binders<Typ>, _body: &Expr) {}

    /// A `choose` was lowered to the uninterpreted function `name`. `binders` are the bound
    /// variables with their types and `triggers` the choose's trigger groups. `predicate` is
    /// the condition the witness satisfies (the AIR `Choose` bind's condition, which also
    /// carries the binders' type invariants) and `body` is the expression the choose evaluates
    /// to under that witness.
    fn on_choose_decl(
        &mut self,
        _name: &Ident,
        _binders: &Binders<Typ>,
        _triggers: &Triggers,
        _predicate: &Expr,
        _body: &Expr,
    ) {
    }

    /// An axiom declaration was processed (for accumulating function definitions).
    fn on_axiom_decl(&mut self, _expr: &Expr) {}

    fn as_any(&self) -> &dyn Any;
    fn as_any_mut(&mut self) -> &mut dyn Any;
}
