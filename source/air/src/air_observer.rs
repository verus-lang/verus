//! AIR-level verification pipeline observer.
//!
//! Defines `AirObserver` — the interface for observing the AIR-level
//! verification pipeline: query lowering, WP version creation, and lambda /
//! choose / axiom declarations.
//!
//! This trait is independent: it does **not** require any other observer
//! trait. Query *results* are observed separately via `QueryResultObserver`
//! (`query_result_observer.rs`), and VIR→AIR lowering via `VirObserver`
//! (`vir/src/vir_observer.rs`). A consumer implements only the traits it needs.

use crate::ast::{Decl, Expr, Ident, Query, Snapshots};
use std::any::Any;

/// Origin of a WP versioned constant created during `lower_query`.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum VersionOrigin {
    /// From a `StmtX::Havoc` — unconstrained new version (loop entry).
    Havoc,
    /// From a `StmtX::Assign` — constrained new version (= rhs).
    Assign,
    /// Phantom version from Switch branch reconciliation.
    BranchMerge,
    /// Phantom version from Breakable break reconciliation.
    BreakMerge,
}

/// Observer for the AIR-level verification pipeline.
///
/// All methods have default no-op implementations except `as_any`
/// and `as_any_mut` which must be implemented (trivially: `self`).
pub trait AirObserver: Any {
    /// A verification query has been lowered (variables → versioned constants).
    fn on_query_lowered(&mut self, _query: &Query, _snapshots: &Snapshots, _local_vars: &[Decl]) {}

    /// Called from `lower_query` at the moment a new WP version is created.
    ///
    /// For `Havoc`/`Assign` origins, the Nth call for base variable `x`
    /// corresponds to the Nth VIR-level `on_havoc` or `on_assign` callback
    /// for `x`. For merge origins, the call corresponds to the most recent
    /// `on_branch_merge` or `on_break_merge` callback.
    ///
    /// See `VersionCorrelator` in `vir/src/vir_observer.rs` for a shared helper
    /// that correlates these callbacks with VIR-level data.
    fn on_wp_version_created(&mut self, _versioned: &Ident, _kind: VersionOrigin) {}

    /// A lambda definition was declared (%%lambda%%N).
    fn on_lambda_decl(&mut self, _name: &Ident, _params: &[Ident], _body: &Expr) {}

    /// A choose binder name was declared (%%choose%%N).
    fn on_choose_decl(&mut self, _name: &Ident, _binder_name: &Ident) {}

    /// An axiom declaration was processed (for accumulating function definitions).
    fn on_axiom_decl(&mut self, _expr: &Expr) {}

    fn as_any(&self) -> &dyn Any;
    fn as_any_mut(&mut self) -> &mut dyn Any;
}
