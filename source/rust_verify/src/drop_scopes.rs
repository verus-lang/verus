//! Tracking of rustc's drop scopes during HIR-to-VIR translation, for the purposes of
//! emitting `ExprX::Drop` nodes.
//!
//! We mirror the way that rustc's MIR builder (`rustc_mir_build::builder::scope`) handles scopes:
//!
//!  - The "region scope tree" (`tcx.region_scope_tree`) tells us, for each local variable, the
//!    scope it belongs to (`var_scope`), and for each expression that gets materialized into
//!    a temporary, the scope of that temporary (`temporary_scope`).
//!    These computations account for edition differences and temporary lifetime extension.
//!  - As we translate the HIR, we maintain a stack of the scopes we're currently inside,
//!    pushing a scope at the same places where the MIR builder would.
//!  - When a local or temporary comes into existence, we "schedule" its drop in the
//!    appropriate scope (which must be on the stack).
//!  - When we leave a scope, we emit all the drops scheduled in it, in reverse order.
//!  - When we exit scopes early (break, continue, return), we emit the drops for all the
//!    scopes being exited.
//!
//! See `drop-order-notes.md` for more details about Rust's rules.
//!
//! We only emit drops for exec code; drops are not emitted in spec or proof code.

use crate::context::BodyCtxt;
use rustc_hir::HirId;
use rustc_middle::middle::region::{Scope, ScopeData, ScopeTree};
use rustc_span::Span;
use std::sync::Arc;
use vir::ast::{Expr, ExprX, LocalOrTemp, Mode, Place, PlaceX, Stmt, StmtX, VarIdent, VirErr};
use vir::ast_util::unit_typ;
use vir::def::Spanned;

struct DropScope {
    scope: Scope,
    /// Drops in the order they were scheduled (the reverse of the order they execute in)
    drops: Vec<(LocalOrTemp, Span)>,
}

/// Stack of scopes, outermost to innermost, for the current function or closure body
#[derive(Default)]
pub(crate) struct DropScopes {
    scopes: Vec<DropScope>,
}

/// Scopes temporarily removed from the stack (see `suspend_drop_scopes_from`)
pub(crate) struct SuspendedDropScopes(Vec<DropScope>);

impl<'tcx> BodyCtxt<'tcx> {
    fn scope_tree(&self) -> &'tcx ScopeTree {
        self.ctxt.tcx.region_scope_tree(self.fun_id.expect_local())
    }

    fn emits_drops(&self) -> bool {
        self.mode == Mode::Exec && !self.in_ghost && !self.external_body && !self.in_fn_sig
    }

    fn mk_drop(&self, local_or_temp: &LocalOrTemp, span: Span) -> Expr {
        self.spanned_typed_new(span, &unit_typ(), ExprX::Drop(local_or_temp.clone()))
    }

    fn mk_drops(&self, drops: impl Iterator<Item = (LocalOrTemp, Span)>) -> Vec<Expr> {
        drops.map(|(lt, span)| self.mk_drop(&lt, span)).collect()
    }

    pub(crate) fn push_drop_scope(&self, scope: Scope) {
        self.drop_scopes.borrow_mut().scopes.push(DropScope { scope, drops: vec![] });
    }

    /// Pop the given scope (which must be on top of the stack) and return its drops,
    /// in the order they should execute.
    pub(crate) fn pop_drop_scope(&self, scope: Scope) -> Vec<Expr> {
        let s = self.drop_scopes.borrow_mut().scopes.pop().expect("pop_drop_scope");
        assert!(s.scope == scope, "pop_drop_scope: mismatched scope");
        self.mk_drops(s.drops.into_iter().rev())
    }

    /// Run `f` inside the given scope, then pop the scope and return its drops
    /// (in the order they should execute).
    pub(crate) fn in_drop_scope<R>(
        &self,
        scope: Scope,
        f: impl FnOnce() -> Result<R, VirErr>,
    ) -> Result<(R, Vec<Expr>), VirErr> {
        self.push_drop_scope(scope);
        let r = f();
        let drops = self.pop_drop_scope(scope);
        Ok((r?, drops))
    }

    /// Temporarily remove the given scope, and all scopes inside it, from the stack.
    /// This is used when we need to translate code that is lexically inside a scope,
    /// but which rustc treats as being outside it (e.g., the `else` block of a let-else).
    pub(crate) fn suspend_drop_scopes_from(&self, scope: Scope) -> SuspendedDropScopes {
        let mut drop_scopes = self.drop_scopes.borrow_mut();
        let Some(idx) = drop_scopes.scopes.iter().rposition(|ds| ds.scope == scope) else {
            panic!("Verus Internal Error: suspend_drop_scopes_from failed to find scope");
        };
        SuspendedDropScopes(drop_scopes.scopes.split_off(idx))
    }

    pub(crate) fn resume_drop_scopes(&self, suspended: SuspendedDropScopes) {
        self.drop_scopes.borrow_mut().scopes.extend(suspended.0);
    }

    /// Run `f` with a fresh scope stack (used for closure bodies)
    pub(crate) fn with_fresh_drop_scopes<R>(&self, f: impl FnOnce() -> R) -> R {
        let saved = std::mem::take(&mut *self.drop_scopes.borrow_mut());
        let r = f();
        let inner = std::mem::replace(&mut *self.drop_scopes.borrow_mut(), saved);
        assert!(inner.scopes.len() == 0);
        r
    }

    /// Schedule the drop in the given scope.
    /// If the scope isn't on the stack, use the nearest enclosing scope that is.
    /// (This can happen if we translate some HIR construct without traversing every
    /// HIR node in it; in most cases, the skipped HIR nodes don't have any drops.)
    fn schedule_drop(&self, scope: Scope, local_or_temp: LocalOrTemp, span: Span) {
        if !self.emits_drops() {
            return;
        }
        let scope_tree = self.scope_tree();
        let mut drop_scopes = self.drop_scopes.borrow_mut();
        let mut scope = Some(scope);
        while let Some(s) = scope {
            if let Some(ds) = drop_scopes.scopes.iter_mut().rev().find(|ds| ds.scope == s) {
                ds.drops.push((local_or_temp, span));
                return;
            }
            scope = scope_tree.opt_encl_scope(s);
        }
        // We didn't find any enclosing scope; this might happen, e.g., for a temporary
        // extended to the end of the function body. In that case, we do nothing.
    }

    /// Schedule a drop for a temporary created from `expr`
    /// (where `place` is the `PlaceX::Temporary` node).
    /// The temporary is dropped at the end of `expr`'s temporary scope,
    /// which may be extended by temporary lifetime extension.
    pub(crate) fn schedule_temp_drop(&self, expr: &rustc_hir::Expr<'tcx>, place: &Place) {
        if !self.emits_drops() {
            return;
        }
        assert!(matches!(place.x, PlaceX::Temporary(_)));
        let temp_lifetime = self.scope_tree().temporary_scope(expr.hir_id.local_id);
        if let Some(scope) = temp_lifetime.temp_lifetime {
            self.schedule_drop(scope, LocalOrTemp::Temp(place.span.id), expr.span);
        }
    }

    /// Schedule a drop for a local variable bound at the pattern with id `hir_id`.
    pub(crate) fn schedule_local_drop(&self, hir_id: HirId, var: &VarIdent, span: Span) {
        if !self.emits_drops() {
            return;
        }
        if let Some(scope) = self.scope_tree().var_scope(hir_id.local_id) {
            self.schedule_drop(scope, LocalOrTemp::Local(var.clone()), span);
        }
    }

    /// Schedule a drop for a local variable in the given scope, which must be on the stack.
    /// (Used for function parameters.)
    pub(crate) fn schedule_local_drop_in(&self, scope: Scope, var: &VarIdent, span: Span) {
        self.schedule_drop(scope, LocalOrTemp::Local(var.clone()), span);
    }

    /// All drops currently scheduled in scopes strictly inside the scope of the given
    /// HIR node (in the order they should execute).
    /// This is used for `break` and `continue`, where `hir_id` is the loop.
    pub(crate) fn drops_for_exit_to(&self, hir_id: HirId) -> Vec<Expr> {
        let target = Scope { local_id: hir_id.local_id, data: ScopeData::Node };
        let drop_scopes = self.drop_scopes.borrow();
        let Some(idx) = drop_scopes.scopes.iter().rposition(|ds| ds.scope == target) else {
            // This shouldn't happen, since we always enter the scope of a loop
            // before translating its body
            return vec![];
        };
        self.mk_drops(
            drop_scopes.scopes[idx + 1..]
                .iter()
                .rev()
                .flat_map(|ds| ds.drops.iter().rev().cloned()),
        )
    }

    /// All drops currently scheduled in all scopes of the function or closure body
    /// (in the order they should execute).
    /// This is used for `return`.
    pub(crate) fn drops_for_return(&self) -> Vec<Expr> {
        let drop_scopes = self.drop_scopes.borrow();
        self.mk_drops(drop_scopes.scopes.iter().rev().flat_map(|ds| ds.drops.iter().rev().cloned()))
    }

    /// All drops currently scheduled in the given scope and all scopes inside it
    /// (in the order they should execute).
    /// The scope must be on the stack.
    pub(crate) fn drops_for_exit_from(&self, scope: Scope) -> Vec<Expr> {
        let drop_scopes = self.drop_scopes.borrow();
        let Some(idx) = drop_scopes.scopes.iter().rposition(|ds| ds.scope == scope) else {
            panic!("Verus Internal Error: drops_for_exit_from failed to find scope");
        };
        self.mk_drops(
            drop_scopes.scopes[idx..].iter().rev().flat_map(|ds| ds.drops.iter().rev().cloned()),
        )
    }

    /// For the `if` expression whose then-branch has the given HirId,
    /// the scope containing the condition and the then-branch
    /// (`IfThenRescope` in edition 2024 and later, `IfThen` otherwise).
    pub(crate) fn if_then_scope(&self, then_hir_id: HirId) -> Scope {
        let local_id = then_hir_id.local_id;
        let rescope = Scope { local_id, data: ScopeData::IfThenRescope };
        if self.scope_tree().parent_map.contains_key(&rescope) {
            rescope
        } else {
            Scope { local_id, data: ScopeData::IfThen }
        }
    }
}

pub(crate) fn node_scope(hir_id: HirId) -> Scope {
    Scope { local_id: hir_id.local_id, data: ScopeData::Node }
}

pub(crate) fn drop_stmts(bctx: &BodyCtxt, drops: Vec<Expr>) -> Vec<Stmt> {
    drops
        .into_iter()
        .map(|d| {
            // The statement needs its own AstId
            let mut span = d.span.clone();
            span.id = bctx.ctxt.spans.get_next_span_id();
            Spanned::new(span, StmtX::Expr(d))
        })
        .collect()
}

/// Return an expression that evaluates `e` and then executes the drops.
/// If `e` is a block, we just append the drops to the block's drops; this way,
/// we don't disturb any code that looks for a block in a specific place (e.g., for headers).
/// For the same reason, we look through the same nodes that `vir::headers::read_header`
/// looks through (which come from implicit adjustments).
pub(crate) fn append_drops(bctx: &BodyCtxt, e: Expr, drops: Vec<Expr>) -> Expr {
    if drops.len() == 0 {
        return e;
    }
    match append_drops_to_block(&e, &drops) {
        Some(e) => e,
        None => bctx.ctxt.spanned_typed_new_vir(
            &e.span,
            &e.typ,
            ExprX::Block(Arc::new(vec![]), Some(e.clone()), Arc::new(drops)),
        ),
    }
}

fn drops_temp(drops: &Vec<Expr>, place: &Place) -> bool {
    drops.iter().any(|d| matches!(&d.x, ExprX::Drop(LocalOrTemp::Temp(id)) if *id == place.span.id))
}

fn append_drops_to_block(e: &Expr, drops: &Vec<Expr>) -> Option<Expr> {
    match &e.x {
        ExprX::Block(stmts, tail, drops0) => {
            let mut all_drops = (**drops0).clone();
            all_drops.extend(drops.iter().cloned());
            Some(e.new_x(ExprX::Block(stmts.clone(), tail.clone(), Arc::new(all_drops))))
        }
        // If `e1` never returns, then neither of these orderings execute the drops:
        ExprX::NeverToAny(e1) => {
            Some(e.new_x(ExprX::NeverToAny(append_drops_to_block(e1, drops)?)))
        }
        // The drops can't affect the value already stored in the temporary,
        // so it's equivalent to execute the drops before reading the temporary
        // (as long as we aren't dropping the temporary itself):
        ExprX::ReadPlace(place, rk) => match &place.x {
            PlaceX::Temporary(e1) if !drops_temp(drops, place) => {
                let e1 = append_drops_to_block(e1, drops)?;
                Some(e.new_x(ExprX::ReadPlace(place.new_x(PlaceX::Temporary(e1)), *rk)))
            }
            _ => None,
        },
        ExprX::ImplicitReborrowOrSpecRead(place, b, span) => match &place.x {
            PlaceX::Temporary(e1) if !drops_temp(drops, place) => {
                let e1 = append_drops_to_block(e1, drops)?;
                let place = place.new_x(PlaceX::Temporary(e1));
                Some(e.new_x(ExprX::ImplicitReborrowOrSpecRead(place, *b, span.clone())))
            }
            _ => None,
        },
        _ => None,
    }
}

/// Return an expression that executes the drops and then evaluates `e`.
pub(crate) fn prepend_drops(bctx: &BodyCtxt, e: Expr, drops: Vec<Expr>) -> Expr {
    if drops.len() == 0 {
        return e;
    }
    bctx.ctxt.spanned_typed_new_vir(
        &e.span,
        &e.typ,
        ExprX::Block(Arc::new(drop_stmts(bctx, drops)), Some(e.clone()), Arc::new(vec![])),
    )
}
