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
use rustc_middle::ty::Ty;
use rustc_span::Span;
use std::sync::Arc;
use vir::ast::{
    BinaryOp, Expr, ExprX, LocalOrTemp, Mode, Place, PlaceX, Stmt, StmtX, VarIdent, VirErr,
};
use vir::ast_util::unit_typ;

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

/// The operands of an `ExprX::Call` or `ExprX::Ctor` node that is being translated
/// (see `begin_operands`)
pub(crate) struct Operands {
    /// The scope of the HIR expression for the call or constructor
    scope: Scope,
    /// The span (and AstId) for the VIR node
    span: vir::messages::Span,
}

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
    /// Panics if the scope isn't on the stack.
    fn schedule_drop(&self, scope: Scope, local_or_temp: LocalOrTemp, span: Span, ty: Ty<'tcx>) {
        if !self.emits_drops() || !self.ty_needs_drop(ty) {
            return;
        }
        let mut drop_scopes = self.drop_scopes.borrow_mut();
        if let Some(ds) = drop_scopes.scopes.iter_mut().rev().find(|ds| ds.scope == scope) {
            ds.drops.push((local_or_temp, span));
            return;
        }
        panic!("Verus Internal Error: schedule_drop failed to find scope {:?}", scope);
    }

    /// Schedule a drop for a temporary created from `expr`
    /// (where `place` is the `PlaceX::Temporary` node).
    /// The temporary is dropped at the end of `expr`'s temporary scope,
    /// which may be extended by temporary lifetime extension.
    pub(crate) fn schedule_temp_drop(
        &self,
        expr: &rustc_hir::Expr<'tcx>,
        place: &Place,
        ty: Ty<'tcx>,
    ) {
        if !self.emits_drops() || !self.ty_needs_drop(ty) {
            return;
        }
        assert!(matches!(place.x, PlaceX::Temporary(_)));
        let temp_lifetime = self.scope_tree().temporary_scope(expr.hir_id.local_id);
        if let Some(scope) = temp_lifetime.temp_lifetime {
            self.schedule_drop(scope, LocalOrTemp::Temp(place.span.id), expr.span, ty);
        }
    }

    /// Schedule a drop for a local variable bound at the pattern with id `hir_id`.
    pub(crate) fn schedule_local_drop(
        &self,
        hir_id: HirId,
        var: &VarIdent,
        span: Span,
        ty: Ty<'tcx>,
    ) {
        if !self.emits_drops() || !self.ty_needs_drop(ty) {
            return;
        }
        if let Some(scope) = self.scope_tree().var_scope(hir_id.local_id) {
            self.schedule_drop(scope, LocalOrTemp::Local(var.clone()), span, ty);
        }
    }

    /// Does this type have drop glue?
    fn ty_needs_drop(&self, ty: Ty<'tcx>) -> bool {
        // Replace free vars with ReErased
        let ty = rustc_middle::ty::fold_regions(self.ctxt.tcx, ty, |region, debruijn| match region
            .kind()
        {
            rustc_middle::ty::RegionKind::ReEarlyParam(..) => self.ctxt.tcx.lifetimes.re_erased,
            rustc_middle::ty::RegionKind::ReBound(
                rustc_middle::ty::BoundVarIndexKind::Bound(d),
                _,
            ) if d == debruijn => self.ctxt.tcx.lifetimes.re_erased,
            _ => region,
        });
        let typing_env = rustc_middle::ty::TypingEnv::new(
            self.ctxt.tcx.param_env(self.fun_id),
            rustc_middle::ty::TypingMode::non_body_analysis(),
        );
        ty.needs_drop(self.ctxt.tcx, typing_env)
    }

    /// Begin translating the operands of the call or constructor `expr`
    /// (which will become a `ExprX::Call` or `ExprX::Ctor` node).
    ///
    /// Like rustc's MIR builder, after each by-value operand is evaluated, we schedule a drop of
    /// its temporary in the scope of `expr` (`schedule_operand_drop`). The call or constructor moves
    /// the operands out of their temporaries, so we unschedule these drops when all operands
    /// have been evaluated (`end_operands`). Thus the drops only appear on early exits
    /// from the later operands.
    pub(crate) fn begin_operands(&self, expr: &rustc_hir::Expr<'tcx>) -> Operands {
        Operands { scope: node_scope(expr.hir_id), span: self.ctxt.spans.to_air_span(expr.span) }
    }

    /// Schedule a drop of the temporary for operand number `idx`, which has just been evaluated
    pub(crate) fn schedule_operand_drop(
        &self,
        operands: &Operands,
        idx: usize,
        operand: &rustc_hir::Expr<'tcx>,
    ) {
        let ty = self.types.expr_ty_adjusted(operand);
        if !self.emits_drops() || !self.ty_needs_drop(ty) {
            return;
        }
        let lt = LocalOrTemp::CallArg(operands.span.id, idx);
        self.schedule_drop(operands.scope, lt, operand.span, ty);
    }

    /// All the operands have been evaluated, and the call or constructor moves them;
    /// unschedule their drops, and return the span to use for the VIR node.
    pub(crate) fn end_operands(&self, operands: Operands) -> vir::messages::Span {
        let mut drop_scopes = self.drop_scopes.borrow_mut();
        let Some(ds) = drop_scopes.scopes.iter_mut().rev().find(|ds| ds.scope == operands.scope)
        else {
            panic!("Verus Internal Error: end_operands failed to find scope {:?}", operands.scope);
        };
        let id = operands.span.id;
        ds.drops.retain(|(lt, _)| !matches!(lt, LocalOrTemp::CallArg(id2, _) if *id2 == id));
        operands.span
    }

    /// Translate the operands of the call or constructor `expr`, scheduling drops for them
    /// (see `begin_operands`), and build the VIR node from them with `mk`.
    pub(crate) fn operands_to_vir<T>(
        &self,
        expr: &rustc_hir::Expr<'tcx>,
        operands: &[&rustc_hir::Expr<'tcx>],
        mk: impl FnOnce(vir::messages::Span, Vec<Expr>) -> Result<T, VirErr>,
    ) -> Result<T, VirErr> {
        let ops = self.begin_operands(expr);
        let mut vir_operands = vec![];
        for (i, operand) in operands.iter().enumerate() {
            vir_operands.push(crate::rust_to_vir_expr::expr_to_vir_consume(self, operand)?);
            self.schedule_operand_drop(&ops, i, operand);
        }
        let span = self.end_operands(ops);
        mk(span, vir_operands)
    }

    /// Schedule a drop for a local variable in the given scope, which must be on the stack.
    /// (Used for function parameters.)
    pub(crate) fn schedule_local_drop_in(
        &self,
        scope: Scope,
        var: &VarIdent,
        span: Span,
        ty: Ty<'tcx>,
    ) {
        self.schedule_drop(scope, LocalOrTemp::Local(var.clone()), span, ty);
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
            panic!("drops_for_exit_to: cannot find scope");
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
    /// get the scope containing the condition and the then-branch.
    ///
    /// This is `IfThenRescope` in edition >= 2024, `IfThen` otherwise.
    /// (See `rustc_mir_build/src/thir/cx/expr.rs`)
    pub(crate) fn if_then_scope(&self, if_hir_expr: &rustc_hir::Expr<'tcx>) -> Scope {
        let rustc_hir::ExprKind::If(_, then, _) = &if_hir_expr.kind else { unreachable!() };
        let then_hir_id = then.hir_id;
        let then_scope = Scope {
            local_id: then_hir_id.local_id,
            data: {
                if if_hir_expr.span.at_least_rust_2024() {
                    ScopeData::IfThenRescope
                } else {
                    ScopeData::IfThen
                }
            },
        };

        // Confirm we made the right choice
        assert!(self.scope_tree().parent_map.contains_key(&then_scope));

        then_scope
    }
}

pub(crate) fn node_scope(hir_id: HirId) -> Scope {
    Scope { local_id: hir_id.local_id, data: ScopeData::Node }
}

pub(crate) fn drop_stmts(bctx: &BodyCtxt, drops: Vec<Expr>) -> Vec<Stmt> {
    drops.into_iter().map(|d| bctx.ctxt.spanned_new_vir(&d.span, StmtX::Expr(d.clone()))).collect()
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
    let right = if drops.len() == 1 {
        drops[0].clone()
    } else {
        let stmts = Arc::new(drop_stmts(bctx, drops));
        bctx.ctxt.spanned_typed_new_vir(
            &e.span,
            &vir::ast_util::unit_typ(),
            ExprX::Block(stmts, None),
        )
    };
    bctx.ctxt.spanned_typed_new_vir(
        &e.span,
        &e.typ,
        ExprX::Binary(BinaryOp::Left, e.clone(), right),
    )
}

pub(crate) fn block_with_drops(
    bctx: &BodyCtxt,
    span: &Span,
    stmts: Vec<Stmt>,
    e: Option<Expr>,
    drops: Vec<Expr>,
) -> Expr {
    let x = match &e {
        Some(e) => ExprX::Block(Arc::new(stmts), Some(append_drops(bctx, e.clone(), drops))),
        None => {
            let mut stmts = stmts;
            stmts.extend(drop_stmts(bctx, drops));
            ExprX::Block(Arc::new(stmts), None)
        }
    };
    let typ = match e {
        Some(e) => e.typ.clone(),
        None => unit_typ(),
    };
    bctx.spanned_typed_new(span.clone(), &typ, x)
}

/// Return an expression that executes the drops and then evaluates `e`.
pub(crate) fn prepend_drops(bctx: &BodyCtxt, drops: Vec<Expr>, e: Expr) -> Expr {
    if drops.len() == 0 {
        return e;
    }
    bctx.ctxt.spanned_typed_new_vir(
        &e.span,
        &e.typ,
        ExprX::Block(Arc::new(drop_stmts(bctx, drops)), Some(e.clone())),
    )
}
