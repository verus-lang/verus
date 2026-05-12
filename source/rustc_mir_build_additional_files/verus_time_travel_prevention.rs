/*!
The main point of transformation in this file is to prevent prophetic "paradoxes" that arise
from taking a spec snapshot of a variable while it is mutably borrowed.

```rust
let mut x = 0;
let x_ref = &mut x;

let ghost x_snapshot = x;

*x_ref = 20;
```

Taking such a snapshot would be prophetic, but Verus mode-checking (modes.rs) assumes by default
that uses of a local variable are non-prophetic. Thus, for soundness reasons, we need to disallow
code like the above, unless `x` is specifically used in a way that indicates it is prophetic.

Besides soundness issues, it's also a usability issue. It's perfectly sound to use a prophetic
variable in an assert (in general, it's fine for safety conditions), for example,

```rust
let mut x = 0;
let x_ref = &mut x;

assert(x == 0); // this check would fail; that might be confusing

*x_ref = 20;
```

But the behavior would be pretty confusing, so this is also disallowed (again, unless it's
used in a way that indicates propheticness is intentional).

To implement this restriction, we essentially need to "partially borrow check" all spec code.
Note that we still to opt-out of other borrowck restrictions (e.g. we want to be able to
take spec snapshots of moved variables).
Specifically, we want to check that certain spec uses do not reference data which is currently
_mutably_ borrowed.

# The transformation

At a high-level, the key idea is that for any (non-ghost) variable `x`, we introduce a secondary
variable, "the shadow variable", `x_shadow` which represents the ability to take a non-prophetic
spec snapshot.  The variable `x_shadow` will always be initialized, and never moved-from,
only borrowed-from.

When `x` is declared, we insert a declaration of `x_shadow`:

```rust
let x: T = ...;                               // Existing line
let x_shadow = arbitrary_ghost_value::<T>();  // Added by our transformation
```

Next, whenever `x` appears in spec code, if it requires this special checking, we replace
the usage with a borrow of x_shadow: `&x_shadow`.
For the sake of this file, we can assume that it's already determined _which_ spec variables
need this extra checking, specifically, any variable usage whose erasure mode is set to
`VarErasure::Shadow` needs this special checking.

Finally, whenever we take a mutable reference from `x`, we also "tie" the lifetime together:
`&mut x` becomes `mutable_reference_tie(&mut x, &mut x_shadow)` where
`mutable_reference_tie<'a, T, U>(&'a mut T, &'a mut U) -> &'a mut T`.
This has the effect of forcing `x_shadow` to be mutably-borrowed as long as `x` is borrowed,
but won't have any other effect on lifetime checking.

More generally,
`&mut place` becomes `mutable_reference_tie(&mut place, &mut place_shadow)` where
`place` is any place expression (like `x.field`) and `place_shadow` is the corresponding
place in the shadow variable (like `x_shadow.field`).

# Details

There are a lot of different cases to consider, accounting for all the ways mutable references
can actually be declared.

### Two-phase borrows

Two-phase borrows pose an additional challenge. Imagine we expanded:

```
f(&mut[two_phase] x, y)
```

to:

```
f(mutable_reference_tie(&mut[two_phase] x, &mut x_shadow), y)
```

The problem is that the scope of the first phase of two-phase borrow only extends through to the
artificial `mutable_reference_tie` call (i.e., before the evaluation of `y`) whereas we need
it to go all the way to the `f` call (i.e., after the evaluation of `y`).

To my knowledge, extending the two-phase borrow in this way isn't expressible in THIR.
Therefore, this requires us to also modify the THIR->MIR conversion. First, we use
a different identifier for the "tie" function so that the case is recognizable.

```
f(two_phase_mutable_reference_tie(&mut[two_phase] x, &mut x_shadow), y)
```

Then we modify the MIR builder to look for `two_phase_mutable_reference_tie` calls and modify
the evaluation order correspondingly. In the above case, the evalution order would be:

 - `tmp1 = &mut[two_phase x]`
 - `tmp2 = &mut[two_phase x_shadow]`
 - `arg2 = y`
 - `arg1 = two_phase_mutable_reference_tie(tmp1, tmp2)`
 - `f(arg1, arg2)`

### Patterns

It's possible to create mutable references via patterns, e.g.:

```rust
let (ref mut x, y) = place;
```

Again, we need to do a mutable borrow from the corresponding shadow place. We translate
the above like this:

```rust
let (ref mut x_half1, y) = place;
let (ref mut x_half2, _) = shadow_place;
// For each binder with a `ref mut` binding in the pattern:
let x = mutable_reference_tie(x_half1, x_half2);
// Binders for shadow vars of the newly declared vars:
let x_shadow = arbitrary_ghost_value();
let y_shadow = arbitrary_ghost_value();
```

We call these the "half patterns".

And of course we need to apply this principle to anywhere a pattern can appear:
match, let, let-else, let expression (like in an if-let).

### Assignments

When assigning to `x`, we also need to assign to `x_shadow`:

```rust
x = ...;                                  // Existing line
x_shadow = arbitrary_ghost_value::<T>();  // Added by our transformation
```

This is needed to make Rust always considers `x` and `x_shadow` to have the exact same
set of outstanding borrows.
This is relevant in a situation that reborrows from a mutable
reference and then overwrites that reference:

```rust
let mut x_ref = &mut a;
let mut reborrow = &mut *x_ref;
x_ref = &mut b;
let mut reborrow2 = &mut *x_ref;

*reborrow = 0;   // extends lifetime from `&mut a`
*reborrow2 = 0;  // extends lifetime from `&mut b`
```

Without the assignment, we would have `*x_ref` borrowed twice at the same time;
but _with_ the assignment, the two mutable references `&mut *x_ref` don't intersect.
Thus, the assignment line is load-bearing for Rust to accept this code, so it needs
to be replicated for the shadow var.

### Closures

Inside a closure, we don't emit shadow vars for captured vars. Instead, those are
emitted by the enclosing fn/closure at the point the closure is created.
This is handled with the rest of closure-handling, in verus.rs.

### Pattern guards

When a variable is bound by a pattern with a guard, that variable is in-scope during the guard,
but it cannot be mutably borrowed from. Therefore, we do not need to bind a shadow variable
during a guard.

```rust
match m {
    x if ({
        // guard expression
        // don't need to bound any shadow variables here or perform shadow transformations
        // related to `x`
    }) => ({
        let x_shadow = ...; // bind shadow variables here
    })
}
```

### Loops

Loops make for an additional complication because the way they are encoded in Verus source / HIR
does not correspond to their conceptual "evaluation" points, e.g., a while-loop would be desugared
as thus:

```rust
loop {
    if cond() {
        ::verus_builtin::invariant(...);
        body;
    } else {
        break;
    }
}
```

when the conceptual evaluation point of the `invariant` is at the beginning/end of the loop.
Same issue for `invariant_except_break` / `ensures` / `decreases`
(and remember that the prophecy check is essential for soundness when it comes to decreases).

To resolve this, we have to handle all loop headers specially. First, we simply ignore them
when we encounter them during the main traversal (they should be marked EraseAbsolutely).
Then, when handling the Loop node itself, we insert the headers' shadow usages at the
appropriate program points.
*/

use crate::rustc_index::Idx;
use crate::thir::cx::ThirBuildCx;
use crate::verus::{LocalUse, expr_id_from_kind};
use crate::verus::{
    LoopSpecEvaluationLocation, TreeErase, VarErasure, VerusErasureCtxt, erase_tree_kind,
    erased_ghost_value, erased_ghost_value_kind_with_args, shadow_ghost_value_kind_with_args,
};
use rustc_hir as hir;
use rustc_hir::def_id::LocalDefId;
use rustc_hir::{BindingMode, ByRef, HirId, Mutability, Pinnedness};
use rustc_middle::middle::region;
use rustc_middle::mir::{BorrowKind, MutBorrowKind};
use rustc_middle::thir::{
    Arm, ArmId, Block, BlockSafety, Expr, ExprId, ExprKind, LocalVarId, LogicalOp, Pat, PatKind,
    Stmt, StmtId, StmtKind, Thir,
};
use rustc_middle::ty::{GenericArg, Region, RegionKind, Ty, TyCtxt, TyKind};
use rustc_span::Span;
use rustc_span::Symbol;

/// Post-process any THIR expression to apply the relevant transformation.
/// (This might apply to any an expression that results from an adjustment.)
pub(crate) fn expr_post<'tcx>(
    cx: &mut ThirBuildCx<'tcx>,
    hir_expr: &'tcx hir::Expr<'tcx>,
    ty: Ty<'tcx>,
    kind: rustc_middle::thir::ExprKind<'tcx>,
) -> rustc_middle::thir::ExprKind<'tcx> {
    if !cx.verus_ctxt.do_time_travel_prevention {
        return kind;
    }

    match &kind {
        ExprKind::Borrow { borrow_kind: BorrowKind::Mut { kind: borrow_kind_mut }, arg: _ } => {
            let two_phase = match borrow_kind_mut {
                MutBorrowKind::Default | MutBorrowKind::ClosureCapture => false,
                MutBorrowKind::TwoPhaseBorrow => true,
            };
            // Turn `&mut place` into
            // `&mut mutable_reference_tie(&mut place, &mut shadow_place)`
            // If the place is a temporary, we don't need to do the transformation.
            let shadow = shadow_mut_ref_kind(cx, hir_expr.hir_id, hir_expr.span, kind.clone());
            match shadow {
                None => kind,
                Some(shadow_kind) => {
                    let main_expr = expr_id_from_kind(cx, kind, hir_expr.hir_id, hir_expr.span, ty);
                    let shadow_expr =
                        expr_id_from_kind(cx, shadow_kind, hir_expr.hir_id, hir_expr.span, ty);
                    tie_mut_refs(
                        cx,
                        hir_expr.hir_id,
                        hir_expr.span,
                        main_expr,
                        shadow_expr,
                        two_phase,
                    )
                }
            }
        }
        ExprKind::Assign { lhs, rhs } => {
            // Turn `x = expr` into
            // `{ x = expr; x_shadow = erased_ghost_value(); }`
            //
            // Note: We don't need to handle AssignOp because it only applies to primitive types.
            let lhs = *lhs;
            let rhs = *rhs;
            if let Some(shadow_lhs) = shadow_place(cx, hir_expr.hir_id, hir_expr.span, lhs) {
                let main_assign = expr_id_from_kind(cx, kind, hir_expr.hir_id, hir_expr.span, ty);
                let rhs_ty = cx.thir.exprs[rhs].ty;
                let erasure_ctxt = cx.verus_ctxt.ctxt.clone().unwrap();
                let shadow_rhs =
                    erased_ghost_value(cx, &erasure_ctxt, hir_expr.hir_id, hir_expr.span, rhs_ty);
                let shadow_assign = expr_id_from_kind(
                    cx,
                    ExprKind::Assign { lhs: shadow_lhs, rhs: shadow_rhs },
                    hir_expr.hir_id,
                    hir_expr.span,
                    ty,
                );
                sequence_2_unit_exprs(cx, &erasure_ctxt, hir_expr, main_assign, shadow_assign)
            } else {
                kind
            }
        }
        ExprKind::Match { arms, scrutinee, match_source } => {
            let mut new_arms = vec![];
            for arm_id in arms.iter() {
                new_arms.push(arm_post(cx, hir_expr, *arm_id, *scrutinee));
            }
            ExprKind::Match {
                arms: new_arms.into_boxed_slice(),
                scrutinee: *scrutinee,
                match_source: *match_source,
            }
        }
        ExprKind::Let { .. } => expr_let_post(cx, hir_expr, kind),
        ExprKind::LoopMatch { .. } => {
            panic!("Verus Internal Error: LoopMatch not supported");
        }
        ExprKind::Loop { .. } => loop_post(cx, hir_expr, ty, kind),
        _ => kind,
    }
}

/// Post-process the top-level body expression of the function.
/// This is just declaring the shadow vars for the parameters.
pub(crate) fn body_post<'tcx>(
    cx: &mut ThirBuildCx<'tcx>,
    hir_body: &hir::Expr<'tcx>,
    body_id: ExprId,
) -> ExprId {
    if !cx.verus_ctxt.do_time_travel_prevention {
        return body_id;
    }
    let erasure_ctxt = cx.verus_ctxt.ctxt.clone().unwrap();

    let mut bindings = vec![];
    for param in cx.thir.params.iter() {
        if let Some(pat) = &param.pat {
            bindings.push(pattern_bindings(&pat));
        }
    }
    let bindings = bindings.iter().flatten().collect::<Vec<_>>();

    if bindings.len() == 0 {
        return body_id;
    }

    if bindings.iter().any(|b| b.ref_mut) {
        // This shouldn't happen because Verus doesn't support patterns-in-params
        panic!("Verus does not support param binding with ref mut binding");
    }

    let scope = region::Scope { local_id: hir_body.hir_id.local_id, data: region::ScopeData::Node };

    let mut stmts = vec![];
    for binding in bindings.iter() {
        stmts.push(make_shadow_decl(cx, &erasure_ctxt, hir_body.hir_id, binding, scope));
    }

    let block = Block {
        targeted_by_break: false,
        region_scope: scope,
        span: hir_body.span,
        stmts: stmts.into_boxed_slice(),
        expr: Some(body_id),
        safety_mode: BlockSafety::Safe,
    };
    let block_id = cx.thir.blocks.push(block);
    expr_id_from_kind(
        cx,
        ExprKind::Block { block: block_id },
        hir_body.hir_id,
        hir_body.span,
        cx.thir.exprs[body_id].ty,
    )
}

/// Post-process the given statement. This is only nontrivial for `let` statements.
/// This executes the "half pattern" transformation (if necessary) and declares any shadow vars.
///
/// Dealing with else-blocks isn't much trouble because nothing gets bound in the else case.
pub(crate) fn expand_stmt<'tcx>(
    cx: &mut ThirBuildCx<'tcx>,
    hir_stmt: &hir::Stmt<'tcx>,
    stmt: StmtId,
    block_id: hir::ItemLocalId,
    index: usize,
) -> Vec<StmtId> {
    if !cx.verus_ctxt.do_time_travel_prevention {
        return vec![stmt];
    }
    let erasure_ctxt = cx.verus_ctxt.ctxt.clone().unwrap();

    // The index in the scope here is with reference to the HIR; we don't need to adjust
    // the index for the inserted expressions or anything.
    let scope = region::Scope {
        local_id: block_id,
        data: region::ScopeData::Remainder(region::FirstStatementIndex::new(index)),
    };

    let StmtKind::Let { ref pattern, initializer, else_block, .. } = cx.thir.stmts[stmt].kind
    else {
        return vec![stmt];
    };

    let bindings = pattern_bindings(pattern);

    let mut stmts = vec![stmt];

    // 'Half pattern' transformation
    if let Some(rhs) = initializer
        && bindings.iter().any(|b| b.ref_mut)
        && let Some(shadow_rhs) = shadow_place(cx, hir_stmt.hir_id, hir_stmt.span, rhs)
    {
        let StmtKind::Let { ref pattern, span, .. } = cx.thir.stmts[stmt].kind else {
            unreachable!()
        };
        let pat1 = make_half_pat(pattern.clone(), Half::Normal);
        let pat2 = make_half_pat(pattern.clone(), Half::Shadow);

        let new_stmt = stmt_update_pat(cx, stmt, pat1);
        stmts = vec![new_stmt];

        stmts.push(make_half_decl(
            cx,
            &erasure_ctxt,
            hir_stmt.hir_id,
            span,
            pat2,
            shadow_rhs,
            else_block.is_some(),
            scope,
        ));
        for binding in bindings.iter() {
            if binding.ref_mut {
                stmts.push(make_tie_halves_decl(cx, hir_stmt.hir_id, binding, scope));
            }
        }
    }

    // Shadow var decls
    for binding in bindings.iter() {
        stmts.push(make_shadow_decl(cx, &erasure_ctxt, hir_stmt.hir_id, binding, scope));
    }

    stmts
}

/// Post-process a let-expression. Similar to statements but for let-expressions.
/// Let-expressions are composed with `&&` instead of `;`, e.g.:
///
/// `let (ref mut x_half1, y) = place` expression becomes:
///
/// ```rust
///      let (ref mut x_half1, y) = place
///   && let (ref mut x_half2, _) = shadow_place;
///   && let x = mutable_reference_tie(x_half1, x_half2);
///   && let x_shadow = arbitrary_ghost_value();
///   && let y_shadow = arbitrary_ghost_value();
/// ```
///
/// We need to be careful about refutability issues. Rust always adds an extra edge for
/// the match-failure cases of a let expression. (This even includes let expressions
/// where the pattern is actually refutable, e.g., our
/// `let x_shadow = arbitrary_ghost_value()` line.)
///
/// This can cause problems in a scenario like:
///
/// ```rust
/// fn test_if_let_move(s: Option<String>) {
///     if let Some(a) = s {
///         let t1 = a;
///     } else {
///         let t2 = s;
///     }
/// }
/// ```
///
/// Here, the extra clauses added by our translation create extra CFG edges, which means
/// that we do a move out of `s` and then reach the else-block (which wouldn't be the case
/// if this were translated normally).
///
/// To deal with this, we *also* modify the THIR->MIR lowering to skip this extra edge
/// for any Let expression that we determine to be the result of our half-pattern translation.
/// See `let_expr_treat_as_irrefutable`.
fn expr_let_post<'tcx>(
    cx: &mut ThirBuildCx<'tcx>,
    hir_expr: &hir::Expr<'tcx>,
    kind: ExprKind<'tcx>,
) -> ExprKind<'tcx> {
    let erasure_ctxt = cx.verus_ctxt.ctxt.clone().unwrap();

    let ExprKind::Let { ref pat, expr: rhs } = kind else { panic!("expr_let_post") };

    let bindings = pattern_bindings(pat);
    if bindings.len() == 0 {
        return kind;
    }

    let mut let_exprs = vec![];

    if bindings.iter().any(|b| b.ref_mut)
        && let Some(shadow_rhs) = shadow_place(cx, hir_expr.hir_id, hir_expr.span, rhs)
    {
        let mut kind = kind;
        let ExprKind::Let { ref mut pat, .. } = kind else { unreachable!() };

        let pat1 = make_half_pat(pat.clone(), Half::Normal);
        let pat2 = make_half_pat(pat.clone(), Half::Shadow);

        *pat = pat1;
        let_exprs.push(expr_id_from_kind(
            cx,
            kind,
            hir_expr.hir_id,
            hir_expr.span,
            cx.tcx.mk_ty_from_kind(TyKind::Bool),
        ));

        let_exprs.push(make_half_let_expr(
            cx,
            &erasure_ctxt,
            hir_expr.hir_id,
            hir_expr.span,
            pat2,
            shadow_rhs,
        ));
        for binding in bindings.iter() {
            if binding.ref_mut {
                let_exprs.push(make_tie_halves_let_expr(cx, hir_expr.hir_id, binding));
            }
        }
    } else {
        let_exprs.push(expr_id_from_kind(
            cx,
            kind,
            hir_expr.hir_id,
            hir_expr.span,
            cx.tcx.mk_ty_from_kind(TyKind::Bool),
        ));
    }

    for binding in bindings.iter() {
        let_exprs.push(make_shadow_let_expr(cx, &erasure_ctxt, hir_expr.hir_id, binding));
    }

    conjoin_exprs(cx, &let_exprs, hir_expr.hir_id, hir_expr.span)
}

/// Returns true if this is one of our inserted LetExprs which should be treated
/// as irrefutable.
pub(crate) fn let_expr_treat_as_irrefutable<'tcx>(
    tcx: TyCtxt<'tcx>,
    thir: &Thir<'tcx>,
    local_def_id: LocalDefId,
    pat: &Pat<'tcx>,
    expr_id: ExprId,
) -> bool {
    let Some(erasure_ctxt) = crate::verus::get_verus_erasure_ctxt_option() else {
        return false;
    };

    let enclosing_def_id = crate::verus::enclosing_fn_local_def_id(tcx, local_def_id);

    // This will catch either:
    // `let (ref mut x_half2, _) = shadow_place`
    // or:
    // `let x_shadow = arbitrary_ghost_value()`
    if pat_has_shadow(enclosing_def_id, pat) {
        return true;
    }

    // This will catch:
    // let x = mutable_reference_tie(x_half1, x_half2)
    match &thir.exprs[expr_id].kind {
        ExprKind::Call { fun, args, .. } => match thir.exprs[*fun].ty.kind() {
            TyKind::FnDef(fn_def_id, _)
                if *fn_def_id == erasure_ctxt.mutable_reference_tie_fn_def_id =>
            {
                assert!(args.len() == 2);
                match &thir.exprs[args[1]].kind {
                    ExprKind::VarRef { id } => is_half_var_id(enclosing_def_id, *id, Half::Shadow),
                    _ => false,
                }
            }
            _ => false,
        },
        _ => false,
    }
}

/// Does the pat contain a `x_shadow` var or `x_half2` var?
fn pat_has_shadow<'tcx>(enclosing_def_id: LocalDefId, pat: &Pat<'tcx>) -> bool {
    match &pat.kind {
        PatKind::Missing => false,
        PatKind::Wild => false,
        PatKind::Binding {
            name: _,
            mode: _,
            var,
            ty: _,
            subpattern,
            is_primary: _,
            is_shorthand: _,
        } => {
            if is_half_var_id(enclosing_def_id, *var, Half::Shadow) {
                return true;
            }
            if is_shadow_var_id(enclosing_def_id, *var) {
                return true;
            }
            if let Some(subpat) = subpattern {
                if pat_has_shadow(enclosing_def_id, subpat) {
                    return true;
                }
            }
            false
        }
        PatKind::Variant { adt_def: _, args: _, variant_index: _, subpatterns }
        | PatKind::Leaf { subpatterns } => {
            for field_pat in subpatterns.iter() {
                if pat_has_shadow(enclosing_def_id, &field_pat.pattern) {
                    return true;
                }
            }
            false
        }

        PatKind::Deref { subpattern, pin: _ } => pat_has_shadow(enclosing_def_id, subpattern),
        PatKind::DerefPattern { subpattern, borrow: _ } => {
            pat_has_shadow(enclosing_def_id, subpattern)
        }
        PatKind::Constant { value: _ } => false,
        PatKind::Range(_pat_range) => false,
        PatKind::Slice { prefix, slice, suffix } | PatKind::Array { prefix, slice, suffix } => {
            for p in prefix.iter() {
                if pat_has_shadow(enclosing_def_id, p) {
                    return true;
                }
            }
            if let Some(sl) = slice {
                if pat_has_shadow(enclosing_def_id, sl) {
                    return true;
                }
            }
            for p in suffix.iter() {
                if pat_has_shadow(enclosing_def_id, p) {
                    return true;
                }
            }
            false
        }
        PatKind::Or { pats } => {
            for pat in pats.iter() {
                if pat_has_shadow(enclosing_def_id, pat) {
                    return true;
                }
            }
            false
        }
        PatKind::Never => false,
        PatKind::Error(_error_guaranteed) => false,
    }
}

/// Translate the given arm with the 'half pattern' transformation. The arm's pattern is
/// adjusted in-place, and the extra decls are added into the arm body.
///
/// Note: right now Verus doesn't support 'ref mut' bindings together with guard patterns.
/// If that were supported, this would need some more consideration.
fn arm_post<'tcx>(
    cx: &mut ThirBuildCx<'tcx>,
    hir_match: &hir::Expr<'tcx>,
    arm_id: ArmId,
    scrutinee: ExprId,
) -> ArmId {
    let erasure_ctxt = cx.verus_ctxt.ctxt.clone().unwrap();

    let arm = &cx.thir.arms[arm_id];
    let bindings = pattern_bindings(&arm.pattern);
    if bindings.len() == 0 {
        return arm_id;
    }
    let scope = arm.scope;

    let mut stmts = vec![];
    let mut pat = arm.pattern.clone();

    if bindings.iter().any(|b| b.ref_mut)
        && let Some(shadow_scrutinee) =
            shadow_place(cx, hir_match.hir_id, hir_match.span, scrutinee)
    {
        let pat1 = make_half_pat(pat.clone(), Half::Normal);
        let pat2 = make_half_pat(pat, Half::Shadow);

        pat = pat1;

        stmts.push(make_half_decl(
            cx,
            &erasure_ctxt,
            hir_match.hir_id,
            hir_match.span,
            pat2,
            shadow_scrutinee,
            true,
            scope,
        ));
        for binding in bindings.iter() {
            if binding.ref_mut {
                stmts.push(make_tie_halves_decl(cx, hir_match.hir_id, binding, scope));
            }
        }
    }

    for binding in bindings.iter() {
        stmts.push(make_shadow_decl(cx, &erasure_ctxt, hir_match.hir_id, binding, scope));
    }

    let arm = &cx.thir.arms[arm_id];
    let block = Block {
        targeted_by_break: false,
        region_scope: scope,
        span: cx.thir.exprs[arm.body].span,
        stmts: stmts.into_boxed_slice(),
        expr: Some(arm.body),
        safety_mode: BlockSafety::Safe,
    };
    let block_id = cx.thir.blocks.push(block);

    let new_body = expr_id_from_kind(
        cx,
        ExprKind::Block { block: block_id },
        hir_match.hir_id,
        hir_match.span,
        cx.thir.exprs[arm.body].ty,
    );

    let arm = &cx.thir.arms[arm_id];
    let new_arm = Arm {
        hir_id: arm.hir_id,
        pattern: pat,
        guard: arm.guard,
        body: new_body,
        scope: arm.scope,
        span: arm.span,
    };
    cx.thir.arms.push(new_arm)
}

/// Conjoin the given expressions (intended to be used with Let expressions)
fn conjoin_exprs<'tcx>(
    cx: &mut ThirBuildCx<'tcx>,
    exprs: &[ExprId],
    hir_id: HirId,
    span: Span,
) -> ExprKind<'tcx> {
    // rustc_mid_build expects `&&` chains to associate a specific direction,
    // specifically ((e1 && e2) && e3) which is what we emit here.
    // Note: when we support let-chains, we will need to do more work to re-associate properly
    // at the top level.
    assert!(exprs.len() >= 2);
    let mut kind = ExprKind::LogicalOp { op: LogicalOp::And, lhs: exprs[0], rhs: exprs[1] };
    let bool_ty = cx.tcx.mk_ty_from_kind(TyKind::Bool);
    for rhs_id in exprs.iter().skip(2) {
        let lhs_id = expr_id_from_kind(cx, kind, hir_id, span, bool_ty);
        kind = ExprKind::LogicalOp { op: LogicalOp::And, lhs: lhs_id, rhs: *rhs_id };
    }
    kind
}

/// Represents a binding that requires a complementary shadow binding.
struct Binding<'tcx> {
    name: Symbol,
    var: LocalVarId,
    ty: Ty<'tcx>,
    span: Span,
    /// Is this a 'ref mut' binding?
    /// (i.e., does it require special handling as a mutable reference)
    ref_mut: bool,
    /// Mutability of the binding (i.e., the normal 'mut')
    mutbl: Mutability,
}

/// Find all bindings in the given pattern
fn pattern_bindings<'tcx>(pat: &Pat<'tcx>) -> Vec<Binding<'tcx>> {
    let mut bindings = vec![];
    pattern_bindings_rec(&mut bindings, pat);
    bindings
}

fn pattern_bindings_rec<'tcx>(bindings: &mut Vec<Binding<'tcx>>, pat: &Pat<'tcx>) {
    match &pat.kind {
        PatKind::Missing => {}
        PatKind::Wild => {}
        PatKind::Binding { name, mode, var, ty, subpattern, is_primary: _, is_shorthand: _ } => {
            bindings.push(Binding {
                name: *name,
                var: *var,
                ty: *ty,
                span: pat.span,
                ref_mut: matches!(mode, BindingMode(ByRef::Yes(_, Mutability::Mut), _)),
                mutbl: mode.1,
            });
            if let Some(subpat) = subpattern {
                pattern_bindings_rec(bindings, subpat);
            }
        }
        PatKind::Variant { adt_def: _, args: _, variant_index: _, subpatterns }
        | PatKind::Leaf { subpatterns } => {
            for field_pat in subpatterns.iter() {
                pattern_bindings_rec(bindings, &field_pat.pattern);
            }
        }
        PatKind::Deref { subpattern, pin: _ } => {
            pattern_bindings_rec(bindings, subpattern);
        }
        PatKind::DerefPattern { subpattern, borrow: _ } => {
            pattern_bindings_rec(bindings, subpattern);
        }
        PatKind::Constant { value: _ } => {}
        PatKind::Range(_pat_range) => {}
        PatKind::Slice { prefix, slice, suffix } | PatKind::Array { prefix, slice, suffix } => {
            for p in prefix.iter() {
                pattern_bindings_rec(bindings, p);
            }
            if let Some(sl) = slice {
                pattern_bindings_rec(bindings, sl);
            }
            for p in suffix.iter() {
                pattern_bindings_rec(bindings, p);
            }
        }
        PatKind::Or { pats } => {
            if pats.len() > 0 {
                pattern_bindings_rec(bindings, &pats[0]);
            }
        }
        PatKind::Never => {}
        PatKind::Error(_error_guaranteed) => {}
    }
}

/// Represents one of the two halves in the half pattern transformation.
#[derive(Clone, Copy)]
enum Half {
    Normal,
    Shadow,
}

/// Transform the original pattern into one of the pattern-halves.
/// e.g., for `(ref mut x, y)` we create one of:
/// Normal: `(ref mut x_half1, y)`
/// Shadow: `(ref mut x_half2, _)`
/// More generally: Each 'ref mut' binding turns into either `x_half1` or `x_half2`.
/// For all other bindings, it stays the same in the Normal pattern and is removed from
/// the Shadow pattern.
fn make_half_pat<'tcx>(pat: Box<Pat<'tcx>>, half_kind: Half) -> Box<Pat<'tcx>> {
    let mut pat = pat;
    make_half_pat_rec(&mut pat, half_kind);
    pat
}

fn make_half_pat_rec<'tcx>(pat: &mut Pat<'tcx>, half_kind: Half) {
    match &mut pat.kind {
        PatKind::Missing => {}
        PatKind::Wild => {}
        PatKind::Binding {
            name: _,
            mode,
            var,
            ty: _,
            subpattern,
            is_primary: _,
            is_shorthand: _,
        } => {
            if let BindingMode(ByRef::Yes(pinned, Mutability::Mut), mutbl) = mode {
                assert!(matches!(pinned, Pinnedness::Not));
                *var = half_local_var_id(*var, half_kind);
                *mutbl = Mutability::Not;
            }
            if let Some(subpat) = subpattern {
                make_half_pat_rec(subpat, half_kind);
            }

            let erase_binder = matches!(half_kind, Half::Shadow)
                && !matches!(mode, BindingMode(ByRef::Yes(_, Mutability::Mut), _));
            if erase_binder {
                if subpattern.is_some() {
                    let mut subpat = None;
                    std::mem::swap(subpattern, &mut subpat);
                    let subpat = *subpat.unwrap();
                    *pat = subpat;
                } else {
                    pat.kind = PatKind::Wild;
                }
            }
        }
        PatKind::Variant { adt_def: _, args: _, variant_index: _, subpatterns }
        | PatKind::Leaf { subpatterns } => {
            for field_pat in subpatterns.iter_mut() {
                make_half_pat_rec(&mut field_pat.pattern, half_kind);
            }
        }
        PatKind::Deref { subpattern, pin: _ } => {
            make_half_pat_rec(subpattern, half_kind);
        }
        PatKind::DerefPattern { subpattern, borrow: _ } => {
            make_half_pat_rec(subpattern, half_kind);
        }
        PatKind::Constant { value: _ } => {}
        PatKind::Range(_pat_range) => {}
        PatKind::Slice { prefix, slice, suffix } | PatKind::Array { prefix, slice, suffix } => {
            for p in prefix.iter_mut() {
                make_half_pat_rec(p, half_kind);
            }
            if let Some(sl) = slice {
                make_half_pat_rec(sl, half_kind);
            }
            for p in suffix.iter_mut() {
                make_half_pat_rec(p, half_kind);
            }
        }
        PatKind::Or { pats } => {
            for p in pats.iter_mut() {
                make_half_pat_rec(p, half_kind);
            }
        }
        PatKind::Never => {}
        PatKind::Error(_error_guaranteed) => {}
    }
}

/// Return a new statement equivalent to the given `stmt` but with the pattern replaced
/// by the given one.
fn stmt_update_pat<'tcx>(
    cx: &mut ThirBuildCx<'tcx>,
    stmt: StmtId,
    new_pat: Box<Pat<'tcx>>,
) -> StmtId {
    let StmtKind::Let {
        remainder_scope,
        init_scope,
        pattern: _,
        initializer,
        else_block,
        span,
        hir_id,
    } = cx.thir.stmts[stmt].kind
    else {
        panic!("stmt_update_pat");
    };
    let stmt = Stmt {
        kind: StmtKind::Let {
            hir_id,
            remainder_scope,
            init_scope,
            pattern: new_pat,
            initializer,
            else_block,
            span,
        },
    };
    cx.thir.stmts.push(stmt)
}

/// Creates a let-statement for the shadow half of the half-pattern transformation.
/// If the pattern may be refutable, we also add an 'else' block.
fn make_half_decl<'tcx>(
    cx: &mut ThirBuildCx<'tcx>,
    erasure_ctxt: &VerusErasureCtxt,
    hir_id: HirId,
    span: Span,
    pat: Box<Pat<'tcx>>,
    shadow_rhs: ExprId,
    refutable: bool,
    remainder_scope: region::Scope,
) -> StmtId {
    let else_block = if refutable {
        let never_ty = cx.tcx.mk_ty_from_kind(TyKind::Never);
        let e = erased_ghost_value(cx, erasure_ctxt, hir_id, span, never_ty);
        let block = Block {
            targeted_by_break: false,
            region_scope: region::Scope {
                local_id: hir_id.local_id,
                data: region::ScopeData::Node,
            },
            span: span,
            stmts: vec![].into_boxed_slice(),
            expr: Some(e),
            safety_mode: BlockSafety::Safe,
        };
        Some(cx.thir.blocks.push(block))
    } else {
        None
    };

    let stmt = Stmt {
        kind: StmtKind::Let {
            hir_id,
            remainder_scope,
            init_scope: region::Scope { local_id: hir_id.local_id, data: region::ScopeData::Node },
            pattern: pat,
            initializer: Some(shadow_rhs),
            else_block,
            span: span,
        },
    };

    cx.thir.stmts.push(stmt)
}

/// Same as `make_half_decl`, but returns a let expression instead of let statement.
fn make_half_let_expr<'tcx>(
    cx: &mut ThirBuildCx<'tcx>,
    _erasure_ctxt: &VerusErasureCtxt,
    hir_id: HirId,
    span: Span,
    pat: Box<Pat<'tcx>>,
    shadow_rhs: ExprId,
) -> ExprId {
    let kind = ExprKind::Let { expr: shadow_rhs, pat };
    expr_id_from_kind(cx, kind, hir_id, span, cx.tcx.mk_ty_from_kind(TyKind::Bool))
}

/// Create the decl that ties the two halves together, establishing the variable whose
/// name matches the original variable:
/// ```
/// let x = mutable_reference_tie(x_half1, x_half2);
/// ```
fn make_tie_halves_decl<'tcx>(
    cx: &mut ThirBuildCx<'tcx>,
    hir_id: HirId,
    binding: &Binding<'tcx>,
    remainder_scope: region::Scope,
) -> StmtId {
    let (pat, tied) = make_tie_halves_components(cx, hir_id, binding);

    let stmt = Stmt {
        kind: StmtKind::Let {
            hir_id,
            remainder_scope,
            init_scope: region::Scope { local_id: hir_id.local_id, data: region::ScopeData::Node },
            pattern: pat,
            initializer: Some(tied),
            else_block: None,
            span: binding.span,
        },
    };

    cx.thir.stmts.push(stmt)
}

/// Same as `make_tie_halves_decl`, but returns a let expression instead of let statement.
fn make_tie_halves_let_expr<'tcx>(
    cx: &mut ThirBuildCx<'tcx>,
    hir_id: HirId,
    binding: &Binding<'tcx>,
) -> ExprId {
    let (pat, tied) = make_tie_halves_components(cx, hir_id, binding);
    let kind = ExprKind::Let { expr: tied, pat };
    expr_id_from_kind(cx, kind, hir_id, binding.span, cx.tcx.mk_ty_from_kind(TyKind::Bool))
}

fn make_tie_halves_components<'tcx>(
    cx: &mut ThirBuildCx<'tcx>,
    hir_id: HirId,
    binding: &Binding<'tcx>,
) -> (Box<Pat<'tcx>>, ExprId) {
    let pat = Box::new(Pat {
        ty: binding.ty,
        span: binding.span,
        kind: PatKind::Binding {
            name: binding.name,
            mode: BindingMode(ByRef::No, binding.mutbl),
            var: binding.var,
            ty: binding.ty,
            subpattern: None,
            is_primary: true,
            is_shorthand: false,
        },
        extra: None,
    });

    let e1 = expr_id_from_kind(
        cx,
        ExprKind::VarRef { id: half_local_var_id(binding.var, Half::Normal) },
        hir_id,
        binding.span,
        binding.ty,
    );
    let e2 = expr_id_from_kind(
        cx,
        ExprKind::VarRef { id: half_local_var_id(binding.var, Half::Shadow) },
        hir_id,
        binding.span,
        binding.ty,
    );
    let tied_kind = tie_mut_refs(cx, hir_id, binding.span, e1, e2, false);
    let tied = expr_id_from_kind(cx, tied_kind, hir_id, binding.span, binding.ty);
    (pat, tied)
}

/// Returns a decl that binds the shadow var:
/// ```
/// let x_shadow = arbitrary_ghost_value();
/// ```
fn make_shadow_decl<'tcx>(
    cx: &mut ThirBuildCx<'tcx>,
    erasure_ctxt: &VerusErasureCtxt,
    hir_id: HirId,
    binding: &Binding<'tcx>,
    remainder_scope: region::Scope,
) -> StmtId {
    let pat = Box::new(Pat {
        ty: binding.ty,
        span: binding.span,
        kind: PatKind::Binding {
            name: shadow_name(binding.name),
            mode: BindingMode(ByRef::No, Mutability::Mut),
            var: shadow_local_var_id(binding.var),
            ty: binding.ty,
            subpattern: None,
            is_primary: true,
            is_shorthand: false,
        },
        extra: None,
    });

    let initializer = erased_ghost_value(cx, erasure_ctxt, hir_id, binding.span, binding.ty);

    let stmt = Stmt {
        kind: StmtKind::Let {
            hir_id,
            remainder_scope,
            init_scope: region::Scope { local_id: hir_id.local_id, data: region::ScopeData::Node },
            pattern: pat,
            initializer: Some(initializer),
            else_block: None,
            span: binding.span,
        },
    };

    cx.thir.stmts.push(stmt)
}

/// Same as `make_shadow_decl`, but returns a let expression instead of let statement.
fn make_shadow_let_expr<'tcx>(
    cx: &mut ThirBuildCx<'tcx>,
    erasure_ctxt: &VerusErasureCtxt,
    hir_id: HirId,
    binding: &Binding<'tcx>,
) -> ExprId {
    let pat = Box::new(Pat {
        ty: binding.ty,
        span: binding.span,
        kind: PatKind::Binding {
            name: shadow_name(binding.name),
            mode: BindingMode(ByRef::No, Mutability::Mut),
            var: shadow_local_var_id(binding.var),
            ty: binding.ty,
            subpattern: None,
            is_primary: true,
            is_shorthand: false,
        },
        extra: None,
    });

    let initializer = erased_ghost_value(cx, erasure_ctxt, hir_id, binding.span, binding.ty);

    let kind = ExprKind::Let { expr: initializer, pat };
    expr_id_from_kind(cx, kind, hir_id, binding.span, cx.tcx.mk_ty_from_kind(TyKind::Bool))
}

/// Create the name for the shadow var.
/// This name might show up in error messages: e.g.,
/// > cannot borrow `(Verus spec a)` as immutable because it is also borrowed as mutable
/// or:
/// > cannot borrow `(Verus spec a).field` as immutable because it is also borrowed as mutable
fn shadow_name(name: Symbol) -> Symbol {
    Symbol::intern(&format!("(Verus spec {:})", name.as_str()))
    //Symbol::intern(&format!("{:} (which cannot be used in Verus ghost code while it is borrowed as mutable)", name.as_str()))
    //Symbol::intern(&format!("({:} for Verus ghost code)", name.as_str()))
}

/// Get the LocalVarId for the `x_shadow` variable
fn shadow_local_var_id(v: LocalVarId) -> LocalVarId {
    modded_local_var_id(v, 1)
}

/// Get the LocalVarId for the `x_half1` or `x_half2` variables
fn half_local_var_id(v: LocalVarId, hk: Half) -> LocalVarId {
    modded_local_var_id(
        v,
        match hk {
            Half::Normal => 2,
            Half::Shadow => 3,
        },
    )
}

/// Is this an `x_half1`/`x_half2` identifier?
fn is_half_var_id(enclosing_def_id: LocalDefId, v: LocalVarId, hk: Half) -> bool {
    let v_id = v.0.owner.def_id.local_def_index.as_usize();
    let main_id = enclosing_def_id.local_def_index.as_usize();
    let modifier_offset = v_id.checked_sub(main_id).unwrap();
    assert!(modifier_offset <= 3);
    match hk {
        Half::Normal => modifier_offset == 2,
        Half::Shadow => modifier_offset == 3,
    }
}

/// Is this an `x_shadow` identifier?
fn is_shadow_var_id(enclosing_def_id: LocalDefId, v: LocalVarId) -> bool {
    let v_id = v.0.owner.def_id.local_def_index.as_usize();
    let main_id = enclosing_def_id.local_def_index.as_usize();
    let modifier_offset = v_id.checked_sub(main_id).unwrap();
    assert!(modifier_offset <= 3);
    modifier_offset == 1
}

/// Make a fresh LocalVarId
fn modded_local_var_id(v: LocalVarId, mod_idx: usize) -> LocalVarId {
    // The easiest way to make unique LocalVarIds for the shadow variables
    // is to use a different ownerId (since all the existing LocalVarIds will have the same OwnerId)
    // The result will obviously be a bogus HirId, but this seems to be fine because
    // the LocalVarIds are only used for uniqueness.
    //
    // This does have some downside. For one, dbg-printing these LocalVarIds causes a panic.
    LocalVarId(HirId {
        owner: rustc_hir::OwnerId {
            def_id: rustc_hir::def_id::LocalDefId {
                local_def_index: rustc_hir::def_id::DefIndex::from_usize(
                    v.0.owner.def_id.local_def_index.as_usize() + mod_idx,
                ),
            },
        },
        local_id: v.0.local_id,
    })
}

/// Given `&mut place`, return `&mut place_shadow`.
/// Returns None if we don't need to do anything in the shadow world
/// (e.g., the place is a temporary).
fn shadow_mut_ref_kind<'tcx>(
    cx: &mut ThirBuildCx<'tcx>,
    hir_id: HirId,
    span: Span,
    arg: ExprKind<'tcx>,
) -> Option<ExprKind<'tcx>> {
    match &arg {
        ExprKind::Borrow { borrow_kind, arg } => {
            let shadow_arg = shadow_place(cx, hir_id, span, *arg)?;
            Some(ExprKind::Borrow { borrow_kind: *borrow_kind, arg: shadow_arg })
        }
        _ => unreachable!(),
    }
}

/// Given `place`, return `place_shadow`. e.g.:
/// `x`       -> `x_shadow`
/// `x.field` -> `x_shadow.field`
/// `*x`      -> `*x_shadow`
pub(crate) fn shadow_place<'tcx>(
    cx: &mut ThirBuildCx<'tcx>,
    hir_id: HirId,
    span: Span,
    arg: ExprId,
) -> Option<ExprId> {
    shadow_place_rec(cx, hir_id, span, arg)
}

fn shadow_place_rec<'tcx>(
    cx: &mut ThirBuildCx<'tcx>,
    hir_id: HirId,
    span: Span,
    arg: ExprId,
) -> Option<ExprId> {
    let expr = cx.thir.exprs[arg].clone();
    let shadow_kind = match &expr.kind {
        ExprKind::Scope { hir_id: _, region_scope: _, value } => {
            return shadow_place_rec(cx, hir_id, span, *value);
        }
        ExprKind::Deref { arg } => {
            let ty = cx.thir.exprs[*arg].ty;
            if matches!(ty.kind(), TyKind::Ref(_, _, Mutability::Not)) {
                // Mutable borrow from behind immutable reference: this will be a normal
                // error so skip special handling
                return None;
            }

            let value = shadow_place_rec(cx, hir_id, span, *arg)?;
            ExprKind::Deref { arg: value }
        }
        ExprKind::Field { lhs, variant_index, name } => {
            let value = shadow_place_rec(cx, hir_id, span, *lhs)?;
            ExprKind::Field { lhs: value, variant_index: *variant_index, name: *name }
        }
        ExprKind::Index { lhs, index } => {
            let lhs = shadow_place_rec(cx, hir_id, span, *lhs)?;
            let index_ty = cx.thir.exprs[*index].ty;
            let erasure_ctxt = cx.verus_ctxt.ctxt.clone().unwrap();
            let index = erased_ghost_value(cx, &erasure_ctxt, hir_id, span, index_ty);
            ExprKind::Index { lhs, index }
        }
        ExprKind::VarRef { id } => {
            if crate::verus_expr::is_bound_via_pattern_guard(cx, id.0) {
                return None;
            }
            ExprKind::VarRef { id: shadow_local_var_id(*id) }
        }
        ExprKind::UpvarRef { var_hir_id: _, closure_def_id: _ } => {
            return None;
        }

        ExprKind::If { .. }
        | ExprKind::Call { .. }
        | ExprKind::ByUse { .. }
        | ExprKind::Binary { .. }
        | ExprKind::LogicalOp { .. }
        | ExprKind::Unary { .. }
        | ExprKind::Cast { .. }
        | ExprKind::Use { .. }
        | ExprKind::NeverToAny { .. }
        | ExprKind::PointerCoercion { .. }
        | ExprKind::Loop { .. }
        | ExprKind::Let { .. }
        | ExprKind::Match { .. }
        | ExprKind::Block { .. }
        | ExprKind::Assign { .. }
        | ExprKind::AssignOp { .. }
        | ExprKind::Borrow { .. }
        | ExprKind::RawBorrow { .. }
        | ExprKind::Break { .. }
        | ExprKind::Continue { .. }
        | ExprKind::Return { .. }
        | ExprKind::Become { .. }
        | ExprKind::ConstBlock { .. }
        | ExprKind::Repeat { .. }
        | ExprKind::Array { .. }
        | ExprKind::Tuple { .. }
        | ExprKind::Adt(..)
        | ExprKind::ValueTypeAscription { .. }
        | ExprKind::PlaceTypeAscription { .. }
        | ExprKind::Closure(..)
        | ExprKind::Literal { .. }
        | ExprKind::NonHirLiteral { .. }
        | ExprKind::ZstLiteral { .. }
        | ExprKind::NamedConst { .. }
        | ExprKind::ConstParam { .. }
        | ExprKind::StaticRef { .. }
        | ExprKind::InlineAsm { .. }
        | ExprKind::ThreadLocalRef(..)
        | ExprKind::LoopMatch { .. }
        | ExprKind::ConstContinue { .. }
        | ExprKind::Yield { .. } => {
            return None;
        }

        ExprKind::PlaceUnwrapUnsafeBinder { .. }
        | ExprKind::ValueUnwrapUnsafeBinder { .. }
        | ExprKind::WrapUnsafeBinder { .. } => {
            unimplemented!();
        }
    };

    let shadow_expr =
        Expr { kind: shadow_kind, ty: expr.ty, temp_scope_id: expr.temp_scope_id, span: expr.span };
    let shadow_expr_id = cx.thir.exprs.push(shadow_expr);
    Some(shadow_expr_id)
}

/// Returns `mutable_reference_tie(e1, e2)`
fn tie_mut_refs<'tcx>(
    cx: &mut ThirBuildCx<'tcx>,
    hir_id: HirId,
    span: Span,
    e1: ExprId,
    e2: ExprId,
    two_phase: bool,
) -> ExprKind<'tcx> {
    let erasure_ctxt = cx.verus_ctxt.ctxt.clone().unwrap();

    let e1_ty = cx.thir.exprs[e1].ty;
    let e2_ty = cx.thir.exprs[e2].ty;

    let e1_ty_inner = match &e1_ty.kind() {
        TyKind::Ref(_r, t, _m) => *t,
        _ => unreachable!(),
    };
    let e2_ty_inner = match &e2_ty.kind() {
        TyKind::Ref(_region, ty, _mutbl) => *ty,
        _ => unreachable!(),
    };

    let arg1 = GenericArg::from(e1_ty_inner);
    let arg2 = GenericArg::from(e2_ty_inner);
    let args = cx.tcx.mk_args(&[arg1, arg2]);
    let fn_def_id = if two_phase {
        erasure_ctxt.two_phase_mutable_reference_tie_fn_def_id
    } else {
        erasure_ctxt.mutable_reference_tie_fn_def_id
    };
    let fn_ty = cx.tcx.mk_ty_from_kind(TyKind::FnDef(fn_def_id, args));

    let fun_expr_kind = ExprKind::ZstLiteral { user_ty: None };
    let fun_expr = expr_id_from_kind(cx, fun_expr_kind, hir_id, span, fn_ty);

    ExprKind::Call {
        ty: fn_ty,
        fun: fun_expr,
        args: Box::new([e1, e2]),
        from_hir_call: false,
        fn_span: span,
    }
}

pub(crate) fn is_two_phase_mutable_reference_tie<'tcx>(
    thir: &Thir<'tcx>,
    expr_id: ExprId,
) -> Option<(ExprId, ExprId, ExprId, Ty<'tcx>)> {
    let Some(erasure_ctxt) = crate::verus::get_verus_erasure_ctxt_option() else {
        return None;
    };
    match &thir.exprs[expr_id].kind {
        ExprKind::Call { ty, fun, args, .. } => match ty.kind() {
            TyKind::FnDef(fn_def_id, _)
                if *fn_def_id == erasure_ctxt.two_phase_mutable_reference_tie_fn_def_id =>
            {
                assert!(args.len() == 2);
                Some((*fun, args[0], args[1], thir.exprs[expr_id].ty))
            }
            _ => None,
        },
        _ => None,
    }
}

/// Given a bunch of variable uses, return an expression containing relevant shadow uses,
/// for any use with erasure-mode `VarErasure::Shadow`.
pub(crate) fn shadow_var_uses<'tcx>(
    cx: &mut ThirBuildCx<'tcx>,
    erasure_ctxt: &VerusErasureCtxt,
    uses: Vec<LocalUse<'tcx>>,
) -> Vec<ExprId> {
    let mut v = vec![];
    for local_use in uses.iter() {
        let emit_shadow = match erasure_ctxt.vars.get(&local_use.hir_id) {
            Some(VarErasure::Erase) => false,
            Some(VarErasure::Shadow | VarErasure::Keep) | None => true,
        };
        if !emit_shadow {
            continue;
        }

        if cx.is_upvar(local_use.local.0) {
            continue;
        }
        if crate::verus_expr::is_bound_via_pattern_guard(cx, local_use.local.0) {
            continue;
        }

        let kind = ExprKind::VarRef { id: shadow_local_var_id(local_use.local) };
        let mut ty = local_use.ty;
        let mut e = expr_id_from_kind(cx, kind, local_use.root_hir_id, local_use.span, ty);

        for proj in local_use.projs.iter() {
            let kind = match proj.kind {
                crate::verus::ProjKind::Deref => ExprKind::Deref { arg: e },
                crate::verus::ProjKind::Field(variant_index, name) => {
                    ExprKind::Field { lhs: e, variant_index, name }
                }
            };
            ty = proj.ty;
            e = expr_id_from_kind(cx, kind, local_use.root_hir_id, local_use.span, ty);
        }

        let kind = ExprKind::Borrow { borrow_kind: BorrowKind::Shared, arg: e };
        let ref_ty = cx.tcx.mk_ty_from_kind(TyKind::Ref(
            Region::new_from_kind(cx.tcx, RegionKind::ReErased),
            ty,
            Mutability::Not,
        ));
        let e = expr_id_from_kind(cx, kind, local_use.root_hir_id, local_use.span, ref_ty);

        v.push(e);
    }
    v
}

/// Generates a use of a single shadow var:
/// Replace var x (of type T) with `arbitrary_ghost_value::<T>(&shadow_x)`.
/// (This function assumes it's already checked that the given variable has
/// erasure mode `VarErasure::Shadow`.)
pub(crate) fn shadow_var_use<'tcx>(
    cx: &mut ThirBuildCx<'tcx>,
    erasure_ctxt: &VerusErasureCtxt,
    expr: &'tcx hir::Expr<'tcx>,
    var_hir_id: HirId,
) -> ExprKind<'tcx> {
    let local = LocalVarId(var_hir_id);

    let kind = ExprKind::VarRef { id: shadow_local_var_id(local) };
    let ty = cx.typeck_results.expr_ty(expr);
    let e = expr_id_from_kind(cx, kind, expr.hir_id, expr.span, ty);

    let kind = ExprKind::Borrow { borrow_kind: BorrowKind::Shared, arg: e };
    let ref_ty = cx.tcx.mk_ty_from_kind(TyKind::Ref(
        Region::new_from_kind(cx.tcx, RegionKind::ReErased),
        ty,
        Mutability::Not,
    ));
    let e = expr_id_from_kind(cx, kind, expr.hir_id, expr.span, ref_ty);

    shadow_ghost_value_kind_with_args(cx, erasure_ctxt, expr.hir_id, expr.span, ty, vec![e])
}

/// Transform `shadow_ghost_value(&place).field` to `shadow_ghost_value(&place.field)`
/// or:
/// `*shadow_ghost_value(&place)` to `shadow_ghost_value(&*place)`
pub(crate) fn try_move_head_into_shadow<'tcx>(
    cx: &mut ThirBuildCx<'tcx>,
    hir_expr: &'tcx hir::Expr<'tcx>,
    ty: Ty<'tcx>,
    kind: &rustc_middle::thir::ExprKind<'tcx>,
) -> Option<ExprKind<'tcx>> {
    match *kind {
        ExprKind::Field { lhs: arg, variant_index: _, name: _ } | ExprKind::Deref { arg } => {
            let erasure_ctxt = cx.verus_ctxt.ctxt.clone().unwrap();
            if is_shadow_value(cx, &erasure_ctxt, &cx.thir.exprs[arg].kind) {
                Some(shadow_apply_projection(
                    cx,
                    &erasure_ctxt,
                    hir_expr,
                    arg,
                    ApplyProjection { ty, kind: kind.clone() },
                ))
            } else {
                None
            }
        }
        _ => None,
    }
}

fn is_shadow_value<'tcx>(
    cx: &ThirBuildCx<'tcx>,
    erasure_ctxt: &VerusErasureCtxt,
    expr_kind: &rustc_middle::thir::ExprKind<'tcx>,
) -> bool {
    match expr_kind {
        ExprKind::Call { fun, args: _, .. } => match cx.thir.exprs[*fun].ty.kind() {
            TyKind::FnDef(fn_def_id, _) => *fn_def_id == erasure_ctxt.shadow_ghost_value_fn_def_id,
            _ => false,
        },
        ExprKind::Scope { region_scope: _, value, hir_id: _ } => {
            is_shadow_value(cx, erasure_ctxt, &cx.thir.exprs[*value].kind)
        }
        _ => false,
    }
}

struct ApplyProjection<'tcx> {
    ty: Ty<'tcx>,
    kind: rustc_middle::thir::ExprKind<'tcx>,
}

fn shadow_apply_projection<'tcx>(
    cx: &mut ThirBuildCx<'tcx>,
    erasure_ctxt: &VerusErasureCtxt,
    hir_expr: &hir::Expr<'tcx>,
    expr_id: ExprId,
    p: ApplyProjection<'tcx>,
) -> ExprKind<'tcx> {
    match &cx.thir.exprs[expr_id].kind {
        ExprKind::Call { args, .. } => {
            let arg = args[0];
            let arg = match &cx.thir.exprs[arg].kind {
                ExprKind::Tuple { fields } => fields[0],
                _ => unreachable!(),
            };

            let ty = p.ty;
            let new_arg = shadow_apply_projection_inner(cx, erasure_ctxt, hir_expr, arg, p);
            shadow_ghost_value_kind_with_args(
                cx,
                erasure_ctxt,
                hir_expr.hir_id,
                hir_expr.span,
                ty,
                vec![new_arg],
            )
        }
        ExprKind::Scope { region_scope: _, value, hir_id: _ } => {
            shadow_apply_projection(cx, erasure_ctxt, hir_expr, *value, p)
        }
        _ => panic!("shadow_apply_projection failed"),
    }
}

fn shadow_apply_projection_inner<'tcx>(
    cx: &mut ThirBuildCx<'tcx>,
    _erasure_ctxt: &VerusErasureCtxt,
    hir_expr: &hir::Expr<'tcx>,
    expr_id: ExprId,
    p: ApplyProjection<'tcx>,
) -> ExprId {
    let ExprKind::Borrow { borrow_kind, arg } = cx.thir.exprs[expr_id].kind else { unreachable!() };
    let projected_arg_kind = match &p.kind {
        ExprKind::Field { lhs: _, variant_index, name } => {
            ExprKind::Field { lhs: arg, variant_index: *variant_index, name: *name }
        }
        ExprKind::Deref { .. } => ExprKind::Deref { arg },
        _ => panic!("shadow_apply_projection_inner unexpected kind"),
    };
    let projected_arg =
        expr_id_from_kind(cx, projected_arg_kind, hir_expr.hir_id, hir_expr.span, p.ty);
    let borrow_kind = ExprKind::Borrow { borrow_kind, arg: projected_arg };
    let ref_ty = cx.tcx.mk_ty_from_kind(TyKind::Ref(
        Region::new_from_kind(cx.tcx, RegionKind::ReErased),
        p.ty,
        Mutability::Not,
    ));
    expr_id_from_kind(cx, borrow_kind, hir_expr.hir_id, hir_expr.span, ref_ty)
}

/// Get a shadow use as a statement.
pub(crate) fn shadow_use_stmt<'tcx>(
    cx: &mut ThirBuildCx<'tcx>,
    _erasure_ctxt: &VerusErasureCtxt,
    hir_expr: &'tcx hir::Expr<'tcx>,
    shadow_expr: ExprId,
) -> StmtId {
    let ty = cx.thir.exprs[shadow_expr].ty;

    let kind = ExprKind::Borrow { borrow_kind: BorrowKind::Shared, arg: shadow_expr };
    let ref_ty = cx.tcx.mk_ty_from_kind(TyKind::Ref(
        Region::new_from_kind(cx.tcx, RegionKind::ReErased),
        ty,
        Mutability::Not,
    ));
    let e = expr_id_from_kind(cx, kind, hir_expr.hir_id, hir_expr.span, ref_ty);

    let stmt = Stmt {
        kind: StmtKind::Expr {
            scope: region::Scope {
                local_id: hir_expr.hir_id.local_id,
                data: region::ScopeData::Node,
            },
            expr: e,
        },
    };
    cx.thir.stmts.push(stmt)
}

/// Sequence 2 unit expressions into a single unit expression.
fn sequence_2_unit_exprs<'tcx>(
    cx: &mut ThirBuildCx<'tcx>,
    erasure_ctxt: &VerusErasureCtxt,
    hir_expr: &hir::Expr<'tcx>,
    e1: ExprId,
    e2: ExprId,
) -> ExprKind<'tcx> {
    erased_ghost_value_kind_with_args(
        cx,
        erasure_ctxt,
        hir_expr.hir_id,
        hir_expr.span,
        cx.tcx.types.unit,
        vec![e1, e2],
    )
}

pub(crate) fn loop_post<'tcx>(
    cx: &mut ThirBuildCx<'tcx>,
    hir_expr: &hir::Expr<'tcx>,
    ty: Ty<'tcx>,
    kind: rustc_middle::thir::ExprKind<'tcx>,
) -> rustc_middle::thir::ExprKind<'tcx> {
    let rustc_hir::ExprKind::Loop(hir_block, ..) = &hir_expr.kind else {
        panic!("Verus Internal Error: Expected ExprKind::Loop from THIR Loop");
    };

    let erasure_ctxt = cx.verus_ctxt.ctxt.clone().unwrap();

    let Some(loop_erasure) = erasure_ctxt.loop_erasure.get(&hir_expr.hir_id) else {
        // nothing to do
        return kind;
    };

    let mut inner_exprs = vec![];
    let mut outer_exprs = vec![];

    for (fn_hir_id, loc) in loop_erasure.specs.iter() {
        let (inner, outer) = match loc {
            LoopSpecEvaluationLocation::BodyStart => (true, false),
            LoopSpecEvaluationLocation::PostLoop => (false, true),
            LoopSpecEvaluationLocation::BodyStartAndPostLoop => (true, true),
        };
        let rustc_hir::Node::Expr(fn_hir_expr) = cx.tcx.hir_node(*fn_hir_id) else {
            panic!("Verus Internal Error: loop_post expected expected Expr");
        };
        let rustc_hir::ExprKind::Call(_fn, args) = &fn_hir_expr.kind else {
            panic!("Verus Internal Error: loop_post expected expected ExprKind::Call");
        };
        if args.len() != 1 {
            panic!("Verus Internal Error: loop_post expected expected args.len() == 1");
        }
        let arg_hir_expr = &args[0];
        let arg_ty = cx.typeck_results.expr_ty(arg_hir_expr);

        if inner {
            let kind =
                erase_tree_kind(cx, arg_hir_expr, hir_block.hir_id, TreeErase::IncludeBasicChecks);
            let e = expr_id_from_kind(cx, kind, hir_block.hir_id, hir_block.span, arg_ty);
            inner_exprs.push(e);
        }

        if outer {
            let kind =
                erase_tree_kind(cx, arg_hir_expr, hir_expr.hir_id, TreeErase::IncludeBasicChecks);
            let e = expr_id_from_kind(cx, kind, hir_expr.hir_id, hir_expr.span, arg_ty);
            outer_exprs.push(e);
        }
    }

    let mut kind = kind;

    // Insert inner_exprs
    let ExprKind::Loop { body } = kind else { unreachable!() };
    let new_body = insert_exprs_before(cx, inner_exprs, body, hir_block);
    kind = ExprKind::Loop { body: new_body };

    // Insert outer_exprs
    kind = insert_exprs_after_kind(cx, kind, ty, outer_exprs, hir_expr);

    return kind;
}

fn insert_exprs_before<'tcx>(
    cx: &mut ThirBuildCx<'tcx>,
    pre_exprs: Vec<ExprId>,
    last_expr: ExprId,
    hir_block: &rustc_hir::Block<'tcx>,
) -> ExprId {
    if pre_exprs.len() == 0 {
        return last_expr;
    }
    let scope =
        region::Scope { local_id: hir_block.hir_id.local_id, data: region::ScopeData::Node };
    let mut stmts = vec![];
    for e in pre_exprs.into_iter() {
        let stmt = Stmt { kind: StmtKind::Expr { scope, expr: e } };
        stmts.push(cx.thir.stmts.push(stmt));
    }
    let block = Block {
        targeted_by_break: false,
        region_scope: scope,
        span: hir_block.span,
        stmts: stmts.into_boxed_slice(),
        expr: Some(last_expr),
        safety_mode: BlockSafety::Safe,
    };
    let block = cx.thir.blocks.push(block);
    let kind = ExprKind::Block { block };
    let ty = cx.thir.exprs[last_expr].ty;
    expr_id_from_kind(cx, kind, hir_block.hir_id, hir_block.span, ty)
}

fn insert_exprs_after_kind<'tcx>(
    cx: &mut ThirBuildCx<'tcx>,
    kind: rustc_middle::thir::ExprKind<'tcx>,
    ty: Ty<'tcx>,
    post_exprs: Vec<ExprId>,
    hir_expr: &rustc_hir::Expr<'tcx>,
) -> rustc_middle::thir::ExprKind<'tcx> {
    if post_exprs.len() == 0 {
        return kind;
    }
    let erasure_ctxt = cx.verus_ctxt.ctxt.clone().unwrap();

    let e1 = expr_id_from_kind(cx, kind, hir_expr.hir_id, hir_expr.span, ty);

    let scope = region::Scope { local_id: hir_expr.hir_id.local_id, data: region::ScopeData::Node };
    let mut stmts = vec![];
    for e in post_exprs.into_iter() {
        let stmt = Stmt { kind: StmtKind::Expr { scope, expr: e } };
        stmts.push(cx.thir.stmts.push(stmt));
    }
    let block = Block {
        targeted_by_break: false,
        region_scope: scope,
        span: hir_expr.span,
        stmts: stmts.into_boxed_slice(),
        expr: None,
        safety_mode: BlockSafety::Safe,
    };
    let block = cx.thir.blocks.push(block);
    let kind = ExprKind::Block { block };
    let e2 = expr_id_from_kind(cx, kind, hir_expr.hir_id, hir_expr.span, cx.tcx.types.unit);

    // get_first(e1, e2)
    let arg1 = GenericArg::from(cx.thir.exprs[e1].ty);
    let arg2 = GenericArg::from(cx.thir.exprs[e2].ty);
    let args = cx.tcx.mk_args(&[arg1, arg2]);
    let fn_def_id = erasure_ctxt.get_first_fn_def_id;
    let fn_ty = cx.tcx.mk_ty_from_kind(TyKind::FnDef(fn_def_id, args));

    let fun_expr_kind = ExprKind::ZstLiteral { user_ty: None };
    let fun_expr = expr_id_from_kind(cx, fun_expr_kind, hir_expr.hir_id, hir_expr.span, fn_ty);

    ExprKind::Call {
        ty: fn_ty,
        fun: fun_expr,
        args: Box::new([e1, e2]),
        from_hir_call: false,
        fn_span: hir_expr.span,
    }
}
