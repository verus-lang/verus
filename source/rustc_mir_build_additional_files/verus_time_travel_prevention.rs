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

For two-phase borrows, we can't use the `mutable_references_tie` solution like we would
for normal mutable borrows. Imagine we expanded:

```
f(&mut[two_phase] x, y)
```

to:

```
f(mutable_reference_tie(&mut[two_phase] x, &mut x_shadow), y)
```

The problem is that the scope of the two-phase borrow only extends through the
artificial `mutable_reference_tie` call, not through the entire `f` call.

We do this instead:

```
fake_call(
    f(&mut[two_phase] x, y),
    &mut x_shadow,
    ...
)
```

where the `fake_call` wires up any lifetime variables appropriately to the output of `f`.
Note that the mutable borrow of `x_shadow` doesn't actually occur until `f` returns, but
this is fine because the two-phase borrow doesn't properly start until the end of the args
to `f`.

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
*/

use crate::rustc_index::Idx;
use crate::thir::cx::ThirBuildCx;
use crate::verus::{LocalUse, expr_id_from_kind};
use crate::verus::{
    VarErasure, VerusErasureCtxt, erased_ghost_value, erased_ghost_value_kind_with_args,
    make_fake_call_kind,
};
use rustc_hir as hir;
use rustc_hir::{BindingMode, ByRef, HirId, Mutability, Pinnedness};
use rustc_middle::middle::region;
use rustc_middle::mir::{BorrowKind, MutBorrowKind};
use rustc_middle::thir::LintLevel;
use rustc_middle::thir::{
    Arm, ArmId, Block, BlockSafety, Expr, ExprId, ExprKind, LocalVarId, LogicalOp, Pat, PatKind,
    Stmt, StmtId, StmtKind,
};
use rustc_middle::ty::{GenericArg, Region, RegionKind, Ty, TyKind};
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
            match borrow_kind_mut {
                MutBorrowKind::Default | MutBorrowKind::ClosureCapture => {
                    // Turn `&mut place` into
                    // `&mut mutable_reference_tie(&mut place, &mut shadow_place)`
                    // If the place is a temporary, we don't need to do the transformation.
                    let shadow =
                        shadow_mut_ref_kind(cx, hir_expr.hir_id, hir_expr.span, kind.clone());
                    match shadow {
                        None => kind,
                        Some(shadow_kind) => {
                            let main_expr =
                                expr_id_from_kind(cx, kind, hir_expr.hir_id, hir_expr.span, ty);
                            let shadow_expr = expr_id_from_kind(
                                cx,
                                shadow_kind,
                                hir_expr.hir_id,
                                hir_expr.span,
                                ty,
                            );
                            tie_mut_refs(cx, hir_expr.hir_id, hir_expr.span, main_expr, shadow_expr)
                        }
                    }
                }
                MutBorrowKind::TwoPhaseBorrow => {
                    // must be handled separately
                    kind
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
        ExprKind::Call { .. } => call_post(cx, hir_expr, ty, kind),
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
        pattern: pat,
        guard: arm.guard,
        body: new_body,
        lint_level: arm.lint_level,
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
        PatKind::AscribeUserType { ascription: _, subpattern } => {
            pattern_bindings_rec(bindings, subpattern);
        }
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
        PatKind::Deref { subpattern } => {
            pattern_bindings_rec(bindings, subpattern);
        }
        PatKind::DerefPattern { subpattern, borrow: _ } => {
            pattern_bindings_rec(bindings, subpattern);
        }
        PatKind::Constant { value: _ } => {}
        PatKind::ExpandedConstant { def_id: _, subpattern } => {
            pattern_bindings_rec(bindings, subpattern);
        }
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
        PatKind::AscribeUserType { ascription: _, subpattern } => {
            make_half_pat_rec(subpattern, half_kind);
        }
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
        PatKind::Deref { subpattern } => {
            make_half_pat_rec(subpattern, half_kind);
        }
        PatKind::DerefPattern { subpattern, borrow: _ } => {
            make_half_pat_rec(subpattern, half_kind);
        }
        PatKind::Constant { value: _ } => {}
        PatKind::ExpandedConstant { def_id: _, subpattern } => {
            make_half_pat_rec(subpattern, half_kind);
        }
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
        lint_level,
        span,
    } = cx.thir.stmts[stmt].kind
    else {
        panic!("stmt_update_pat");
    };
    let stmt = Stmt {
        kind: StmtKind::Let {
            remainder_scope,
            init_scope,
            pattern: new_pat,
            initializer,
            else_block,
            lint_level,
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
            remainder_scope,
            init_scope: region::Scope { local_id: hir_id.local_id, data: region::ScopeData::Node },
            pattern: pat,
            initializer: Some(shadow_rhs),
            else_block,
            lint_level: LintLevel::Explicit(hir_id),
            span: span,
        },
    };

    cx.thir.stmts.push(stmt)
}

/// Same as `make_half_decl`, but returns a let expression instead of let statement.
/// For let expressions, we don't have to worry about refutability.
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
            remainder_scope,
            init_scope: region::Scope { local_id: hir_id.local_id, data: region::ScopeData::Node },
            pattern: pat,
            initializer: Some(tied),
            else_block: None,
            lint_level: LintLevel::Explicit(hir_id),
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
    let tied_kind = tie_mut_refs(cx, hir_id, binding.span, e1, e2);
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
    });

    let initializer = erased_ghost_value(cx, erasure_ctxt, hir_id, binding.span, binding.ty);

    let stmt = Stmt {
        kind: StmtKind::Let {
            remainder_scope,
            init_scope: region::Scope { local_id: hir_id.local_id, data: region::ScopeData::Node },
            pattern: pat,
            initializer: Some(initializer),
            else_block: None,
            lint_level: LintLevel::Explicit(hir_id),
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
        ExprKind::Scope { region_scope: _, lint_level: _, value } => {
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
        ExprKind::VarRef { id } => ExprKind::VarRef { id: shadow_local_var_id(*id) },
        ExprKind::UpvarRef { var_hir_id, closure_def_id: _ } => {
            ExprKind::VarRef { id: shadow_local_var_id(*var_hir_id) }
        }

        ExprKind::Box { .. }
        | ExprKind::If { .. }
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
    let fn_def_id = erasure_ctxt.mutable_reference_tie_fn_def_id;
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

/// Post-process a function call, dealing with two-phase borrows
pub(crate) fn call_post<'tcx>(
    cx: &mut ThirBuildCx<'tcx>,
    hir_expr: &hir::Expr<'tcx>,
    return_ty: Ty<'tcx>,
    kind: ExprKind<'tcx>,
) -> ExprKind<'tcx> {
    let erasure_ctxt = cx.verus_ctxt.ctxt.clone().unwrap();
    let tcx = cx.tcx;

    let ExprKind::Call { ref args, ty: fun_ty, .. } = kind else { panic!("expr_let_post") };

    match fun_ty.kind() {
        TyKind::FnDef(def_id, _) if *def_id == erasure_ctxt.erased_ghost_value_fn_def_id => {
            return kind;
        }
        _ => {}
    }

    let mut two_phase_args = vec![];
    for (i, arg) in args.iter().enumerate() {
        if let Some(two_phase_arg) = get_two_phase_arg(cx, hir_expr, *arg, i) {
            two_phase_args.push(two_phase_arg);
        }
    }

    if two_phase_args.len() == 0 {
        return kind;
    }

    let original_call = expr_id_from_kind(cx, kind, hir_expr.hir_id, hir_expr.span, return_ty);

    // If the input type is (I_1, I_2, ..., I_n) -> Out
    // and the subsequence of args that needs two-phase handling are T_1, ..., T_k
    // then the fake function call is going to have type:
    // for<...> fn(Out, T_1, ..., T_k) -> Out

    let mut args = vec![original_call];
    for two_phase_arg in two_phase_args.iter() {
        args.push(two_phase_arg.shadow_arg);
    }

    let fn_sig = crate::verus::fn_sig_with_region_vars(tcx, fun_ty);
    let bound_var_kinds = fn_sig.bound_vars();

    // note: we could also skip if the output ty doesn't reference the bound vars
    let output_ty = fn_sig.skip_binder().output();
    let mut input_tys = vec![output_ty];
    for two_phase_arg in two_phase_args.iter() {
        input_tys.push(fn_sig.skip_binder().inputs()[two_phase_arg.idx]);
    }

    let inputs_and_output =
        tcx.mk_type_list_from_iter(input_tys.iter().cloned().chain(std::iter::once(output_ty)));
    let fnty = tcx.mk_ty_from_kind(TyKind::FnPtr(
        rustc_middle::ty::Binder::bind_with_vars(
            rustc_middle::ty::FnSigTys { inputs_and_output },
            bound_var_kinds,
        ),
        rustc_middle::ty::FnHeader {
            c_variadic: false,
            safety: rustc_hir::Safety::Safe,
            abi: rustc_abi::ExternAbi::Rust,
        },
    ));

    make_fake_call_kind(cx, &erasure_ctxt, hir_expr.hir_id, hir_expr.span, fnty, args)
}

#[derive(Debug)]
struct TwoPhaseArg {
    shadow_arg: ExprId,
    idx: usize,
}

fn get_two_phase_arg<'tcx>(
    cx: &mut ThirBuildCx<'tcx>,
    hir_expr: &hir::Expr<'tcx>,
    arg: ExprId,
    idx: usize,
) -> Option<TwoPhaseArg> {
    let kind = &cx.thir.exprs[arg].kind;
    match kind {
        ExprKind::Borrow {
            borrow_kind: BorrowKind::Mut { kind: MutBorrowKind::TwoPhaseBorrow },
            arg: _,
        } => match shadow_mut_ref_kind(cx, hir_expr.hir_id, hir_expr.span, kind.clone()) {
            Some(shadow_arg_kind) => {
                let ty = cx.thir.exprs[arg].ty;
                let shadow_arg =
                    expr_id_from_kind(cx, shadow_arg_kind, hir_expr.hir_id, hir_expr.span, ty);
                Some(TwoPhaseArg { shadow_arg, idx })
            }
            None => None,
        },
        ExprKind::Scope { region_scope: _, lint_level: _, value } => {
            get_two_phase_arg(cx, hir_expr, *value, idx)
        }
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

        let kind = ExprKind::VarRef { id: shadow_local_var_id(local_use.local) };
        let e = expr_id_from_kind(cx, kind, local_use.root_hir_id, local_use.span, local_use.ty);

        let kind = ExprKind::Borrow { borrow_kind: BorrowKind::Shared, arg: e };
        let ref_ty = cx.tcx.mk_ty_from_kind(TyKind::Ref(
            Region::new_from_kind(cx.tcx, RegionKind::ReErased),
            local_use.ty,
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

    erased_ghost_value_kind_with_args(cx, erasure_ctxt, expr.hir_id, expr.span, ty, vec![e])
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
