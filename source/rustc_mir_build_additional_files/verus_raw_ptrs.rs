/*!
Lifetime checking for "native" raw pointer dereferences.

When Verus checks a raw pointer dereference `*p`, it uses a tracked permission
(e.g., a `PointsTo`) to justify the access. (The permission is determined during
rust_to_vir and passed here via `VerusErasureCtxt::raw_deref_permissions`.)
Verus's SMT encoding only checks the permission is _correct_; we still need to make sure
the permission is actually _available_ (e.g., not moved, not borrowed, not behind a shared
reference if we need to write) at the point where the pointer is dereferenced.

To do this, we emit borrows of the permission next to each use of a place containing
a raw pointer dereference. For example, given a place like `(*(*(*a).x).y).z`
(where each `*` is a raw pointer dereference) with permissions `Perm_A`, `Perm_B`, `Perm_C`
(for `a`, `(*a).x`, and `(*(*a).x).y`), we emit:

```rust
// Copy
_ = &Perm_A; _ = &Perm_B; _ = &Perm_C;
m = copy (*(*(*a).x).y).z;

// Assign
_ = &Perm_A; _ = &Perm_B; _ = &mut Perm_C;
(*(*(*a).x).y).z = ...;

// Mutable borrow
_ = &Perm_A; _ = &Perm_B;
r = mutable_reference_tie(&mut (*(*(*a).x).y).z, mutable_reference_tie(&mut Perm_C, &mut Shadow_Perm_C));

// Shared borrow
_ = &Perm_A; _ = &Perm_B;
r = shared_reference_tie(&(*(*(*a).x).y).z, &Perm_C);

// Raw borrow
_ = &Perm_A; _ = &Perm_B;
r = &raw (*(*(*a).x).y).z;
```

i.e., the inner pointers are always read, while the usage of the _outermost_ pointer
depends on how the place is used.

This is split across THIR construction and MIR building:

 * During THIR construction (this file), for each raw deref `*p`, we construct a
   THIR place expression for its permission, recorded in `ExtraThir::raw_deref_permissions`
   (keyed by the ExprId of `p`).
   For borrows, we construct the `*_reference_tie` calls directly in THIR.
   For any usage of the outermost pointer other than reading, we record the usage in
   `ExtraThir::raw_deref_outer_usage`.

 * During MIR building (verus_builder.rs), whenever we build a place (or perform a bounds
   check on an intermediate place), we emit the borrows of the permissions immediately
   before the place is used. This is important since a single THIR place expression
   may be used by multiple MIR statements (e.g., bounds checks), and there may be user code
   (e.g., index expressions) running in between.
*/

use crate::thir::cx::ThirBuildCx;
use crate::verus::{PermissionProjection, RawDerefPermission, expr_id_from_kind};
use rustc_hir as hir;
use rustc_hir::HirId;
use rustc_middle::mir::{BorrowKind, MutBorrowKind};
use rustc_middle::thir::{ExprId, ExprKind, LocalVarId, Thir};
use rustc_middle::ty::{GenericArg, Mutability, Ty, TyKind};
use rustc_span::Span;

/// How a permission is used (i.e., what kind of borrow we emit for it).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PermUsage {
    /// Emit a shared borrow of the permission
    Read,
    /// Emit a mutable borrow of the permission
    Write,
    /// Don't emit anything for this permission (either because the usage doesn't require
    /// the permission, or because it was already handled during THIR construction)
    Skip,
}

/// Get all the raw pointer dereferences that make up the given place expression.
/// Returns the pointer operands, from the outermost to the innermost.
/// The bool is true if there is any dereference (raw or otherwise) "above"
/// the outermost raw pointer dereference, i.e., if using the place would actually require
/// reading through the outermost pointer, even if the place is only raw-borrowed.
///
/// This needs to traverse the place in the same way as `expr_as_place` does.
pub(crate) fn place_raw_derefs<'tcx>(thir: &Thir<'tcx>, expr_id: ExprId) -> (Vec<ExprId>, bool) {
    let mut ptrs = vec![];
    let mut deref_above_outermost = false;
    let mut seen_deref = false;
    let mut e = expr_id;
    loop {
        match &thir.exprs[e].kind {
            ExprKind::Scope { value, .. } => e = *value,
            ExprKind::Field { lhs, .. } => e = *lhs,
            ExprKind::Index { lhs, .. } => e = *lhs,
            ExprKind::PlaceTypeAscription { source, .. }
            | ExprKind::PlaceUnwrapUnsafeBinder { source } => e = *source,
            ExprKind::Deref { arg } => {
                if thir.exprs[*arg].ty.is_raw_ptr() {
                    if ptrs.len() == 0 {
                        deref_above_outermost = seen_deref;
                    }
                    ptrs.push(*arg);
                }
                seen_deref = true;
                e = *arg;
            }
            _ => break,
        }
    }
    (ptrs, deref_above_outermost)
}

/// Called on every (non-overloaded) Deref node.
/// If it's a raw pointer dereference with a permission, record the permission's place.
pub(crate) fn deref_post<'tcx>(
    cx: &mut ThirBuildCx<'tcx>,
    hir_expr: &'tcx hir::Expr<'tcx>,
    kind: &ExprKind<'tcx>,
) {
    let ExprKind::Deref { arg } = kind else {
        return;
    };
    let arg = *arg;
    if !cx.thir.exprs[arg].ty.is_raw_ptr() {
        return;
    }
    let Some(erasure_ctxt) = cx.verus_ctxt.ctxt.clone() else {
        return;
    };
    let Some(perm) = erasure_ctxt.raw_deref_permissions.get(&hir_expr.hir_id) else {
        return;
    };
    if let Some(perm_expr) = permission_place(cx, hir_expr.hir_id, hir_expr.span, perm) {
        cx.verus_ctxt.extra_thir.raw_deref_permissions.insert(arg, perm_expr);
    }
}

/// Construct the THIR place expression for the given permission.
fn permission_place<'tcx>(
    cx: &mut ThirBuildCx<'tcx>,
    hir_id: HirId,
    span: Span,
    perm: &RawDerefPermission,
) -> Option<ExprId> {
    if cx.tcx.hir_enclosing_body_owner(perm.local).to_def_id() != cx.body_owner {
        // TODO(native_raw_ptrs): support this; we'd need to make sure the permission
        // is captured by the closure.
        cx.tcx.dcx().span_err(
            span,
            "Verus does not yet support dereferencing a raw pointer inside a closure using a permission declared outside the closure",
        );
        return None;
    }

    let mut ty = cx.typeck_results.node_type(perm.local);
    let kind = ExprKind::VarRef { id: LocalVarId(perm.local) };
    let mut e = expr_id_from_kind(cx, kind, hir_id, span, ty);

    for proj in perm.projections.iter() {
        (e, ty) = deref_shared_refs(cx, hir_id, span, e, ty);
        match proj {
            PermissionProjection::DerefMut => {
                let TyKind::Ref(_, inner_ty, Mutability::Mut) = ty.kind() else {
                    panic!("Verus Internal Error: permission place: expected &mut type");
                };
                ty = *inner_ty;
                e = expr_id_from_kind(cx, ExprKind::Deref { arg: e }, hir_id, span, ty);
            }
            PermissionProjection::Field { variant, field } => {
                let TyKind::Adt(adt_def, args) = ty.kind() else {
                    panic!("Verus Internal Error: permission place: expected ADT type");
                };
                let variant_index = if adt_def.is_enum() {
                    let Some((idx, _)) = adt_def
                        .variants()
                        .iter_enumerated()
                        .find(|(_, v)| v.name.as_str() == variant.as_str())
                    else {
                        panic!("Verus Internal Error: permission place: variant not found");
                    };
                    idx
                } else {
                    rustc_abi::FIRST_VARIANT
                };
                let variant_def = adt_def.variant(variant_index);
                let Some((name, field_def)) = variant_def
                    .fields
                    .iter_enumerated()
                    .find(|(_, f)| f.name.as_str() == field.as_str())
                else {
                    panic!("Verus Internal Error: permission place: field not found");
                };
                ty = cx.tcx.normalize_erasing_regions(cx.typing_env, field_def.ty(cx.tcx, args));
                let kind = ExprKind::Field { lhs: e, variant_index, name };
                e = expr_id_from_kind(cx, kind, hir_id, span, ty);
            }
        }
    }
    (e, _) = deref_shared_refs(cx, hir_id, span, e, ty);
    Some(e)
}

/// Shared references are implicit in VIR places, so we need to insert the derefs here.
fn deref_shared_refs<'tcx>(
    cx: &mut ThirBuildCx<'tcx>,
    hir_id: HirId,
    span: Span,
    mut e: ExprId,
    mut ty: Ty<'tcx>,
) -> (ExprId, Ty<'tcx>) {
    while let TyKind::Ref(_, inner_ty, Mutability::Not) = ty.kind() {
        ty = *inner_ty;
        e = expr_id_from_kind(cx, ExprKind::Deref { arg: e }, hir_id, span, ty);
    }
    (e, ty)
}

/// Make a fresh copy of a permission place expression (as constructed by `permission_place`)
/// so that we don't use the same ExprId in multiple places in the tree.
fn clone_permission_place<'tcx>(cx: &mut ThirBuildCx<'tcx>, e: ExprId) -> ExprId {
    let mut expr = cx.thir.exprs[e].clone();
    expr.kind = match expr.kind {
        ExprKind::VarRef { id } => ExprKind::VarRef { id },
        ExprKind::Deref { arg } => ExprKind::Deref { arg: clone_permission_place(cx, arg) },
        ExprKind::Field { lhs, variant_index, name } => {
            ExprKind::Field { lhs: clone_permission_place(cx, lhs), variant_index, name }
        }
        _ => panic!("Verus Internal Error: clone_permission_place unexpected kind"),
    };
    cx.thir.exprs.push(expr)
}

/// Record how the outermost raw pointer dereference of the given place is used.
fn record_outer_usage<'tcx>(cx: &mut ThirBuildCx<'tcx>, place: ExprId, usage: PermUsage) {
    let (ptrs, _) = place_raw_derefs(&cx.thir, place);
    if let Some(outer) = ptrs.first() {
        cx.verus_ctxt.extra_thir.raw_deref_outer_usage.insert(*outer, usage);
    }
}

/// Called on an assignment `place = rhs` or `place op= rhs`.
pub(crate) fn assign_post<'tcx>(cx: &mut ThirBuildCx<'tcx>, lhs: ExprId) {
    record_outer_usage(cx, lhs, PermUsage::Write);
}

/// Called on a raw borrow `&raw const place` or `&raw mut place`.
pub(crate) fn raw_borrow_post<'tcx>(
    cx: &mut ThirBuildCx<'tcx>,
    mutability: Mutability,
    arg: ExprId,
) {
    let (ptrs, deref_above_outermost) = place_raw_derefs(&cx.thir, arg);
    if ptrs.len() == 0 {
        return;
    }
    // A raw borrow doesn't access the memory pointed to by the outermost pointer
    // unless we need to go through some other pointer stored in that memory.
    let usage = match (deref_above_outermost, mutability) {
        (false, _) => PermUsage::Skip,
        (true, Mutability::Not) => PermUsage::Read,
        (true, Mutability::Mut) => PermUsage::Write,
    };
    cx.verus_ctxt.extra_thir.raw_deref_outer_usage.insert(ptrs[0], usage);
}

/// Called on a borrow `&place` or `&mut place`.
/// If the outermost raw pointer dereference in `place` has a permission, returns:
///
/// `shared_reference_tie(&place, &perm)` or
/// `mutable_reference_tie(&mut place, mutable_reference_tie(&mut perm, &mut shadow_perm))`
pub(crate) fn borrow_post<'tcx>(
    cx: &mut ThirBuildCx<'tcx>,
    hir_expr: &'tcx hir::Expr<'tcx>,
    ty: Ty<'tcx>,
    kind: &ExprKind<'tcx>,
) -> Option<ExprKind<'tcx>> {
    let ExprKind::Borrow { borrow_kind, arg } = kind else {
        return None;
    };
    let (ptrs, _) = place_raw_derefs(&cx.thir, *arg);
    let outer = *ptrs.first()?;
    let perm = *cx.verus_ctxt.extra_thir.raw_deref_permissions.get(&outer)?;
    let erasure_ctxt = cx.verus_ctxt.ctxt.clone().unwrap();

    let hir_id = hir_expr.hir_id;
    let span = hir_expr.span;
    let region = cx.tcx.lifetimes.re_erased;

    let perm = clone_permission_place(cx, perm);
    let perm_ty = cx.thir.exprs[perm].ty;
    let (perm_borrow, fn_def_id) = match borrow_kind {
        BorrowKind::Mut { kind: MutBorrowKind::TwoPhaseBorrow } => {
            // TODO(native_raw_ptrs): support this
            cx.tcx.dcx().span_err(
                span,
                "Verus does not yet support two-phase borrows from a raw pointer dereference; consider assigning the mutable reference to a variable first",
            );
            return None;
        }
        BorrowKind::Mut { kind: _ } => {
            // `mutable_reference_tie(&mut perm, &mut shadow_perm)`
            let perm_ref_ty = Ty::new_mut_ref(cx.tcx, region, perm_ty);
            let perm_borrow_kind = ExprKind::Borrow {
                borrow_kind: BorrowKind::Mut { kind: MutBorrowKind::Default },
                arg: perm,
            };
            let shadow_kind = crate::verus_time_travel_prevention::shadow_mut_ref_kind(
                cx,
                hir_id,
                span,
                perm_borrow_kind.clone(),
            );
            let perm_borrow = expr_id_from_kind(cx, perm_borrow_kind, hir_id, span, perm_ref_ty);
            let perm_borrow = match shadow_kind {
                None => perm_borrow,
                Some(shadow_kind) => {
                    let shadow = expr_id_from_kind(cx, shadow_kind, hir_id, span, perm_ref_ty);
                    let kind = crate::verus_time_travel_prevention::tie_mut_refs(
                        cx,
                        hir_id,
                        span,
                        perm_borrow,
                        shadow,
                        false,
                    );
                    expr_id_from_kind(cx, kind, hir_id, span, perm_ref_ty)
                }
            };
            (perm_borrow, erasure_ctxt.mutable_reference_tie_fn_def_id)
        }
        BorrowKind::Shared => {
            // `&perm`
            let perm_ref_ty = Ty::new_imm_ref(cx.tcx, region, perm_ty);
            let perm_borrow_kind = ExprKind::Borrow { borrow_kind: BorrowKind::Shared, arg: perm };
            let perm_borrow = expr_id_from_kind(cx, perm_borrow_kind, hir_id, span, perm_ref_ty);
            (perm_borrow, erasure_ctxt.shared_reference_tie_fn_def_id)
        }
        BorrowKind::Fake(_) => {
            return None;
        }
    };

    cx.verus_ctxt.extra_thir.raw_deref_outer_usage.insert(outer, PermUsage::Skip);

    let main_borrow = expr_id_from_kind(cx, kind.clone(), hir_id, span, ty);
    Some(tie_refs(cx, hir_id, span, main_borrow, perm_borrow, fn_def_id))
}

/// Construct `tie_fn(e1, e2)` where `tie_fn` is `mutable_reference_tie` or
/// `shared_reference_tie`
fn tie_refs<'tcx>(
    cx: &mut ThirBuildCx<'tcx>,
    hir_id: HirId,
    span: Span,
    e1: ExprId,
    e2: ExprId,
    fn_def_id: rustc_hir::def_id::DefId,
) -> ExprKind<'tcx> {
    let TyKind::Ref(_, e1_ty_inner, _) = cx.thir.exprs[e1].ty.kind() else { unreachable!() };
    let TyKind::Ref(_, e2_ty_inner, _) = cx.thir.exprs[e2].ty.kind() else { unreachable!() };
    let args = cx.tcx.mk_args(&[GenericArg::from(*e1_ty_inner), GenericArg::from(*e2_ty_inner)]);
    let fn_ty = cx.tcx.mk_ty_from_kind(TyKind::FnDef(fn_def_id, args));
    let fun = expr_id_from_kind(cx, ExprKind::ZstLiteral { user_ty: None }, hir_id, span, fn_ty);
    ExprKind::Call { ty: fn_ty, fun, args: Box::new([e1, e2]), from_hir_call: false, fn_span: span }
}
