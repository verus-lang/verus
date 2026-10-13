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
(for `a`, `(*a).x`, and `(*(*a).x).y`), the inner pointers `a` and `(*a).x` are only read,
so we emit `_ = &Perm_A; _ = &Perm_B;`.

The outermost permission `Perm_C: PointsTo<T>` is used depending on how the place is used.
It's not enough to just borrow `Perm_C`; we also need the type `T` (in particular, any
lifetimes in `T`) to determine the type of the value being read, written, or borrowed,
since the type of the pointee `*(*(*a).x).y` is irrelevant. (A raw pointer `*mut &'a u64`
might point to memory that actually contains a `&'static u64` or vice versa; the `PointsTo`
determines which.)
Thus we construct a "permission-rooted place", replacing the pointer dereference
with a dereference of the permission's contents, and use it in place of the original:

```rust
// Copy
_ = &Perm_A; _ = &Perm_B;
t1 = &(*(*(*a).x).y).z;
t2 = PointsTo::borrow(&Perm_C);                                 // t2: &T
t = shared_reference_tie(t2, t1);                               // t: &T
m = copy (*t).z;

// Assign
_ = &Perm_A; _ = &Perm_B;
t1 = &mut (*(*(*a).x).y).z;
t2 = PointsTo::borrow_mut(&mut Perm_C);                         // t2: &mut T
t = mutable_reference_tie(t2, t1);                              // t: &mut T
(*t).z = ...;

// Shared borrow
_ = &Perm_A; _ = &Perm_B;
t1 = &(*(*(*a).x).y).z;
t2 = PointsTo::borrow(&Perm_C);
t = shared_reference_tie(t2, t1);
r = &(*t).z;

// Mutable borrow
_ = &Perm_A; _ = &Perm_B;
t1 = &mut (*(*(*a).x).y).z;
t2 = PointsTo::borrow_mut(mutable_reference_tie(&mut Perm_C, &mut Shadow_Perm_C));
t = mutable_reference_tie(t2, t1);
r = &mut (*t).z;

// Raw borrow
_ = &Perm_A; _ = &Perm_B;
r = &raw (*(*(*a).x).y).z;
```

Here `*_reference_tie<'a, T, U>(&'a T, &'a U) -> &'a T` returns its first argument,
so the type of the value read, written, or borrowed is determined by the permission,
while the lifetime of the result is tied to both the permission and the original place.
Note that the permission-rooted place reuses the projections from the original place
(e.g., `.z`, including any index locals) so there is no re-evaluation of any expressions.

If the permission is inside a `Tracked` (e.g., `Tracked<Option<PointsTo<T>>>`), then getting
to the `T` requires calls to `Tracked::deref` / `Tracked::deref_mut` as well.
(See `RawDerefPermissions::outermost` and `PermissionProjection`.)

(Note that the ordinary Rust borrow-checking on exec code, which runs separately,
uses the pointer's type.)

Notes:

 * For raw borrows, whether we emit a permission for the outermost raw pointer
   depends on whether the pointer is read or not.
   If the raw deref is the outermost deref, then we're only doing
   pointer arithmetic and there's no actual read from the pointer.
   (Indeed, Rust does not even consider this an unsafe operation.)
   If there's another safe deref after the last raw deref,
   then we do need to read from the pointer and thus we need the permission for it.)

 * We don't have to handle moves, since Rust disallows moving from behind a raw pointer.
   The user has to use something like `ptr::read` to do this, you can't just move by writing
   `let m = *p`.

### Implementation

Our lowering is split across THIR construction and MIR building:

 * During THIR construction (this file), for each raw deref `*p`, we construct a
   THIR place expression for its permission, recorded in `ExtraThir::raw_deref_permissions`
   (keyed by the ExprId of `p`).
   For any usage of the outermost pointer other than reading, we record the usage in
   `ExtraThir::raw_deref_outer_usage`.
   It should be the case that if a place expression does not get registered here during the THIR
   pass, then it is a copy, thus requiring read permissions.

 * During MIR building (verus_builder.rs), whenever we build a place (or perform a bounds
   check on an intermediate place), we emit the borrows of the permissions immediately
   before the place is used (and for the final use, replace the place with the
   permission-rooted place). This is important since a single THIR place expression
   may be used by multiple MIR statements (e.g., bounds checks), and there may be user code
   (e.g., index expressions) running in between.
*/

use crate::thir::cx::ThirBuildCx;
use crate::verus::{PermissionProjection, RawDerefPermission, expr_id_from_kind};
use rustc_hir as hir;
use rustc_hir::HirId;
use rustc_middle::mir::{BorrowKind, MutBorrowKind};
use rustc_middle::thir::{ExprId, ExprKind, LocalVarId, Thir};
use rustc_abi::{FieldIdx, VariantIdx};
use rustc_middle::ty::{Mutability, Ty, TyCtxt, TyKind, TypingEnv};
use rustc_span::Span;

/// How a permission is used (i.e., what kind of borrow we emit for it).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PermUsage {
    /// Shared borrow of the permission (for a copy of the place; this is the default)
    Read,
    /// Shared borrow of the permission (for a shared borrow of the place)
    BorrowShared,
    /// Mutable borrow of the permission (for an assignment)
    Write,
    /// Mutable borrow of the permission, tied to the permission's shadow place
    /// (for a mutable borrow of the place; see verus_time_travel_prevention.rs)
    BorrowMut,
    /// Don't emit anything for this permission, because the usage doesn't require it
    Skip,
}

/// The THIR place expressions for a permission.
#[derive(Debug, Clone)]
pub struct PermExprs {
    /// The permission (of type `PointsTo<T>`, or a `Tracked` wrapper containing it);
    /// see `RawDerefPermissions::perm`
    pub perm: ExprId,
    /// The shadow place of the permission, if any
    pub shadow: Option<ExprId>,
    /// The remaining projections needed to get from `perm` to the `T` in `PointsTo<T>`;
    /// these are applied by the MIR builder, which emits calls for the non-place projections.
    /// (See `RawDerefPermissions::outermost`)
    pub outermost_suffix: Vec<PermissionProjection>,
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
    if !cx.verus_ctxt.extra_thir.check_raw_deref_permissions {
        return;
    }
    let erasure_ctxt = cx.verus_ctxt.ctxt.clone().unwrap();
    let Some(perm) = erasure_ctxt.raw_deref_permissions.get(&hir_expr.hir_id) else {
        panic!("Verus Internal Error: raw deref permission not found");
    };
    let perm_exprs = match perm {
        None => None,
        Some(perms) => permission_place(cx, hir_expr.hir_id, hir_expr.span, &perms.perm).map(|perm| {
            let shadow = if cx.verus_ctxt.do_time_travel_prevention {
                crate::verus_time_travel_prevention::shadow_place(
                    cx,
                    hir_expr.hir_id,
                    hir_expr.span,
                    perm,
                )
            } else {
                None
            };
            let n = perms.perm.projections.len();
            assert!(perms.outermost.local == perms.perm.local);
            assert!(perms.outermost.projections[..n] == perms.perm.projections[..]);
            let outermost_suffix = perms.outermost.projections[n..].to_vec();
            PermExprs { perm, shadow, outermost_suffix }
        }),
    };
    cx.verus_ctxt.extra_thir.raw_deref_permissions.insert(arg, perm_exprs);
}

/// Construct the THIR place expression for the given permission.
/// Returns None (after emitting an error) if unsupported.
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
            "Verus does not support dereferencing a raw pointer inside a closure using a permission declared outside the closure",
        );
        return None;
    }

    let mut ty = cx.typeck_results.node_type(perm.local);
    let kind = ExprKind::VarRef { id: LocalVarId(perm.local) };
    let mut e = expr_id_from_kind(cx, kind, hir_id, span, ty);

    for proj in perm.projections.iter() {
        match proj {
            PermissionProjection::DerefMut => {
                let TyKind::Ref(_, inner_ty, Mutability::Mut) = ty.kind() else {
                    panic!("Verus Internal Error: permission place: expected &mut type");
                };
                ty = *inner_ty;
                e = expr_id_from_kind(cx, ExprKind::Deref { arg: e }, hir_id, span, ty);
            }
            PermissionProjection::DerefShared => {
                let TyKind::Ref(_, inner_ty, Mutability::Not) = ty.kind() else {
                    panic!("Verus Internal Error: permission place: expected & type");
                };
                ty = *inner_ty;
                e = expr_id_from_kind(cx, ExprKind::Deref { arg: e }, hir_id, span, ty);
            }
            PermissionProjection::DerefBox => {
                let Some(inner_ty) = ty.boxed_ty() else {
                    panic!("Verus Internal Error: permission place: expected Box type");
                };
                ty = inner_ty;
                e = expr_id_from_kind(cx, ExprKind::Deref { arg: e }, hir_id, span, ty);
            }
            PermissionProjection::Field { variant, field } => {
                let (_, variant_index, name, field_ty) =
                    resolve_field(cx.tcx, cx.typing_env, ty, variant, field);
                ty = field_ty;
                let kind = ExprKind::Field { lhs: e, variant_index, name };
                e = expr_id_from_kind(cx, kind, hir_id, span, ty);
            }
            PermissionProjection::DerefTracked | PermissionProjection::DerefPointsTo => {
                panic!("Verus Internal Error: permission place: unexpected projection");
            }
        }
    }
    Some(e)
}

/// Look up the given field (by name) of the given ADT type.
/// Returns (is_enum, variant index, field index, field type).
pub(crate) fn resolve_field<'tcx>(
    tcx: TyCtxt<'tcx>,
    typing_env: TypingEnv<'tcx>,
    ty: Ty<'tcx>,
    variant: &str,
    field: &str,
) -> (bool, VariantIdx, FieldIdx, Ty<'tcx>) {
    let TyKind::Adt(adt_def, args) = ty.kind() else {
        panic!("Verus Internal Error: permission place: expected ADT type");
    };
    let variant_index = if adt_def.is_enum() {
        let Some((idx, _)) =
            adt_def.variants().iter_enumerated().find(|(_, v)| v.name.as_str() == variant)
        else {
            panic!("Verus Internal Error: permission place: variant not found");
        };
        idx
    } else {
        rustc_abi::FIRST_VARIANT
    };
    let variant_def = adt_def.variant(variant_index);
    let Some((field_index, field_def)) =
        variant_def.fields.iter_enumerated().find(|(_, f)| f.name.as_str() == field)
    else {
        panic!("Verus Internal Error: permission place: field not found");
    };
    let field_ty = tcx.normalize_erasing_regions(typing_env, field_def.ty(tcx, args));
    (adt_def.is_enum(), variant_index, field_index, field_ty)
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
pub(crate) fn borrow_post<'tcx>(
    cx: &mut ThirBuildCx<'tcx>,
    hir_expr: &'tcx hir::Expr<'tcx>,
    kind: &ExprKind<'tcx>,
) {
    let ExprKind::Borrow { borrow_kind, arg } = kind else {
        return;
    };
    let (ptrs, _) = place_raw_derefs(&cx.thir, *arg);
    let Some(outer) = ptrs.first() else {
        return;
    };
    let usage = match borrow_kind {
        BorrowKind::Mut { kind: MutBorrowKind::TwoPhaseBorrow } => {
            if let Some(Some(_)) = cx.verus_ctxt.extra_thir.raw_deref_permissions.get(outer) {
                // TODO(native_raw_ptrs): support this
                cx.tcx.dcx().span_err(
                    hir_expr.span,
                    "Verus does not yet support two-phase borrows from a raw pointer dereference; consider assigning the mutable reference to a variable first",
                );
            }
            PermUsage::BorrowMut
        }
        BorrowKind::Mut { kind: _ } => PermUsage::BorrowMut,
        BorrowKind::Shared => PermUsage::BorrowShared,
        BorrowKind::Fake(_) => {
            return;
        }
    };
    record_outer_usage(cx, *arg, usage);
}
