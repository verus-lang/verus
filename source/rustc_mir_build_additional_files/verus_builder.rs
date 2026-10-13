/*! This is used to inject logic in the MIR-builder code.

There are a few reasons we need to modify the MIR:

### Fixing CFG deletions

Typically, the MIR builder deletes CFG edges coming out of function calls that never return,
as judged by the inhabitedness of the return type.
However, Rust may determine some types are uninhabited when they are NOT uninhabited in
Verus's model because of the mode system (e.g. all spec values are inhabited).
Thus, we inject our own check before the builder deletes the edge.

### Emitting constraints for LocalInvariant

An open_local_invariant block looks like this in the macro-expanded source:

```rust
let (guard, mut i) = vstd::invariant::open_atomic_invariant_begin(inv);
{ body ... }
vstd::invariant::open_atomic_invariant_end(guard, i);
```

where `guard: InvariantBlockGuard<'a>`.

We need to keep 'a alive through the entire block. Initially, it seems the easiest
way to do this is just add a constraint that 'a is alive at the
`open_atomic_invariant_end` call (and indeed we do have such a constraint); the problem
is this call might not be reached in the event of nontermination.
Therefore, we need to inject this `'a alive` constraint at enough points in the invariant
body so that some constraint is always reachable.

### Emitting borrows of raw pointer permissions

See verus_raw_ptrs.rs.
*/

use crate::builder::{BasicBlock, BorrowKind, Builder, PlaceBuilder, Rvalue, TerminatorKind, Ty};
use crate::builder::{BlockAnd, BlockAndExtension};
use crate::verus::ExtraThir;
use crate::verus_raw_ptrs::{PermExprs, PermUsage, place_raw_derefs};
use rustc_hir::def_id::DefId;
use rustc_middle::mir::{
    CallSource, Const, ConstOperand, MutBorrowKind, Operand, Place, PlaceElem,
    UnwindAction,
};
use rustc_middle::thir::ExprId;
use rustc_middle::ty::{GenericArg, Mutability, TyKind};
use rustc_hir::LangItem;
use rustc_span::{Span, Spanned, sym};
use std::collections::{HashMap, HashSet};

pub(crate) struct VerusMirBuilderCtxt {
    force_treat_inhabited: HashSet<rustc_middle::mir::BasicBlock>,
    // BasicBlock to the expr id of the call
    bb_to_expr_id: HashMap<rustc_middle::mir::BasicBlock, ExprId>,
}

impl VerusMirBuilderCtxt {
    pub(crate) fn new() -> Self {
        Self { force_treat_inhabited: HashSet::new(), bb_to_expr_id: HashMap::new() }
    }
}

/// The builder calls this when emitting the call into the CFG for the first time.
pub(super) fn record_call_inhabitedness<'a, 'tcx>(
    this: &mut Builder<'a, 'tcx>,
    block: rustc_middle::mir::BasicBlock,
    expr_id: ExprId,
    fun_expr_id: ExprId,
) {
    let Some(extra_thir) = this.verus_extra_thir.clone() else {
        return;
    };
    this.verus_mir_builder_ctxt.bb_to_expr_id.insert(block, expr_id);
    if extra_thir.force_treat_inhabited.contains(&fun_expr_id) {
        this.verus_mir_builder_ctxt.force_treat_inhabited.insert(block);
    }
}

/// The builder calls this when deciding if it should delete the edge.
pub(crate) fn skip_edge_deletion_for_uninhabited_ty<'a, 'tcx>(
    verus_mir_builder_ctxt: &VerusMirBuilderCtxt,
    block: rustc_middle::mir::BasicBlock,
    ty: Ty<'tcx>,
) -> bool {
    func_ty_skip_edge_deletion_for_uninhabited_ty(ty)
        || verus_mir_builder_ctxt.force_treat_inhabited.contains(&block)
}

/// Typically, Rust removes part of the CFG if a function returns an uninhabited type.
/// However, we might have erased code with uninhabited types, e.g.,
/// `erased_ghost_value::<!>()`.
/// To prevent such calls from influencing the CFG, we check if any call is to
/// `erased_ghost_value`, and if so, skip the CFG trimming logic.
pub fn func_ty_skip_edge_deletion_for_uninhabited_ty<'tcx>(ty: Ty<'tcx>) -> bool {
    match ty.kind() {
        TyKind::FnDef(fn_def_id, _) => {
            let Some(erasure_ctxt) = crate::verus::get_verus_erasure_ctxt_option() else {
                return false;
            };
            *fn_def_id == erasure_ctxt.erased_ghost_value_fn_def_id
                || *fn_def_id == erasure_ctxt.shadow_ghost_value_fn_def_id
        }
        _ => false,
    }
}

/// Emit constraints for every open_local_invariant block are currently in.
pub(super) fn emit_extra_constraints<'a, 'tcx>(
    this: &mut Builder<'a, 'tcx>,
    block: rustc_middle::mir::BasicBlock,
    expr_id: ExprId,
) {
    let Some(extra_thir) = this.verus_extra_thir.clone() else {
        return;
    };
    let Some(vars) = extra_thir.local_invs_for_node.get(&expr_id) else {
        return;
    };
    for l in vars.iter() {
        let source_info = this.source_info(l.span);

        // OutsideGuard refers to match guards; completely unrelated to invariant guards
        let index = this.var_local_id(l.guard_var, crate::builder::ForGuard::OutsideGuard);
        let place = PlaceBuilder::from(index).to_place(this);
        let rvalue = Rvalue::Ref(this.tcx.lifetimes.re_erased, BorrowKind::Shared, place);

        let place_ty = place.ty(&this.local_decls, this.tcx).ty;
        let ref_ty = Ty::new_imm_ref(this.tcx, this.tcx.lifetimes.re_erased, place_ty);
        let lhs = this.temp(ref_ty, l.span);

        this.cfg.push_assign(block, source_info, lhs, rvalue);
    }
}

/// If we have a call that never returns, and we want to delete the CFG edge,
/// we need to make sure it doesn't ruin the constraints relating to local_invariant.
///
/// Specifically, if we're in some open_local_invariant block with lifetime `'a`,
/// then `'a` needs to outlive the function lifetime. The only way to make such a constraint
/// is to add an `'a alive` constraint immediately after the call:
///
/// Call(...)
///    |
///    |
///    v
/// [ constraints...; ... ]
///
/// which is what we normally do.
/// However, we can't do this if the Call never returns.
/// Thus, for any Call where we would otherwise want to delete the CFG edge,
/// we instead draw an edge to an infinite-looping basic block that has the
/// necessary constraints:
///
/// Call(...)
///    |
///    |
///    v
/// [ constraints...; goto ]
///    ^                |
///    \                /
///     ----------------
pub(super) fn cfg_removal_fix_constraints<'a, 'tcx>(
    this: &mut Builder<'a, 'tcx>,
    basic_blocks_edited: Vec<usize>,
) {
    for block in basic_blocks_edited.iter() {
        let block = BasicBlock::from_usize(*block);
        cfg_removal_fix_constraints_one_block(this, block);
    }
}

pub(super) fn cfg_removal_fix_constraints_one_block<'a, 'tcx>(
    this: &mut Builder<'a, 'tcx>,
    block: rustc_middle::mir::BasicBlock,
) {
    let Some(extra_thir) = this.verus_extra_thir.clone() else {
        return;
    };
    let Some(expr_id) = this.verus_mir_builder_ctxt.bb_to_expr_id.get(&block) else {
        return;
    };
    let Some(ls) = extra_thir.local_invs_for_node.get(expr_id) else {
        return;
    };
    if ls.len() == 0 {
        return;
    }
    let source_info = this.source_info(ls[0].span);

    let new_block = this.cfg.start_new_block();

    let term = this.cfg.basic_blocks[block].terminator_mut();
    let TerminatorKind::Call { ref mut target, .. } = term.kind else {
        panic!("cfg_removal_fix_constraints_one_block expected Call")
    };
    *target = Some(new_block);

    emit_extra_constraints(this, new_block, *expr_id);

    this.cfg.terminate(new_block, source_info, TerminatorKind::Goto { target: new_block });
}

/// The builder calls this right after building the place for `expr_id` (in preparation
/// for using it). Emit borrows for the permissions of all raw pointer dereferences in the
/// place, and return the place that should be used instead: for the outermost raw pointer
/// dereference, this is the "permission-rooted place" (see verus_raw_ptrs.rs).
pub(super) fn raw_deref_perms_for_place<'a, 'tcx>(
    this: &mut Builder<'a, 'tcx>,
    block: BasicBlock,
    expr_id: ExprId,
    place_builder: PlaceBuilder<'tcx>,
) -> BlockAnd<PlaceBuilder<'tcx>> {
    let Some(extra_thir) = this.verus_extra_thir.clone() else {
        return block.and(place_builder);
    };
    if !extra_thir.check_raw_deref_permissions {
        return block.and(place_builder);
    }
    let (ptrs, _) = place_raw_derefs(&this.thir, expr_id);
    if ptrs.len() == 0 {
        return block.and(place_builder);
    }
    emit_perm_borrows(this, block, &extra_thir, &ptrs[1..]);

    let outer_usage = extra_thir.raw_deref_outer_usage.get(&ptrs[0]).copied();
    let outer_usage = outer_usage.unwrap_or(PermUsage::Read);
    let Some(outer_perm) = get_perm(&extra_thir, ptrs[0]) else {
        return block.and(place_builder);
    };
    if outer_usage == PermUsage::Skip {
        return block.and(place_builder);
    }
    let place = place_builder.to_place(this);
    if outer_usage == PermUsage::Read {
        let place_ty = place.ty(&this.local_decls, this.tcx).ty;
        if !this.tcx.type_is_copy_modulo_regions(this.typing_env(), place_ty) {
            // This is a move, which Rust doesn't allow from behind a raw pointer.
            // Leave the place alone so Rust reports the appropriate error.
            emit_perm_borrows(this, block, &extra_thir, &ptrs[..1]);
            return block.and(PlaceBuilder::from(place));
        }
    }
    let BlockAnd(block, place) = root_at_permission(this, block, outer_perm, place, outer_usage);
    block.and(PlaceBuilder::from(place))
}

/// The builder calls this right before the bounds check for an index expression `base[idx]`
/// (after evaluating `idx`). Emit borrows for the permissions of all raw pointer
/// dereferences in `base` that the bounds check reads through.
pub(super) fn emit_raw_deref_perms_for_bounds_check<'a, 'tcx>(
    this: &mut Builder<'a, 'tcx>,
    block: BasicBlock,
    base: ExprId,
    base_place: &PlaceBuilder<'tcx>,
) {
    let Some(extra_thir) = this.verus_extra_thir.clone() else {
        return;
    };
    if !extra_thir.check_raw_deref_permissions {
        return;
    }
    let (ptrs, deref_above_outermost) = place_raw_derefs(&this.thir, base);
    if ptrs.len() == 0 {
        return;
    }
    let place = base_place.to_place(this);
    let place_ty = place.ty(&this.local_decls, this.tcx).ty;
    let read_outer = match place_ty.kind() {
        // For arrays, the bounds check does a FakeRead of the array place
        TyKind::Array(..) => true,
        // For slices, the bounds check takes a raw pointer to the slice place
        // to get the length (see `len_of_slice_or_array`), so it doesn't need to read through
        // the outermost pointer, unless there's another pointer in between.
        _ => deref_above_outermost,
    };
    if read_outer {
        emit_perm_borrows(this, block, &extra_thir, &ptrs);
    } else {
        emit_perm_borrows(this, block, &extra_thir, &ptrs[1..]);
    }
}

fn get_perm(extra_thir: &ExtraThir, ptr: ExprId) -> Option<PermExprs> {
    match extra_thir.raw_deref_permissions.get(&ptr) {
        None => panic!("Verus Internal Error: raw deref permission not found"),
        Some(perm) => *perm,
    }
}

/// Emit shared borrows of the permissions for the given pointers
/// (ordered from outermost to innermost)
fn emit_perm_borrows<'a, 'tcx>(
    this: &mut Builder<'a, 'tcx>,
    block: BasicBlock,
    extra_thir: &ExtraThir,
    ptrs: &[ExprId],
) {
    for ptr in ptrs.iter().rev() {
        if let Some(perm) = get_perm(extra_thir, *ptr) {
            emit_perm_borrow(this, block, perm.perm, Mutability::Not);
        }
    }
}

/// Emit `tmp = &perm` or `tmp = &mut perm` and return `tmp` and the type of `perm`.
fn emit_perm_borrow<'a, 'tcx>(
    this: &mut Builder<'a, 'tcx>,
    block: BasicBlock,
    perm: ExprId,
    mutbl: Mutability,
) -> (Place<'tcx>, Ty<'tcx>) {
    // The permission place is simple (no index projections, etc.)
    // so this doesn't emit any code.
    let BlockAnd(perm_block, place) = this.as_place(block, perm);
    assert!(perm_block == block);

    let span = this.thir[perm].span;
    let source_info = this.source_info(span);
    let place_ty = place.ty(&this.local_decls, this.tcx).ty;
    let region = this.tcx.lifetimes.re_erased;
    let ref_ty = Ty::new_ref(this.tcx, region, place_ty, mutbl);
    let tmp = this.temp(ref_ty, span);
    let rvalue = Rvalue::Ref(region, borrow_kind_of(mutbl), place);
    this.cfg.push_assign(block, source_info, tmp, rvalue);
    (tmp, place_ty)
}

fn borrow_kind_of(mutbl: Mutability) -> BorrowKind {
    match mutbl {
        Mutability::Not => BorrowKind::Shared,
        Mutability::Mut => BorrowKind::Mut { kind: MutBorrowKind::Default },
    }
}

/// For a place `place` whose outermost raw pointer dereference has permission `perm`,
/// e.g., `(*p).z`, emit:
///
/// ```rust
/// _ = &(*p).z;
/// t = PointsTo::borrow(&perm);
/// ```
///
/// (or the `mut` versions) and return the permission-rooted place `(*t).z`.
/// See verus_raw_ptrs.rs.
fn root_at_permission<'a, 'tcx>(
    this: &mut Builder<'a, 'tcx>,
    mut block: BasicBlock,
    perm: PermExprs,
    place: Place<'tcx>,
    usage: PermUsage,
) -> BlockAnd<Place<'tcx>> {
    let tcx = this.tcx;
    let erasure_ctxt = crate::verus::get_verus_erasure_ctxt_option().unwrap();
    let span = this.thir[perm.perm].span;
    let source_info = this.source_info(span);
    let region = tcx.lifetimes.re_erased;
    let place_ty = place.ty(&this.local_decls, tcx).ty;
    let mutbl = match usage {
        PermUsage::Read | PermUsage::BorrowShared => Mutability::Not,
        PermUsage::Write | PermUsage::BorrowMut => Mutability::Mut,
        PermUsage::Skip => unreachable!(),
    };

    // The projection index of the outermost raw pointer dereference
    let Some(outer_deref_idx) = place
        .iter_projections()
        .filter(|(base, elem)| {
            *elem == PlaceElem::Deref && base.ty(&this.local_decls, tcx).ty.is_raw_ptr()
        })
        .map(|(base, _)| base.projection.len())
        .last()
    else {
        panic!("Verus Internal Error: root_at_permission expected raw pointer dereference");
    };

    // `_ = &place` or `_ = &mut place`
    // Since we don't use the original place itself, we need to access it to make sure it's
    // available (e.g., all the locals involved are initialized).
    // Note that this borrow should only be momentary; we don't want to force lifetimes
    // behind the pointer to outlive anything.
    let place_ref = this.temp(Ty::new_ref(tcx, region, place_ty, mutbl), span);
    let rvalue = Rvalue::Ref(region, borrow_kind_of(mutbl), place);
    this.cfg.push_assign(block, source_info, place_ref, rvalue);

    // `&perm` or `&mut perm`
    let (mut perm_ref, mut perm_ty) = emit_perm_borrow(this, block, perm.perm, mutbl);
    if usage == PermUsage::BorrowMut
        && let Some(shadow) = perm.shadow
    {
        // `mutable_reference_tie(&mut perm, &mut shadow_perm)`
        let (shadow_ref, shadow_ty) = emit_perm_borrow(this, block, shadow, mutbl);
        let res;
        BlockAnd(block, res) = emit_call(
            this,
            block,
            erasure_ctxt.mutable_reference_tie_fn_def_id,
            &[perm_ty, shadow_ty],
            vec![Operand::Move(perm_ref), Operand::Move(shadow_ref)],
            Ty::new_mut_ref(tcx, region, perm_ty),
            span,
        );
        perm_ref = res;
    }

    // The permission may be wrapped in `Tracked`
    // (see `cutoff_at_tracked_unwrap` in erase.rs).
    // `Deref::deref(perm_ref)` or `DerefMut::deref_mut(perm_ref)`
    while let TyKind::Adt(adt_def, args) = perm_ty.kind()
        && adt_def.did() == erasure_ctxt.tracked_struct_def_id
    {
        let (trait_item, method_name) = match mutbl {
            Mutability::Not => (LangItem::Deref, sym::deref),
            Mutability::Mut => (LangItem::DerefMut, sym::deref_mut),
        };
        let trait_def_id = tcx.require_lang_item(trait_item, span);
        let Some(deref_fn) = tcx
            .associated_items(trait_def_id)
            .filter_by_name_unhygienic(method_name)
            .find(|item| item.is_fn())
        else {
            panic!("Verus Internal Error: deref method not found");
        };
        let inner_ty = args.type_at(0);
        let res;
        BlockAnd(block, res) = emit_call(
            this,
            block,
            deref_fn.def_id,
            &[perm_ty],
            vec![Operand::Move(perm_ref)],
            Ty::new_ref(tcx, region, inner_ty, mutbl),
            span,
        );
        perm_ref = res;
        perm_ty = inner_ty;
    }

    let TyKind::Adt(adt_def, perm_args) = perm_ty.kind() else {
        panic!("Verus Internal Error: expected PointsTo type for permission");
    };
    if Some(adt_def.did()) != erasure_ctxt.points_to_struct_def_id {
        // This can happen if the permission is inside a `Tracked` wrapper but not
        // directly, e.g., `Tracked<Option<PointsTo<T>>>`.
        // TODO(native_raw_ptrs): handle this; for now, we are imprecise about lifetimes
        // and just use the original place.
        return block.and(place);
    }

    // `t = PointsTo::borrow(perm_ref)` or `t = PointsTo::borrow_mut(perm_ref)`
    let pointee_ty = perm_args.type_at(0);
    let borrow_fn = match mutbl {
        Mutability::Not => erasure_ctxt.points_to_borrow_fn_def_id,
        Mutability::Mut => erasure_ctxt.points_to_borrow_mut_fn_def_id,
    };
    let Some(borrow_fn) = borrow_fn else {
        panic!("Verus Internal Error: vstd::raw_ptr::PointsTo::borrow not found");
    };
    let t;
    BlockAnd(block, t) = emit_call(
        this,
        block,
        borrow_fn,
        &[pointee_ty],
        vec![Operand::Move(perm_ref)],
        Ty::new_ref(tcx, region, pointee_ty, mutbl),
        span,
    );

    // The permission-rooted place, e.g., `(*t).z`
    // This reuses the projections from the original place (including index locals).
    let mut projection = vec![PlaceElem::Deref];
    projection.extend_from_slice(&place.projection[outer_deref_idx + 1..]);
    block.and(Place { local: t.local, projection: tcx.mk_place_elems(&projection) })
}

/// Emit a call `dest = f::<ty_args>(args)` and return `dest`.
fn emit_call<'a, 'tcx>(
    this: &mut Builder<'a, 'tcx>,
    block: BasicBlock,
    fn_def_id: DefId,
    ty_args: &[Ty<'tcx>],
    args: Vec<Operand<'tcx>>,
    ret_ty: Ty<'tcx>,
    span: Span,
) -> BlockAnd<Place<'tcx>> {
    let tcx = this.tcx;
    let fn_ty = Ty::new_fn_def(tcx, fn_def_id, ty_args.iter().map(|t| GenericArg::from(*t)));
    let const_ = Const::zero_sized(fn_ty);
    let func = Operand::Constant(Box::new(ConstOperand { span, user_ty: None, const_ }));
    let args = args.into_iter().map(|node| Spanned { node, span }).collect();
    let destination = this.temp(ret_ty, span);
    let success = this.cfg.start_new_block();
    let source_info = this.source_info(span);
    let kind = TerminatorKind::Call {
        func,
        args,
        unwind: UnwindAction::Unreachable,
        destination,
        target: Some(success),
        call_source: CallSource::Misc,
        fn_span: span,
    };
    this.cfg.terminate(block, source_info, kind);
    success.and(destination)
}
