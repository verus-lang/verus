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
use crate::verus::ExtraThir;
use crate::verus_raw_ptrs::{PermUsage, place_raw_derefs};
use crate::builder::BlockAnd;
use rustc_middle::mir::MutBorrowKind;
use rustc_middle::thir::ExprId;
use rustc_middle::ty::TyKind;
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
/// place.
pub(super) fn emit_raw_deref_perms_for_place<'a, 'tcx>(
    this: &mut Builder<'a, 'tcx>,
    block: BasicBlock,
    expr_id: ExprId,
) {
    let Some(extra_thir) = this.verus_extra_thir.clone() else {
        return;
    };
    if extra_thir.raw_deref_permissions.len() == 0 {
        return;
    }
    let (ptrs, _) = place_raw_derefs(&this.thir, expr_id);
    if ptrs.len() == 0 {
        return;
    }
    let outer_usage = extra_thir.raw_deref_outer_usage.get(&ptrs[0]).copied();
    emit_raw_deref_perms(this, block, &extra_thir, &ptrs, outer_usage.unwrap_or(PermUsage::Read));
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
    if extra_thir.raw_deref_permissions.len() == 0 {
        return;
    }
    let (ptrs, deref_above_outermost) = place_raw_derefs(&this.thir, base);
    if ptrs.len() == 0 {
        return;
    }
    let place = base_place.to_place(this);
    let place_ty = place.ty(&this.local_decls, this.tcx).ty;
    let outer_usage = match place_ty.kind() {
        // For arrays, the bounds check does a FakeRead of the array place
        TyKind::Array(..) => PermUsage::Read,
        // For slices, the bounds check takes a raw pointer to the slice place
        // to get the length (see `len_of_slice_or_array`), so it doesn't need to read through
        // the outermost pointer, unless there's another pointer in between.
        _ => {
            if deref_above_outermost {
                PermUsage::Read
            } else {
                PermUsage::Skip
            }
        }
    };
    emit_raw_deref_perms(this, block, &extra_thir, &ptrs, outer_usage);
}

/// `ptrs` is ordered from outermost to innermost.
/// Inner pointers always get a `Read` and the outermost gets `outer_usage`.
fn emit_raw_deref_perms<'a, 'tcx>(
    this: &mut Builder<'a, 'tcx>,
    block: BasicBlock,
    extra_thir: &ExtraThir,
    ptrs: &[ExprId],
    outer_usage: PermUsage,
) {
    for (i, ptr) in ptrs.iter().enumerate().rev() {
        let usage = if i == 0 { outer_usage } else { PermUsage::Read };
        let Some(perm) = extra_thir.raw_deref_permissions.get(ptr) else {
            continue;
        };
        let borrow_kind = match usage {
            PermUsage::Read => BorrowKind::Shared,
            PermUsage::Write => BorrowKind::Mut { kind: MutBorrowKind::Default },
            PermUsage::Skip => continue,
        };

        // The permission place is simple (no index projections, etc.)
        // so this doesn't emit any code.
        let BlockAnd(perm_block, place) = this.as_place(block, *perm);
        assert!(perm_block == block);

        let span = this.thir[*perm].span;
        let source_info = this.source_info(span);
        let place_ty = place.ty(&this.local_decls, this.tcx).ty;
        let region = this.tcx.lifetimes.re_erased;
        let ref_ty = match usage {
            PermUsage::Write => Ty::new_mut_ref(this.tcx, region, place_ty),
            _ => Ty::new_imm_ref(this.tcx, region, place_ty),
        };
        let lhs = this.temp(ref_ty, span);
        this.cfg.push_assign(block, source_info, lhs, Rvalue::Ref(region, borrow_kind, place));
    }
}
