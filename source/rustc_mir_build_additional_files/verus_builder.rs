//! This is used to inject logic in the MIR-builder code.

use crate::builder::{BorrowKind, Builder, PlaceBuilder, Rvalue, Ty};
use rustc_middle::thir::ExprId;
use rustc_middle::ty::TyKind;
use std::collections::HashSet;

pub(crate) struct VerusMirBuilderCtxt {
    force_treat_inhabited: HashSet<rustc_middle::mir::BasicBlock>,
}

impl VerusMirBuilderCtxt {
    pub(crate) fn new() -> Self {
        Self { force_treat_inhabited: HashSet::new() }
    }
}

pub(super) fn record_call_inhabitedness<'a, 'tcx>(
    this: &mut Builder<'a, 'tcx>,
    block: rustc_middle::mir::BasicBlock,
    fun_expr_id: ExprId,
) {
    let Some(extra_thir) = this.verus_extra_thir.clone() else {
        return;
    };
    if extra_thir.force_treat_inhabited.contains(&fun_expr_id) {
        this.verus_mir_builder_ctxt.force_treat_inhabited.insert(block);
    }
}

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
