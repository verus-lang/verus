use crate::builder::{BorrowKind, Builder, PlaceBuilder, Rvalue, Ty};
use rustc_middle::thir::ExprId;

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
