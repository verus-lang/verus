//! This is used to inject logic in the MIR-builder code.

use crate::builder::{BorrowKind, Builder, PlaceBuilder, Rvalue, Ty, Const, ConstValue, ConstOperand, Operand, UnwindAction, TerminatorKind, CallSource};
use rustc_middle::thir::ExprId;
use rustc_middle::ty::{TyKind, GenericArg};
use std::collections::HashSet;

pub(crate) struct VerusMirBuilderCtxt {
    force_treat_inhabited: HashSet<rustc_middle::mir::BasicBlock>,
}

impl VerusMirBuilderCtxt {
    pub(crate) fn new() -> Self {
        Self { force_treat_inhabited: HashSet::new() }
    }
}

/// Returns true if the return type of this call is uninhabited. Also store the basic block
/// so this can be computed again later.
pub(super) fn record_call_inhabitedness<'a, 'tcx>(
    this: &mut Builder<'a, 'tcx>,
    block: rustc_middle::mir::BasicBlock,
    fun_expr_id: ExprId,
    return_ty: Ty<'tcx>,
) -> bool {
    let Some(extra_thir) = this.verus_extra_thir.clone() else {
        return false;
    };
    if extra_thir.force_treat_inhabited.contains(&fun_expr_id) {
        this.verus_mir_builder_ctxt.force_treat_inhabited.insert(block);
        false
    } else {
        let fun_ty = this.thir.exprs[fun_expr_id].ty;
        let is_inhabited = return_ty.is_inhabited_from(this.tcx, this.parent_module, this.infcx.typing_env(this.param_env));
        !is_inhabited && !func_ty_skip_edge_deletion_for_uninhabited_ty(fun_ty)
    }
}

pub(crate) fn skip_edge_deletion<'a, 'tcx>(verus_mir_builder_ctxt: &VerusMirBuilderCtxt, block: rustc_middle::mir::BasicBlock, ty: Ty<'tcx>) -> bool {
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

/// If before_call_that_doesnt_return is true, this might insert calls and thus change
/// the basic block.
pub(super) fn emit_extra_constraints<'a, 'tcx>(
    this: &mut Builder<'a, 'tcx>,
    block: rustc_middle::mir::BasicBlock,
    expr_id: ExprId,
    before_call_that_doesnt_return: bool,
) -> rustc_middle::mir::BasicBlock {
    let Some(extra_thir) = this.verus_extra_thir.clone() else {
        return block;
    };
    let Some(vars) = extra_thir.local_invs_for_node.get(&expr_id) else {
        return block;
    };
    let Some(erasure_ctxt) = crate::verus::get_verus_erasure_ctxt_option() else {
        return block;
    };
    let mut block = block;
    for l in vars.iter() {
        let source_info = this.source_info(l.span);

        // Typically we say:
        //    tmp: &'_ GuardTy<'_> = &guard;
        // If this is right before a call that doesn't return, we additionally
        // require the lifetime to be static.

        // OutsideGuard refers to match guards; completely unrelated to invariant guards
        let index = this.var_local_id(l.guard_var, crate::builder::ForGuard::OutsideGuard);
        let place = PlaceBuilder::from(index).to_place(this);
        let rvalue = Rvalue::Ref(this.tcx.lifetimes.re_erased, BorrowKind::Shared, place);

        let place_ty = place.ty(&this.local_decls, this.tcx).ty;
        
        let ref_ty = Ty::new_imm_ref(this.tcx, this.tcx.lifetimes.re_erased, place_ty);
        let lhs = this.temp(ref_ty, l.span);

        this.cfg.push_assign(block, source_info, lhs, rvalue);

        if before_call_that_doesnt_return {
            // Insert constraint that the lifetime of the guard is static
            // The easiest way seems to be inserting a call
            // Call builtin::check_static_reference::<Guard<'_>>(guard);

            let fun_ty = this.tcx.mk_ty_from_kind(TyKind::FnDef(erasure_ctxt.check_static_reference_def_id,
                this.tcx.mk_args(&[GenericArg::from(place_ty)])));
            let const_ = Const::Val(ConstValue::ZeroSized, fun_ty);
            let constant = ConstOperand { span: l.span, user_ty: None, const_ };
            let fun = Operand::Constant(Box::new(constant));

            let success = this.cfg.start_new_block();
            let args = Box::new([rustc_span::source_map::Spanned {
                node: Operand::Move(place),
                span: l.span,
            }]);
            let temp_destination = this.temp(Ty::new_tup(this.tcx, &[]), l.span);
            this.record_operands_moved(&*args);
            this.cfg.terminate(
                block,
                source_info,
                TerminatorKind::Call {
                    func: fun,
                    args,
                    unwind: UnwindAction::Unreachable,
                    destination: temp_destination,
                    target: Some(success),
                    call_source: CallSource::Normal,
                    fn_span: l.span,
                });
            this.diverge_from(block);
            block = success;
        }
    }
    block
}
