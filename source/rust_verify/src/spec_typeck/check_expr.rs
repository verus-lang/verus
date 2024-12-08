use crate::util::{
    err_span, err_span_bare, slice_vec_map_result, unsupported_err_span, vec_map_result,
};
use crate::spec_typeck::unifier::Unifier;
use crate::{unsupported_err, unsupported_err_unless};
use air::scope_map::ScopeMap;
use vir::ast::{Typ, VarIdent, VirErr};
use rustc_hir::{Expr, ExprKind, Block, BlockCheckMode, Closure, ClosureBinder, Constness, CaptureBy, FnDecl, ImplicitSelfKind, ClosureKind};

pub struct State {
    scope_map: ScopeMap<VarIdent, Typ>,
    unifier: Unifier,
    bctx: crate::context::BodyCtxt,
}

pub fn check_expr<'tcx>(
    tcx: rustc_middle::ty::TyCtxt<'tcx>,
    state: &mut State,
    expr: &Expr<'tcx>,
) -> Result<vir::ast::Expr<'tcx>, vir::ast::VirErr> {
    match &expr.kind {
        ExprKind::Block(Block {
            stmts, expr: e, hir_id: _, rules: BlockCheckMode::DefaultBlock, span: _, targeted_by_break: _ }
        ) => {
            todo!();
        }
        ExprKind::Closure(closure) => {
            let Closure {
                def_id: _,
                binder: ClosureBinder::None,
                constness: Constness::NotConst,
                capture_clause: CaptureBy::Ref,
                bound_generic_params: [],
                fn_decl: FnDecl {
                    inputs, output, c_variadic: false, implicit_self: ImplicitSelfKind::None,
                        lifetime_elision_allowed: _,
                },
                body,
                fn_decl_span: _,
                fn_arg_span: _,
                kind: ClosureKind::Closure
            } = closure else {
                unsupported_err!(&expr.span, "complex closure");
            };

            let mut arg_typs = vec![];
            for input in inputs.iter() {
                arg_typs.push(check_type(tcx, state, input)?);
            }

            let body = bctx.ctxt.spec_hir.bodies.get(&body);
            let Body { params, value, coroutine_kind } = body;
            unsupported_err_unless!(coroutine_kind.is_none(), expr.span, "complex closure");

            state.scope_map.push_scope(false);
            for (i, param) in params.iter().enumerate() {
                check_pat(tcx, state, param.pat, arg_typs[i]);
            }
            let body = check_expr(tcx, state, value);
            state.scope_map.pop_scope();

            let fntype = Arc::new(TypX::SpecFn(Arc::new(arg_typs), body.typ.clone()));
            let var_binders = vec![];
            for (i, param) in params.iter.enumerate() {
                let var = match &param.pat.kind {
                    PatKind::Binding(
                        BindingMode(ByRef::No, Mutability::Not),
                        hir_id,
                        ident,
                        None
                    ) => {
                        local_to_var(ident, hir_id.local_id)
                    }
                    _ => {
                        unsupported_err!(&expr.span, "complex closure pattern argument");
                    }
                };
                var_binders.push(Arc::new(VarBinderX { name, a: arg_types[i].clone() }));
            }

            mk_expr(fntype, ExprX::Closure(Arc::new(var_binders), body))
        }
        ExprKind::Binary(bin_op, lhs, rhs) => {
            match &bin_op.node {
                BinOpKind::Sub => {
                    let l = check_expr(tcx, state, lhs)?;
                    let r = check_expr(tcx, state, rhs)?;
                    self.unifier.expect_integer(&l.typ)?;
                    self.unifier.expect_integer(&r.typ)?;
                    mk_expr(
                        int_typ(),
                        ExprX::BinaryOp(BinaryOp::Sub, l, r),
                    )
                }
            }
        }
        ExprKind::Call(callee, args) => {
            let l = check_expr(tcx, state, callee)?;

            let (callee_arg_typs, callee_ret_typ) = match &l.typ {
                TypX::SpecFn(arg_typs, ret_typ) => {
                    if args.len() != arg_typs.len() {
                        return err_span(&expr.span, format!("function takes {:} arguments, got {:}", callee_arg_typs.len(), args.len()));
                    }
                    (arg_typs, ret_typ)
                }
                _ => {
                    let mut args = vec![];
                    for i in 0 .. args.len() {
                        args.push(self.unifier.new_unif_variable_type());
                    }
                    let ret = self.unifier.new_unif_variable_type();
                    let t = Arc::new(TypX::SpecFn(args, ret));
                    self.unifier.expect(callee, t)?;
                    (args, ret)
                }
            };

            for (i, arg) in args.iter().enumerate() {
                let a = check_expr(tcx, state, arg);
                self.unifier.expect(a, callee_arg_typs)?;
            }

            ret
        }
    }
}
