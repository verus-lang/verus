struct State {
    scope_map: ScopeMap<VarIdent, Typ>,
    unifier: Unifier,
}

fn check_expr<'tcx>(
    tcx: rustc_middle::ty::TyCtxt<'tcx>,
    state: &mut State,
    expr: &Expr<'tcx>,
) -> Result<vir::ast::Expr<'tcx>, VirErr> {
    match &expr.kind {
        ExprKind::
        ExprKind::Block(Block { stmts, expr: e, hir_id: _, rules: BlockCheckMode::DefaultBlock, span: _, targeted_by_break: _ }) => {
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
            }

            for (i, arg) in args.iter().enumerate() {
                let a = check_expr(tcx, state, arg);
                self.unifier.expect(a, callee_arg_typs)?;
            }

            ret
        }
    }
}

}
