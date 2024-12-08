use crate::util::{
    err_span, err_span_bare, slice_vec_map_result, unsupported_err_span, vec_map_result,
};
use crate::spec_typeck::unifier::Unifier;
use crate::spec_typeck::State;
use crate::{unsupported_err, unsupported_err_unless};
use air::scope_map::ScopeMap;
use vir::ast::{Typ, VarIdent, VirErr, TypX, VarBinderX, ExprX, BinaryOp, CallTarget};
use rustc_hir::{Expr, ExprKind, Block, BlockCheckMode, Closure, ClosureBinder, Constness, CaptureBy, FnDecl, ImplicitSelfKind, ClosureKind, Body, PatKind, BindingMode, ByRef, Mutability, BinOpKind};
use std::sync::Arc;
use vir::ast_util::int_typ;

impl State<'_> {
    pub fn check_expr<'tcx>(
        &mut self,
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
                    arg_typs.push(self.check_type(input)?);
                }

                let body = self.bctx.ctxt.spec_hir.bodies.get(&body);
                let Body { params, value, coroutine_kind } = body;
                unsupported_err_unless!(coroutine_kind.is_none(), expr.span, "complex closure");

                self.scope_map.push_scope(false);
                for (i, param) in params.iter().enumerate() {
                    self.check_pat(param.pat, arg_typs[i]);
                }
                let body = self.check_expr(value);
                self.scope_map.pop_scope();

                let fntype = Arc::new(TypX::SpecFn(Arc::new(arg_typs), body.typ.clone()));
                let var_binders = vec![];
                for (i, param) in params.iter.enumerate() {
                    let name = match &param.pat.kind {
                        PatKind::Binding(
                            BindingMode(ByRef::No, Mutability::Not),
                            hir_id,
                            ident,
                            None
                        ) => {
                            crate::rust_to_vir_base::local_to_var(ident, hir_id.local_id)
                        }
                        _ => {
                            unsupported_err!(&expr.span, "complex closure pattern argument");
                        }
                    };
                    var_binders.push(Arc::new(VarBinderX { name, a: arg_typs[i].clone() }));
                }

                mk_expr(fntype, ExprX::Closure(Arc::new(var_binders), body))
            }
            ExprKind::Binary(bin_op, lhs, rhs) => {
                match &bin_op.node {
                    BinOpKind::Sub => {
                        let l = self.check_expr(lhs)?;
                        let r = self.check_expr(rhs)?;
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
                let l = self.check_expr(callee)?;

                let (callee_arg_typs, callee_ret_typ) = match &l.typ {
                    TypX::SpecFn(arg_typs, ret_typ) => {
                        if args.len() != arg_typs.len() {
                            return err_span(&expr.span, format!("function takes {:} arguments, got {:}", arg_typs.len(), args.len()));
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

                let mut vir_args = vec![];
                for (i, arg) in args.iter().enumerate() {
                    let a = self.check_expr(arg);
                    self.unifier.expect(a, callee_arg_typs)?;
                    vir_args.push(a);
                }

                let ct = CallTarget::FnSpec(l);
                mk_expr(callee_ret_typ, ExprX::Call(CallTarget::FnSpec(l), Arc::new(args)))
            }
        }
    }
}
