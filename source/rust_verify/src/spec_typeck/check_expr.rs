use crate::util::{err_span};
use crate::unsupported_err;
use crate::spec_typeck::State;
use crate::spec_typeck::check_path::PathResolution;
use vir::ast::{Typ, TypX, VarBinderX, ExprX, BinaryOp, CallTarget, Mode, ArithOp, StmtX, IntRange, Constant, FunX, CallTargetKind, AutospecUsage};
use rustc_hir::{Expr, ExprKind, Block, BlockCheckMode, Closure, ClosureBinder, Constness, CaptureBy, FnDecl, ImplicitSelfKind, ClosureKind, Body, PatKind, BindingMode, ByRef, Mutability, BinOpKind, FnRetTy, StmtKind, LetStmt};
use std::sync::Arc;
use vir::ast_util::{unit_typ, int_typ, integer_typ};
use crate::spec_typeck::check_ty::{integer_typ_of_int_ty, integer_typ_of_uint_ty};
use rustc_ast::ast::{LitKind, LitIntType};
use num_bigint::BigInt;
use rustc_span::Span;

impl<'a, 'tcx> State<'a, 'tcx> {
    pub fn check_expr(
        &mut self,
        expr: &'tcx Expr<'tcx>,
    ) -> Result<vir::ast::Expr, vir::ast::VirErr> {
        let bctx = self.bctx;
        let mk_expr = |typ: &Typ, x: ExprX| Ok(bctx.spanned_typed_new(expr.span, typ, x));

        match &expr.kind {
            ExprKind::Path(qpath) => {
                match self.check_qpath_for_expr(qpath, expr.hir_id)? {
                    PathResolution::Local(hir_id) => {
                        match self.tcx.hir_node(hir_id) {
                            rustc_hir::Node::Pat(pat) => {
                                let var = crate::rust_to_vir_expr::pat_to_var(pat)?;
                                let typ = match self.scope_map.get(&var) {
                                    Some(t) => t,
                                    None => {
                                        return err_span(expr.span, format!("unrecognized local `{:}`", var));
                                    }
                                };
                                mk_expr(typ, ExprX::Var(var))
                            }
                            node => {
                                unsupported_err!(expr.span, format!("Path {:?}", node))
                            }
                        }
                    }
                    PathResolution::Fn(def_id, _typ_args) => {
                        let mode = self.get_item_mode(def_id)?;
                        match mode {
                            Mode::Exec => todo!(),
                            Mode::Spec => todo!(),
                            Mode::Proof => todo!(),
                        }
                    }
                    _ => todo!()
                }
            }
            ExprKind::MethodCall(path_segment, receiver, args, span) => {
                let e = self.check_expr(receiver)?;
                let def_id = self.lookup_method_call(path_segment, &e.typ, *span, expr)?;
                dbg!(def_id);
                todo!();
            }
            ExprKind::Call(Expr { kind: ExprKind::Path(qpath), .. }, args) => {
                match self.check_qpath_for_expr(qpath, expr.hir_id)? {
                    PathResolution::Fn(def_id, typ_args) => {
                        let (input_typs, output_typ) = self.fn_item_type_substitution(expr.span,def_id, &typ_args)?;

                        if input_typs.len() != args.len() {
                            return err_span(expr.span, format!("function takes {:} arguments, got {:}", input_typs.len(), args.len()));
                        }

                        let mut vir_args = vec![];
                        for (arg, input_typ) in args.iter().zip(input_typs.iter()) {
                            let vir_arg = self.check_expr(arg)?;
                            self.expect(&vir_arg.typ, input_typ)?;
                            vir_args.push(vir_arg);
                        }

                        let path = crate::rust_to_vir_base::def_id_to_vir_path(self.tcx,
                            &self.bctx.ctxt.verus_items, def_id);
                        let fun = Arc::new(FunX { path: path.clone() });

                        // correct CallTarget is filled in finalizer pass
                        let ct = CallTarget::Fun(
                            CallTargetKind::Static,
                            fun,
                            typ_args,
                            Arc::new(vec![]),
                            AutospecUsage::IfMarked,
                        );

                        mk_expr(&output_typ,
                            ExprX::Call(ct, Arc::new(vir_args))
                        )
                    }
                    _ => todo!(),
                }
            }
            ExprKind::Call(callee, args) => {
                let vir_callee = self.check_expr(callee)?;

                let (callee_arg_typs, callee_ret_typ) = match &*vir_callee.typ {
                    TypX::SpecFn(arg_typs, ret_typ) => {
                        if args.len() != arg_typs.len() {
                            return err_span(expr.span, format!("function takes {:} arguments, got {:}", arg_typs.len(), args.len()));
                        }
                        (arg_typs.clone(), ret_typ.clone())
                    }
                    _ => {
                        let mut args = vec![];
                        for _i in 0 .. args.len() {
                            args.push(self.new_unknown_typ());
                        }
                        let ret = self.new_unknown_typ();
                        let args = Arc::new(args);
                        let t = Arc::new(TypX::SpecFn(args.clone(), ret.clone()));
                        self.expect(&vir_callee.typ, &t)?;
                        (args, ret)
                    }
                };

                let mut vir_args = vec![];
                for (i, arg) in args.iter().enumerate() {
                    let vir_arg = self.check_expr(arg)?;
                    self.expect(&vir_arg.typ, &callee_arg_typs[i])?;
                    vir_args.push(vir_arg);
                }

                let ct = CallTarget::FnSpec(vir_callee);
                mk_expr(&callee_ret_typ, ExprX::Call(ct, Arc::new(vir_args)))
            }
            ExprKind::Block(Block {
              stmts,
              expr,
              hir_id: _,
              rules: BlockCheckMode::DefaultBlock,
              span: _,
              targeted_by_break: _
            }, None) => {
                self.scope_map.push_scope(true);

                let mut vir_stmts = vec![];

                for stmt in stmts.iter() {
                    match &stmt.kind {
                        StmtKind::Let(LetStmt {
                            pat, ty, init: Some(init), els: None, hir_id: _, span: _, source: _
                        }) => {
                            let typ = match ty {
                                None => self.new_unknown_typ(),
                                Some(ty) => self.check_ty(ty)?,
                            };

                            let vir_init = self.check_expr(init)?;
                            self.expect(&vir_init.typ, &typ)?;
                            let pat = self.check_pat(pat, &typ)?;

                            vir_stmts.push(bctx.spanned_new(stmt.span,
                                StmtX::Decl { pattern: pat, mode: Some(Mode::Spec),
                                    init: Some(vir_init) }));
                        }
                        _ => todo!(),
                    }
                }

                let (vir_expr, final_typ) = match expr {
                    None => (None, unit_typ()),
                    Some(expr) => {
                        let vir_expr = self.check_expr(expr)?;
                        (Some(vir_expr.clone()), vir_expr.typ.clone())
                    }
                };

                self.scope_map.pop_scope();

                mk_expr(&final_typ, ExprX::Block(Arc::new(vir_stmts), vir_expr))
            }
            ExprKind::Closure(closure) => {
                let Closure {
                    def_id: _,
                    binder: ClosureBinder::Default,
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
                    unsupported_err!(expr.span, "complex closure");
                };

                let mut arg_typs = vec![];
                for input in inputs.iter() {
                    arg_typs.push(self.check_ty(input)?);
                }
                let output_typ = match output {
                    FnRetTy::DefaultReturn(_span) => self.new_unknown_typ(),
                    FnRetTy::Return(t) => self.check_ty(t)?
                };

                let closure_body = self.tcx.hir().body(*body);
                let Body { params, value: _ } = closure_body;

                self.scope_map.push_scope(false);
                for (i, param) in params.iter().enumerate() {
                    self.check_pat(param.pat, &arg_typs[i])?;
                }
                let body_expr = self.bctx.ctxt.spec_hir.bodies.get(&body).unwrap();
                let body = self.check_expr(body_expr)?;
                self.scope_map.pop_scope();

                self.expect(&body.typ, &output_typ)?;

                let arg_typs = Arc::new(arg_typs);
                let fntype = Arc::new(TypX::SpecFn(arg_typs.clone(), output_typ));
                let mut var_binders = vec![];
                for (i, param) in params.iter().enumerate() {
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
                            unsupported_err!(expr.span, "complex closure pattern argument");
                        }
                    };
                    var_binders.push(Arc::new(VarBinderX { name, a: arg_typs[i].clone() }));
                }

                mk_expr(&fntype, ExprX::Closure(Arc::new(var_binders), body))
            }
            ExprKind::Binary(bin_op, lhs, rhs) => {
                match &bin_op.node {
                    BinOpKind::Sub => {
                        let l = self.check_expr(lhs)?;
                        let r = self.check_expr(rhs)?;
                        self.expect_integer(&l.typ)?;
                        self.expect_integer(&r.typ)?;
                        mk_expr(
                            &int_typ(),
                            ExprX::Binary(BinaryOp::Arith(ArithOp::Sub, Mode::Spec), l, r),
                        )
                    }
                    _ => todo!()
                }
            }
            
            ExprKind::Lit(lit) => match &lit.node {
                LitKind::Int(i, lit_int_type) => {
                    self.lit_int(expr.span,
                        BigInt::from(i.get()),
                        LitIntSuffix::Normal(*lit_int_type))
                }
                _ => todo!()
            }
            _ => {
                unsupported_err!(expr.span, format!("{:?}", expr));
            }
        }
    }

    fn lit_int(&mut self, span: Span, i: num_bigint::BigInt, suffix: LitIntSuffix) -> 
        Result<vir::ast::Expr, vir::ast::VirErr>
    {
        let typ = match suffix {
            LitIntSuffix::Int => integer_typ(IntRange::Int),
            LitIntSuffix::Nat => integer_typ(IntRange::Nat),
            LitIntSuffix::Normal(LitIntType::Unsuffixed) => self.new_unknown_integer_typ(),
            LitIntSuffix::Normal(LitIntType::Signed(s)) => integer_typ_of_int_ty(s),
            LitIntSuffix::Normal(LitIntType::Unsigned(u)) => integer_typ_of_uint_ty(u),
        };
        Ok(self.bctx.spanned_typed_new(span,
            &typ, ExprX::Const(Constant::Int(i))))
    }
}

enum LitIntSuffix {
    Normal(LitIntType),
    Int,
    Nat,
}
