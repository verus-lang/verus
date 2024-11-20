use crate::util::{err_span};
use crate::verus_items;
use crate::{unsupported_err, unsupported_err_unless};
use crate::spec_typeck::State;
use crate::spec_typeck::check_path::PathResolution;
use vir::ast::{BitwiseOp, NullaryOpr, Typ, TypX, VarBinderX, ExprX, BinaryOp, CallTarget, Mode, ArithOp, StmtX, IntRange, Constant, FunX, CallTargetKind, AutospecUsage, Dt, Ident, VirErr, InequalityOp, Typs, FieldOpr, VariantCheck, UnaryOpr, TypDecoration, ArmX, PatternX, IntegerTypeBitwidth, UnaryOp};
use rustc_hir::{Expr, ExprKind, Block, BlockCheckMode, Closure, ClosureBinder, Constness, CaptureBy, FnDecl, ImplicitSelfKind, ClosureKind, Body, PatKind, BindingMode, ByRef, Mutability, BinOpKind, FnRetTy, StmtKind, LetStmt, ExprField, PatField, UnOp, LetExpr, BorrowKind};
use std::sync::Arc;
use vir::ast_util::{unit_typ, int_typ, integer_typ, bool_typ, nat_typ, typ_to_diagnostic_str, mk_bool};
use crate::spec_typeck::check_ty::{integer_typ_of_int_ty, integer_typ_of_uint_ty};
use rustc_ast::ast::{LitKind, LitIntType};
use num_bigint::BigInt;
use rustc_span::Span;
use vir::def::{field_ident_from_rust, positional_field_ident};
use air::ast_util::{ident_binder, str_ident};
use rustc_hir::def_id::DefId;
use rustc_middle::ty::{AdtDef, VariantDef};
use std::collections::HashSet;
use rustc_hir::def::CtorKind;
use crate::verus_items::VerusItem;
use rustc_hir::QPath;
use rustc_hir::def::Res;
use crate::spec_typeck::method_probe::AutorefOrPtrAdjustment;
use crate::rust_to_vir_expr::mk_ty_clip;

impl<'a, 'tcx> State<'a, 'tcx> {
    /// Type-check the given expression and returns its type.

    pub fn check_expr(
        &mut self,
        expr: &'tcx Expr<'tcx>,
    ) -> Result<vir::ast::Expr, VirErr> {
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
                    PathResolution::Datatype(def_id, typ_args) => {
                        let adt_def = self.tcx.adt_def(def_id);
                        if adt_def.is_enum() {
                            return err_span(expr.span, format!("expected function, tuple struct or tuple variant, found enum `{:}`", self.def_id_to_friendly(def_id)));
                        }
                        if adt_def.is_union() {
                            return err_span(expr.span, format!("expected function, tuple struct or tuple variant, found union `{:}`", self.def_id_to_friendly(def_id)));
                        }
                        assert!(adt_def.is_struct());

                        // TODO visibility of fields ...

                        let variant_def = adt_def.non_enum_variant();

                        let variant_name = str_ident(&variant_def.ident(self.tcx).as_str());
                        self.const_ctor(expr.span, &typ_args, variant_def, &adt_def, variant_name)
                    }
                    PathResolution::DatatypeVariant(variant_def_id, typ_args) => {
                        // TODO visibility of fields ...
                        let enum_did = self.tcx.parent(variant_def_id);
                        let adt_def = self.tcx.adt_def(enum_did);
                        assert!(adt_def.is_enum());
                        let variant_def = adt_def.variant_with_id(variant_def_id);

                        let variant_name = str_ident(&variant_def.ident(self.tcx).as_str());
                        self.const_ctor(expr.span, &typ_args, variant_def, &adt_def, variant_name)
                    }
                    PathResolution::TyParam(ident) => {
                        let const_param_typ = self.typ_of_const_param(expr.span, &ident)?;
                        mk_expr(&const_param_typ, ExprX::NullaryOpr(NullaryOpr::ConstGeneric(
                            Arc::new(TypX::TypParam(ident)))))
                    }
                    pr => {
                        dbg!(pr);
                        todo!()
                    }
                }
            }
            ExprKind::MethodCall(path_segment, receiver, args, span) => {
                let e = self.check_expr(receiver)?;
                let mut self_typ = e.typ.clone();
                let (mres, typ_args) = self.lookup_method_call(path_segment, &self_typ, *span, expr)?;
                let def_id = mres.def_id;

                for _i in 0 .. mres.num_autoderefs {
                    self_typ = match &*self_typ {
                        TypX::Decorate(TypDecoration::Ref | TypDecoration::MutRef | TypDecoration::Box | TypDecoration::Rc | TypDecoration::Arc | TypDecoration::Ghost | TypDecoration::Tracked, None, t) => t.clone(),
                        _ => {
                            return err_span(expr.span, format!("in spec code, Verus cannot apply auto-deref to this type: {:}", typ_to_diagnostic_str(&self_typ)));
                        }
                    };
                }

                match mres.autoref_or_ptr_adjustment {
                    None => { }
                    Some(AutorefOrPtrAdjustment::Autoref { mutbl: rustc_hir::Mutability::Not, unsize: false }) => {
                        self_typ = Arc::new(TypX::Decorate(TypDecoration::Ref, None, self_typ));
                    }
                    _ => todo!()
                }

                let (input_typs, output_typ) = self.fn_item_type_substitution(expr.span, def_id, &typ_args)?;

                if input_typs.len() != args.len() + 1 {
                    return err_span(expr.span, format!("function takes {:} arguments, got {:}", input_typs.len(), args.len()));
                }
                
                let mut vir_args = vec![];

                self.expect_exact(&self_typ, &input_typs[0])?;
                vir_args.push(e);

                for (arg, input_typ) in args.iter().zip(input_typs.iter().skip(1)) {
                    let vir_arg = self.check_expr(arg)?;
                    self.expect_allowing_coercion(&vir_arg.typ, input_typ)?;
                    vir_args.push(vir_arg);
                }
                let vir_args = Arc::new(vir_args);

                if let Some(verus_item) = self.bctx.ctxt.get_verus_item(def_id) {
                    let e = self.check_call_verus_item_late(def_id, verus_item, expr, &vir_args, &typ_args, &output_typ)?;
                    if let Some(e) = e {
                        return Ok(e);
                    }
                }

                self.handle_call_traits(def_id, &typ_args)?;

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
                    ExprX::Call(ct, vir_args)
                )
            }
            ExprKind::Call(Expr { kind: ExprKind::Path(qpath), .. }, args) => {
                if let QPath::Resolved(_qualified_self, path) = qpath {
                    if let Res::Def(_, def_id) = &path.res {
                        if let Some(verus_item) = self.bctx.ctxt.get_verus_item(*def_id) {
                            let args: Vec<&'tcx Expr<'tcx>> = args.iter().collect();
                            let e = self.check_call_verus_item_early(*def_id, verus_item, expr, &args)?;
                            if let Some(e) = e {
                                return Ok(e);
                            }
                        }
                    };
                }
                match self.check_qpath_for_expr(qpath, expr.hir_id)? {
                    PathResolution::Fn(def_id, typ_args) => {
                        if let Some(rust_item) = verus_items::get_rust_item(self.tcx, def_id) {
                            return self.check_call_rust_item(rust_item);
                        }

                        let (input_typs, output_typ) = self.fn_item_type_substitution(expr.span,def_id, &typ_args)?;

                        if input_typs.len() != args.len() {
                            return err_span(expr.span, format!("function takes {:} arguments, got {:}", input_typs.len(), args.len()));
                        }

                        let mut vir_args = vec![];
                        for (arg, input_typ) in args.iter().zip(input_typs.iter()) {
                            let vir_arg = self.check_expr(arg)?;
                            self.expect_allowing_coercion(&vir_arg.typ, input_typ)?;
                            vir_args.push(vir_arg);
                        }
                        let vir_args = Arc::new(vir_args);

                        self.handle_call_traits(def_id, &typ_args)?;

                        if let Some(verus_item) = self.bctx.ctxt.get_verus_item(def_id) {
                            let e = self.check_call_verus_item_late(def_id, verus_item, expr, &vir_args, &typ_args, &output_typ)?;
                            if let Some(e) = e {
                                return Ok(e);
                            }
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
                            ExprX::Call(ct, vir_args)
                        )
                    }
                    PathResolution::Datatype(def_id, typ_args) => {
                        let adt_def = self.tcx.adt_def(def_id);
                        if adt_def.is_enum() {
                            return err_span(expr.span, format!("expected function, tuple struct or tuple variant, found enum `{:}`", self.def_id_to_friendly(def_id)));
                        }
                        if adt_def.is_union() {
                            return err_span(expr.span, format!("expected function, tuple struct or tuple variant, found union `{:}`", self.def_id_to_friendly(def_id)));
                        }
                        assert!(adt_def.is_struct());

                        // TODO visibility of fields ...

                        let variant_def = adt_def.non_enum_variant();

                        let variant_name = str_ident(&variant_def.ident(self.tcx).as_str());
                        self.parens_ctor(expr.span, &typ_args, args, variant_def, &adt_def, variant_name)
                    }
                    PathResolution::DatatypeVariant(variant_def_id, typ_args) => {
                        // TODO visibility of fields ...
                        let enum_did = self.tcx.parent(variant_def_id);
                        let adt_def = self.tcx.adt_def(enum_did);
                        assert!(adt_def.is_enum());
                        let variant_def = adt_def.variant_with_id(variant_def_id);

                        let variant_name = str_ident(&variant_def.ident(self.tcx).as_str());
                        self.parens_ctor(expr.span, &typ_args, args, variant_def, &adt_def, variant_name)
                    }
                    pr => {
                        dbg!(pr);
                        todo!()
                    }
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
                        self.expect_exact(&vir_callee.typ, &t)?;
                        (args, ret)
                    }
                };

                let mut vir_args = vec![];
                for (i, arg) in args.iter().enumerate() {
                    let vir_arg = self.check_expr(arg)?;
                    self.expect_allowing_coercion(&vir_arg.typ, &callee_arg_typs[i])?;
                    vir_args.push(vir_arg);
                }

                let ct = CallTarget::FnSpec(vir_callee);
                mk_expr(&callee_ret_typ, ExprX::Call(ct, Arc::new(vir_args)))
            }
            ExprKind::Struct(qpath, fields, spread_opt) => {
                match self.check_qpath_for_expr(qpath, expr.hir_id)? {
                    PathResolution::Datatype(def_id, typ_args) => {
                        // TODO visibility of fields...
                        let (variant_name, variant_def) = self.check_braces_struct_valid(
                            def_id, fields, &[], spread_opt.is_some(), qpath.span())?;

                        self.braces_ctor(expr.span, &typ_args, fields,
                           *spread_opt,
                           def_id,
                           variant_def,
                           variant_name)
                    }
                    PathResolution::DatatypeVariant(variant_def_id, typ_args) => {
                        if spread_opt.is_some() {
                            todo!();
                        }

                        let enum_did = self.tcx.parent(variant_def_id);
                        let adt_def = self.tcx.adt_def(enum_did);
                        assert!(adt_def.is_enum());
                        let variant_def = adt_def.variant_with_id(variant_def_id);

                        self.check_braces_variant_valid(&adt_def, variant_def, fields, &[], false, expr.span)?;

                        let variant_name = str_ident(&variant_def.ident(self.tcx).as_str());

                        self.braces_ctor(expr.span, &typ_args, fields,
                           None,
                           enum_did,
                           variant_def,
                           variant_name)
                    }
                    _ => todo!(),
                }
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
                            self.expect_allowing_coercion(&vir_init.typ, &typ)?;
                            let pat = self.check_pat(pat, &typ)?;

                            vir_stmts.push(bctx.spanned_new(stmt.span,
                                StmtX::Decl { pattern: pat, mode: Some(Mode::Spec),
                                    init: Some(vir_init) }));
                        }
                        //StmtKind::Semi(e) => {
                        //    self.check_expr(e)?;
                        //}
                        _ => {
                            dbg!(&stmt.kind);
                            todo!()
                        }
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
                self.check_closure(closure, expr)
            }
            ExprKind::Binary(bin_op, lhs, rhs) => {
                match &bin_op.node {
                    BinOpKind::Add | BinOpKind::Mul => {
                        let l = self.check_expr(lhs)?;
                        let r = self.check_expr(rhs)?;

                        self.expect_integer(&l.typ)?;
                        self.expect_integer(&r.typ)?;

                        let l1 = self.get_typ_with_concrete_head_if_possible(&l.typ)?;
                        let r1 = self.get_typ_with_concrete_head_if_possible(&r.typ)?;

                        let typ = if matches!(&*l1, TypX::Int(IntRange::Nat))
                                    && matches!(&*r1, TypX::Int(IntRange::Nat))
                        {
                            nat_typ()
                        } else {
                            int_typ()
                        };
                        let arith_op = match &bin_op.node {
                            BinOpKind::Add => ArithOp::Add,
                            BinOpKind::Mul => ArithOp::Mul,
                            _ => unreachable!(),
                        };
                        mk_expr(
                            &typ,
                            ExprX::Binary(BinaryOp::Arith(arith_op, Mode::Spec), l, r),
                        )
                    }
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
                    BinOpKind::Div => {
                        let l = self.check_expr(lhs)?;
                        let r = self.check_expr(rhs)?;
                        self.expect_integer(&l.typ)?;
                        self.expect_integer(&r.typ)?;
                        self.expect_exact(&l.typ, &r.typ)?;
                        self.concretize_integer_type_to_int_if_possible(&l.typ);

                        let input_typ = self.get_typ_with_concrete_head_if_possible(&l.typ)?;

                        let output_typ = match &*input_typ {
                            TypX::Int(IntRange::U(_) | IntRange::USize | IntRange::Nat) => input_typ.clone(),
                            _ => int_typ(),
                        };

                        mk_expr(
                            &output_typ,
                            ExprX::Binary(BinaryOp::Arith(ArithOp::EuclideanDiv, Mode::Spec), l, r),
                        )
                    }
                    BinOpKind::Rem => {
                        let l = self.check_expr(lhs)?;
                        let r = self.check_expr(rhs)?;
                        self.expect_integer(&l.typ)?;
                        self.expect_integer(&r.typ)?;
                        self.expect_exact(&l.typ, &r.typ)?;

                        mk_expr(
                            &l.typ.clone(),
                            ExprX::Binary(BinaryOp::Arith(ArithOp::EuclideanMod, Mode::Spec), l, r),
                        )
                    }
                    BinOpKind::And | BinOpKind::Or => {
                        let l = self.check_expr(lhs)?;
                        let r = self.check_expr(rhs)?;
                        self.expect_bool(&l.typ)?;
                        self.expect_bool(&r.typ)?;
                        let bin_op = match &bin_op.node {
                            BinOpKind::And => BinaryOp::And,
                            BinOpKind::Or => BinaryOp::Or,
                            _ => unreachable!(),
                        };
                        mk_expr(
                            &bool_typ(),
                            ExprX::Binary(bin_op, l, r),
                        )
                    }
                    BinOpKind::Le | BinOpKind::Ge | BinOpKind::Lt | BinOpKind::Gt => {
                        let l = self.check_expr(lhs)?;
                        let r = self.check_expr(rhs)?;
                        self.expect_integer(&l.typ)?;
                        self.expect_integer(&r.typ)?;
                        let bin_op = match &bin_op.node {
                            BinOpKind::Le => BinaryOp::Inequality(InequalityOp::Le),
                            BinOpKind::Lt => BinaryOp::Inequality(InequalityOp::Lt),
                            BinOpKind::Ge => BinaryOp::Inequality(InequalityOp::Ge),
                            BinOpKind::Gt => BinaryOp::Inequality(InequalityOp::Gt),
                            _ => unreachable!(),
                        };
                        mk_expr(
                            &bool_typ(),
                            ExprX::Binary(bin_op, l, r),
                        )
                    }
                    BinOpKind::BitAnd | BinOpKind::BitOr | BinOpKind::BitXor => {
                        let l = self.check_expr(lhs)?;
                        let r = self.check_expr(rhs)?;
                        self.expect_integer(&l.typ)?;
                        self.expect_integer(&r.typ)?;
                        self.expect_exact(&l.typ, &r.typ)?;
                        let bitwise_op = match &bin_op.node {
                            BinOpKind::BitAnd => BitwiseOp::BitAnd,
                            BinOpKind::BitOr => BitwiseOp::BitOr,
                            BinOpKind::BitXor => BitwiseOp::BitXor,
                            _ => unreachable!(),
                        };
                        let bin_op = BinaryOp::Bitwise(bitwise_op, Mode::Spec);
                        mk_expr(
                            &l.typ.clone(),
                            ExprX::Binary(bin_op, l, r),
                        )
                    }
                    BinOpKind::Shr => {
                        let l = self.check_expr(lhs)?;
                        let r = self.check_expr(rhs)?;

                        // Types not required to be the same
                        self.expect_integer(&l.typ)?;
                        self.expect_integer(&r.typ)?;

                        // Note: bit-width is irrelevant because this is spec code
                        // TODO: refactor AST so supplying bitwidth is unnecessary
                        let bitwise_op = BitwiseOp::Shr(IntegerTypeBitwidth::Width(64));
                        let bin_op = BinaryOp::Bitwise(bitwise_op, Mode::Spec);
                        mk_expr(
                            &l.typ.clone(),
                            ExprX::Binary(bin_op, l, r),
                        )
                    }
                    BinOpKind::Shl => {
                        let l = self.check_expr(lhs)?;
                        let r = self.check_expr(rhs)?;

                        // Types not required to be the same
                        self.expect_integer(&l.typ)?;
                        self.expect_integer(&r.typ)?;

                        let l1 = self.get_typ_with_concrete_head_if_possible(&l.typ)?;
                        let int_range = match &*l1 {
                            TypX::Int(ir) => match ir {
                                IntRange::Int | IntRange::Nat => todo!(),
                                IntRange::Char => todo!(),
                                IntRange::USize | IntRange::ISize
                                  | IntRange::U(_) | IntRange::I(_) => *ir,
                            },
                            TypX::UnificationVar(_) => {
                                todo!()
                            }
                            _ => {
                                todo!()
                            }
                        };

                        let (bw, signedness) = crate::rust_to_vir_base::bitwidth_and_signedness_of_int_range(int_range);
                        let bw = bw.unwrap();

                        // Note: bit-width is irrelevant because this is spec code
                        // TODO: refactor AST so supplying bitwidth is unnecessary
                        let bitwise_op = BitwiseOp::Shl(bw, signedness);
                        let bin_op = BinaryOp::Bitwise(bitwise_op, Mode::Spec);
                        mk_expr(
                            &l.typ.clone(),
                            ExprX::Binary(bin_op, l, r),
                        )
                    }
                    BinOpKind::Eq => {
                        self.check_equality(expr.span, lhs, rhs, false)
                    }
                    BinOpKind::Ne => {
                        self.check_equality(expr.span, lhs, rhs, true)
                    }
                }
            }

            ExprKind::Unary(UnOp::Not, inner) => {
                let vir_expr = self.check_expr(inner)?;
                let typ = self.get_typ_with_concrete_head_if_possible(&vir_expr.typ)?;
                let not_op = match &*typ {
                    TypX::UnificationVar(_) => {
                        return err_span(inner.span, "cannot infer the type of the operand to '!'");
                    }
                    TypX::Int(IntRange::I(_) | IntRange::ISize) => UnaryOp::BitNot(None),
                    TypX::Int(IntRange::U(w)) => UnaryOp::BitNot(Some(IntegerTypeBitwidth::Width(*w))),
                    TypX::Int(IntRange::USize) => UnaryOp::BitNot(Some(IntegerTypeBitwidth::ArchWordSize)),
                    TypX::Bool => UnaryOp::Not,
                    _ => {
                        return err_span(inner.span, format!("cannot apply '!' to type {:}", typ_to_diagnostic_str(&typ)));
                    }
                };
                mk_expr(&typ, ExprX::Unary(not_op, vir_expr))
            }

            ExprKind::Unary(UnOp::Deref, inner) => {
                let vir_expr = self.check_expr(inner)?;

                let t = self.get_typ_with_concrete_head_if_possible(&vir_expr.typ)?;
                if let TypX::UnificationVar(_) = &*t {
                    return err_span(expr.span, format!("cannot infer the type of this reference"));
                }
                match &*t {
                    TypX::UnificationVar(_) => {
                        return err_span(expr.span, format!("cannot infer the type of this reference"));
                    }
                    TypX::Decorate(TypDecoration::Ref | TypDecoration::MutRef, None, inner_typ) => {
                        mk_expr(&inner_typ, vir_expr.x.clone())
                    }
                    _ => {
                        return err_span(expr.span, format!("expected reference or pointer here"));
                    }
                }
            }

            ExprKind::AddrOf(BorrowKind::Ref, Mutability::Not, e) => {
                let vir_e = self.check_expr(e)?;
                let typ = Arc::new(TypX::Decorate(vir::ast::TypDecoration::Ref, None, vir_e.typ.clone()));
                mk_expr(&typ, vir_e.x.clone())
            }

            ExprKind::Tup(es) => {
                let mut vir_es = vec![];
                let mut vir_typs = vec![];
                for e in es.iter() {
                    let vir_e = self.check_expr(e)?;
                    vir_typs.push(vir_e.typ.clone());
                    vir_es.push(vir_e);
                }
                let typ = vir::ast_util::mk_tuple_typ(&Arc::new(vir_typs));
                mk_expr(&typ, vir::ast_util::mk_tuple_x(&Arc::new(vir_es)))
            }

            ExprKind::Lit(lit) => match &lit.node {
                LitKind::Int(i, lit_int_type) => {
                    self.lit_int(expr.span,
                        BigInt::from(i.get()),
                        LitIntSuffix::Normal(*lit_int_type))
                }
                LitKind::Bool(b) => {
                    mk_expr(&bool_typ(), ExprX::Const(Constant::Bool(*b)))
                }
                _ => {
                    dbg!(&lit);
                    todo!()
                }
            }

            ExprKind::Unary(UnOp::Neg, inner) => {
                match &inner.kind {
                    ExprKind::Lit(lit) => match &lit.node {
                        LitKind::Int(i, lit_int_type) => {
                            return self.lit_int(expr.span,
                                -BigInt::from(i.get()),
                                LitIntSuffix::Normal(*lit_int_type));
                        }
                        _ => { }
                    }
                    _ => { }
                }

                todo!();
            }

            ExprKind::Cast(expr, ty) => {
                let vir_expr = self.check_expr(expr)?;
                let to_typ = self.check_ty(ty)?;

                self.concretize_integer_type_to_int_if_possible(&vir_expr.typ);
                let source_typ = self.get_typ_with_concrete_head_if_possible(&vir_expr.typ)?;

                match (&*source_typ, &*to_typ) {
                    (TypX::Int(IntRange::U(_)), TypX::Int(IntRange::Nat))
                    | (TypX::Int(IntRange::USize), TypX::Int(IntRange::Nat))
                    | (TypX::Int(IntRange::Nat), TypX::Int(IntRange::Nat))
                    | (TypX::Int(_), TypX::Int(IntRange::Int))
                    => {
                        // No clip is necessary -- just change the type
                        mk_expr(&to_typ, vir_expr.x.clone())
                    }
                    (TypX::Int(IntRange::Int), TypX::Int(IntRange::Nat)) => {
                        let e = mk_ty_clip(&to_typ, &vir_expr, true);
                        mk_expr(&to_typ, e.x.clone())
                    }
                    (TypX::Int(_), TypX::Int(_)) => {
                        let expr_attrs = bctx.ctxt.tcx.hir().attrs(expr.hir_id);
                        let expr_vattrs = bctx.ctxt.get_verifier_attrs(expr_attrs)?;
                        let e = mk_ty_clip(&to_typ, &vir_expr, expr_vattrs.truncate);
                        mk_expr(&to_typ, e.x.clone())
                    }
                    (TypX::UnificationVar(_), _) => {
                        err_span(
                            expr.span,
                            "Cannot infer the type of this expression",
                        )
                    }
                    _ => err_span(
                        expr.span,
                        "Verus currently only supports casts from integer types, `char`, and pointer types to integer types",
                    ),
                }
            }

            ExprKind::Field(expr, ident) => {
                let vir_expr = self.check_expr(expr)?;

                let mut t = self.get_typ_as_concrete_as_possible(&vir_expr.typ)?;

                loop {
                    match &*t {
                        TypX::Decorate(TypDecoration::Ref | TypDecoration::MutRef
                          | TypDecoration::Box | TypDecoration::Rc
                          | TypDecoration::Arc | TypDecoration::Ghost
                          | TypDecoration::Tracked, None, inner) => { t = inner.clone() }
                        _ => { break; }
                    }
                }

                if let TypX::UnificationVar(_) = &*t {
                    return err_span(expr.span, format!("cannot infer the type of the receiver"));
                }
                let TypX::Datatype(dt, typ_args, _) = &*t else {
                    return err_span(expr.span, format!("`{:}` is not a datatype and therefore doesn't have fields", typ_to_diagnostic_str(&t)));
                };
                let field_name = ident.as_str();
                match dt {
                    Dt::Path(path) => {
                        let def_id = crate::rust_to_vir_base::def_id_of_vir_path(path);
                        let adt_def = self.tcx.adt_def(def_id);
                        if adt_def.is_struct() {
                            let variant_def = adt_def.non_enum_variant();
                            let is_valid = variant_def.fields.iter().any(|f| f.ident(self.tcx).as_str() == field_name);
                            if !is_valid {
                                return err_span(ident.span,
                                  format!("no field `{:}` on type `{:}`", ident.as_str(), typ_to_diagnostic_str(&t)));
                            }

                            let field_typ = self.get_field_typ(expr.span, variant_def, &typ_args, &ident.as_str())?;
                            let field_opr = FieldOpr {
                                datatype: dt.clone(),
                                variant: str_ident(&variant_def.ident(self.tcx).as_str()),
                                field: str_ident(field_name),
                                get_variant: false,
                                check: VariantCheck::None,
                            };

                            mk_expr(
                                &field_typ,
                                ExprX::UnaryOpr(UnaryOpr::Field(field_opr), vir_expr),
                            )

                        } else if adt_def.is_enum() {
                            todo!();
                        } else if adt_def.is_union() {
                            todo!();
                        } else {
                            unreachable!();
                        }
                    }
                    Dt::Tuple(n) => {
                        let n = *n;
                        assert!(n == typ_args.len());
                        let i = match field_name.parse::<usize>() {
                            Err(_) => {
                                return err_span(expr.span, format!("A {:}-tuple type expects a numeric field identifier", n));
                            }
                            Ok(i) => {
                                if i >= n {
                                    return err_span(expr.span, format!("No field {:} for {:}-tuple", i, n));
                                }
                                i
                            }
                        };
                        let x = vir::ast_util::mk_tuple_field_x(&vir_expr, n, i);
                        mk_expr(&typ_args[i], x)
                    }
                }
            }

            ExprKind::If(cond, lhs, rhs) => {
                let cond = cond.peel_drop_temps();
                match &cond.kind {
                    ExprKind::Let(LetExpr { pat, init: expr, ty: _, span: _, is_recovered: None }) => {
                        let vir_expr = self.check_expr(expr)?;

                        /* lhs */
                        let lhs_pattern = self.check_pat(pat, &vir_expr.typ)?;
                        let lhs_guard = mk_bool(&vir_expr.span, true);
                        let lhs_body = self.check_expr(lhs)?;

                        let rhs_pattern = self.bctx.spanned_typed_new(
                            cond.span,
                            &vir_expr.typ,
                            PatternX::Wildcard(false));
                        let rhs_guard = mk_bool(&vir_expr.span, true);
                        let rhs_body = if let Some(rhs) = rhs {
                            self.check_expr(rhs)?
                        } else {
                            self.bctx.spanned_typed_new(
                                expr.span,
                                &unit_typ(),
                                ExprX::Block(Arc::new(Vec::new()), None),
                            )
                        };

                        self.expect_exact(&lhs_body.typ, &rhs_body.typ)?;
                        let typ = lhs_body.typ.clone();

                        let rhs_span = if let Some(rhs) = rhs {
                            rhs.span
                        } else {
                            expr.span
                        };

                        let lhs_vir_arm = ArmX { pattern: lhs_pattern, guard: lhs_guard, body: lhs_body };
                        let rhs_vir_arm = ArmX { pattern: rhs_pattern, guard: rhs_guard, body: rhs_body };
                        let vir_arms = vec![
                            self.bctx.spanned_new(lhs.span, lhs_vir_arm),
                            self.bctx.spanned_new(rhs_span, rhs_vir_arm),
                        ];

                        mk_expr(&typ, ExprX::Match(vir_expr, Arc::new(vir_arms)))
                    }
                    _ => {
                        let vir_cond = self.check_expr(cond)?;
                        self.expect_bool(&vir_cond.typ)?;

                        let vir_lhs = self.check_expr(lhs)?;
                        let (vir_rhs, rhs_typ) = match rhs {
                            Some(rhs) => {
                                let r = self.check_expr(rhs)?;
                                let t = r.typ.clone();
                                (Some(r), t)
                            }
                            None => {
                                (None, unit_typ())
                            }
                        };

                        // TODO can allow some coercions here
                        self.expect_exact(&vir_lhs.typ, &rhs_typ)?;
                        let typ = vir_lhs.typ.clone();

                        mk_expr(&typ, ExprX::If(vir_cond, vir_lhs, vir_rhs))
                    }
                }
            }

            ExprKind::Match(matchee, arms, _match_source) => {
                unsupported_err_unless!(arms.len() != 0, expr.span, "match with no arms");

                let vir_matchee = self.check_expr(matchee)?;
                let mut vir_arms = vec![];
                for arm in arms.iter() {
                    let rustc_hir::Arm { hir_id: _, span, pat, guard, body } = arm;
                    let vir_pat = self.check_pat(pat, &vir_matchee.typ)?;
                    let vir_guard = match guard {
                        None => mk_bool(&vir_pat.span, true),
                        Some(guard) => {
                            let vir_guard = self.check_expr(guard)?;
                            self.expect_bool(&vir_guard.typ)?;
                            vir_guard
                        }
                    };
                    let vir_body = self.check_expr(body)?;
                    vir_arms.push(self.bctx.spanned_new(*span,
                        ArmX { pattern: vir_pat, guard: vir_guard, body: vir_body }));
                }

                for i in 1 .. vir_arms.len() {
                    self.expect_exact(&vir_arms[0].x.body.typ, &vir_arms[i].x.body.typ)?;
                }
                let typ = vir_arms[0].x.body.typ.clone();

                mk_expr(&typ, ExprX::Match(vir_matchee, Arc::new(vir_arms)))
            }

            _ => {
                return err_span(expr.span, format!("Verus ghost code does not support the following expression kind: {:?}", &expr.kind));
            }
        }
    }

    pub(crate) fn lit_int(&mut self, span: Span, i: num_bigint::BigInt, suffix: LitIntSuffix) -> 
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

    pub fn def_id_to_friendly(&self, def_id: DefId) -> String {
        crate::rust_to_vir_base::def_id_to_friendly(self.tcx, Some(&self.bctx.ctxt.verus_items),
            def_id)
    }

    pub fn check_equality(&mut self, span: Span, lhs: &'tcx Expr<'tcx>, rhs: &'tcx Expr<'tcx>, negate: bool)
      -> Result<vir::ast::Expr, vir::ast::VirErr>
    {
        let l = self.check_expr(lhs)?;
        let r = self.check_expr(rhs)?;

        self.expect_types_comparable_by_eq(&l.typ, &r.typ)?;

        let op = if negate {
            BinaryOp::Ne
        } else {
            BinaryOp::Eq(Mode::Spec)
        };

        Ok(self.bctx.spanned_typed_new(span,
            &bool_typ(), ExprX::Binary(op, l, r)))

    }

    fn typ_of_const_param(&self, span: Span, ident: &Ident) -> Result<Typ, VirErr> {
        for clause in self.param_env.caller_bounds() {
            if let rustc_middle::ty::ClauseKind::ConstArgHasType(cnst, _ty) = clause.kind().skip_binder() {
                if let rustc_middle::ty::ConstKind::Param(pc) = cnst.kind() {
                    if pc.name.as_str() == &**ident {
                        let typ = crate::rust_to_vir_base::mid_ty_to_vir(
                            self.tcx,
                            &self.bctx.ctxt.verus_items,
                            self.bctx.fun_id,
                            span,
                            &cnst.ty(),
                            false)?;
                        if !matches!(&*typ, TypX::Int(
                            IntRange::Int | IntRange::Nat | IntRange::U(_) | IntRange::I(_)
                              | IntRange::USize | IntRange::ISize))
                        {
                            todo!();
                        }
                        return Ok(typ);
                    }
                }
            }
        }
        todo!();
    }
}

pub(crate) enum LitIntSuffix {
    Normal(LitIntType),
    Int,
    Nat,
}
