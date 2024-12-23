use crate::util::{err_span};
use crate::verus_items;
use crate::unsupported_err;
use crate::spec_typeck::State;
use crate::spec_typeck::check_path::PathResolution;
use vir::ast::{Typ, TypX, VarBinderX, ExprX, BinaryOp, CallTarget, Mode, ArithOp, StmtX, IntRange, Constant, FunX, CallTargetKind, AutospecUsage, Dt, Ident, VirErr, InequalityOp, Typs, FieldOpr, VariantCheck, UnaryOpr};
use rustc_hir::{Expr, ExprKind, Block, BlockCheckMode, Closure, ClosureBinder, Constness, CaptureBy, FnDecl, ImplicitSelfKind, ClosureKind, Body, PatKind, BindingMode, ByRef, Mutability, BinOpKind, FnRetTy, StmtKind, LetStmt, ExprField, PatField};
use std::sync::Arc;
use vir::ast_util::{unit_typ, int_typ, integer_typ, bool_typ, nat_typ, typ_to_diagnostic_str};
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
                    _ => todo!()
                }
            }
            ExprKind::MethodCall(path_segment, receiver, args, span) => {
                let e = self.check_expr(receiver)?;
                let (def_id, typ_args) = self.lookup_method_call(path_segment, &e.typ, *span, expr)?;

                let (input_typs, output_typ) = self.fn_item_type_substitution(expr.span, def_id, &typ_args)?;

                if input_typs.len() != args.len() + 1 {
                    return err_span(expr.span, format!("function takes {:} arguments, got {:}", input_typs.len(), args.len()));
                }
                
                let mut vir_args = vec![];

                self.expect_exact(&e.typ, &input_typs[0])?;
                vir_args.push(e);

                for (arg, input_typ) in args.iter().zip(input_typs.iter().skip(1)) {
                    let vir_arg = self.check_expr(arg)?;
                    self.expect_allowing_coercion(&vir_arg.typ, input_typ)?;
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
            ExprKind::Call(Expr { kind: ExprKind::Path(qpath), .. }, args) => {
                if let QPath::Resolved(_qualified_self, path) = qpath {
                    if let Res::Def(_, def_id) = &path.res {
                        if let Some(verus_item) = self.bctx.ctxt.get_verus_item(*def_id) {
                            let e = self.check_call_verus_item(verus_item, expr, args)?;
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
                        //if let Some(verus_item) = self.bctx.ctxt.get_verus_item(def_id) {
                        //    if !matches!(verus_item,
                        //        VerusItem::Vstd(_, _) | VerusItem::Marker(_) | VerusItem::BuiltinType(_)) {
                        //        return self.check_call_verus_item(verus_item, expr, args);
                        //    }
                        //}

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

                self.expect_allowing_coercion(&body.typ, &output_typ)?;

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
                    _ => todo!()
                }
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

            ExprKind::Field(expr, ident) => {
                let vir_expr = self.check_expr(expr)?;
                let t = self.get_typ_with_concrete_head_if_possible(&vir_expr.typ)?;
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
                    Dt::Tuple(_) => todo!(),
                }
            }

            _ => {
                return err_span(expr.span, format!("Verus ghost code does not support the following expression kind: {:?}", &expr.kind));
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

    /* Some notes about how Rust / rustc works with variants:

    Any variant can optionally have a "constructor", which is either
    CtorKind::Const or CtorKind::Fn.

    enum Foo {
        VariantConst                  // Some(CtorKind::Const)
        VariantFn(bool)               // Some(CtorKind::Fn)
        VariantBraces { b: bool }     // None
    }

    struct StructConst;               // Some(CtorKind::Const)
    struct StructFn(bool);            // Some(CtorKind::Fn)
    struct StructBraces { b: bool }   // None

    Now, when writing a 'Struct' expression or pattern (with braces), any of these 3 kinds
    is acceptable. For const-style, it would be empty (StructConst { }) and for paren-style
    you would add numeric fields: (StructFn { 0: true }).

    When a variant shows up as a constant (or in a function call) however, it has
    to be a constructor.

    This is valid:
     - VariantConst
     - VariantFn(b)

    This is invalid:
     - VariantConst(b)

    Of course, rustc lets you use VariantFn on its own without calling it; it has function type.
    (But this isn't supported by us right now.)
    */

    /// Check if a 'braces-style construct' (e.g., `Foo { a, b, c }`) is valid
    /// for:
    ///  - structs and unions in expressions 
    ///  - structs in patterns
    /// Errors for enums.
    ///
    /// This checks if all field names are valid and that there are no duplicates.
    ///
    /// Caller should provide either `expr_fields` or `pat_fields`; put empty list []
    /// for the other.
    ///
    /// can_skip_fields: If true, you're allowed to skip fields, otherwise, you must
    /// provide all fields. For a struct, this should be true if a spread is provided,
    /// and for patterns, this should be true if a '..' is a provided.

    pub(crate) fn check_braces_struct_valid(
        &mut self,
        def_id: DefId,
        expr_fields: &'tcx [ExprField<'tcx>],
        pat_fields: &'tcx [PatField<'tcx>],
        can_skip_fields: bool,
        span: Span,
    ) -> Result<(Ident, &'tcx VariantDef), VirErr> {
        let adt_def = self.tcx.adt_def(def_id);
        if adt_def.is_struct() {
            let variant_def = adt_def.non_enum_variant();
            self.check_braces_variant_valid(&adt_def, variant_def, expr_fields, pat_fields, can_skip_fields, span)?;
            let variant_name = str_ident(&variant_def.ident(self.tcx).as_str());
            Ok((variant_name, variant_def))
        } else if adt_def.is_union() {
            todo!()
        } else if adt_def.is_enum() {
            return err_span(span, "this is an enum, so a variant must be provided");
        } else {
            unreachable!();
        }
    }

    pub(crate) fn check_braces_variant_valid(
        &mut self,
        adt_def: &AdtDef,
        variant_def: &'tcx VariantDef,
        expr_fields: &'tcx [ExprField<'tcx>],
        pat_fields: &'tcx [PatField<'tcx>],
        can_skip_fields: bool,
        span: Span,
    ) -> Result<(), VirErr> {
        let is_valid_field = |name: &str| variant_def.fields.iter().any(|f| f.ident(self.tcx).as_str() == name);

        let mut seen_fields = HashSet::<String>::new();

        let idents = expr_fields.iter().map(|f| (f.ident.as_str(), f.span))
               .chain(pat_fields.iter().map(|f| (f.ident.as_str(), f.span)));

        for (f_ident, span) in idents {
            if !is_valid_field(f_ident) {
                if adt_def.is_struct() {
                    return err_span(span,
                      format!("struct `{:}` has no field named `{:}`",
                        self.def_id_to_friendly(adt_def.did()), f_ident));
                } else if adt_def.is_enum() {
                    return err_span(span,
                      format!("variant `{:}::{:}` has no field named `{:}`",
                        self.def_id_to_friendly(adt_def.did()), variant_def.ident(self.tcx).as_str(), f_ident));
                } else {
                    unreachable!()
                }
            }
            
            let not_dupe = seen_fields.insert(f_ident.to_string());
            if !not_dupe {
                return err_span(span,
                  format!("field `{:}` specified more than once", f_ident));
            }
        }

        if !can_skip_fields && seen_fields.len() != variant_def.fields.len() {
            let mut unspecified_fields = vec![];
            for f in variant_def.fields.iter() {
                if !seen_fields.contains(f.ident(self.tcx).as_str()) {
                    unspecified_fields.push(format!("`{:}`", f.ident(self.tcx).as_str()));
                }
            }
            return err_span(span,
              format!("missing {:} {:} in initializer of `{:}`",
                  if unspecified_fields.len() != 1 { "fields" } else { "field" },
                  unspecified_fields.join(", "),
                  if adt_def.is_struct() {
                    self.def_id_to_friendly(adt_def.did())
                  } else if adt_def.is_enum() {
                    format!("{:}::{:}", self.def_id_to_friendly(adt_def.did()), variant_def.ident(self.tcx).as_str())
                  } else {
                    unreachable!()
                  }));
        }

        Ok(())
    }

    fn braces_ctor(
        &mut self,
        span: Span,
        typ_args: &Typs,
        fields: &'tcx [ExprField],
        spread_opt: Option<&'tcx Expr<'tcx>>,
        adt_def_id: DefId,
        variant_def: &VariantDef,
        variant_name: vir::ast::Ident,
    ) -> Result<vir::ast::Expr, VirErr> {
        let path = crate::rust_to_vir_base::def_id_to_vir_path(self.tcx,
                            &self.bctx.ctxt.verus_items, adt_def_id);
        let dt = Dt::Path(path);
        let typ = Arc::new(TypX::Datatype(dt.clone(), typ_args.clone(), Arc::new(vec![])));

        let vir_spread_opt = match spread_opt {
            Some(spread) => {
                let vir_spread = self.check_expr(spread)?;
                self.expect_exact(&vir_spread.typ, &typ)?;
                Some(vir_spread)
            }
            None => None,
        };
        let mut ident_binders = vec![];
        for field in fields.iter() {
            let ExprField { hir_id: _, ident, expr: field_expr, span: _, is_shorthand: _ } = field;
            let vir_field_expr = self.check_expr(field_expr)?;
            let field_typ = self.get_field_typ(field.span, variant_def, &typ_args, &ident.as_str())?;
            self.expect_allowing_coercion(&vir_field_expr.typ, &field_typ)?;

            let ident = field_ident_from_rust(ident.as_str());
            ident_binders.push(ident_binder(&ident, &vir_field_expr));
        }

        let x = ExprX::Ctor(dt, variant_name, Arc::new(ident_binders), vir_spread_opt);
        Ok(self.bctx.spanned_typed_new(span, &typ, x))
    }

    fn parens_ctor(
        &mut self,
        span: Span,
        typ_args: &Typs,
        args: &'tcx [Expr],
        variant_def: &VariantDef,
        adt_def: &AdtDef,
        variant_name: vir::ast::Ident,
    ) -> Result<vir::ast::Expr, VirErr> {
        if variant_def.ctor_kind() != Some(CtorKind::Fn) {
            return err_span(span, format!("this constructor is not a function-call constructor"));
        }
        if args.len() != variant_def.fields.len() {
            return err_span(span, format!("this construtor takes {:} argument{:} but {:} argument{:} were supplied",
                variant_def.fields.len(),
                if variant_def.fields.len() != 1 { "s" } else { "" },
                args.len(),
                if args.len() != 1 { "s" } else { "" }));
        }

        let path = crate::rust_to_vir_base::def_id_to_vir_path(self.tcx,
            &self.bctx.ctxt.verus_items, adt_def.did());
        let dt = Dt::Path(path);
        let typ = Arc::new(TypX::Datatype(dt.clone(), typ_args.clone(), Arc::new(vec![])));

        let mut ident_binders = vec![];
        for (i, arg) in args.iter().enumerate() {
            let vir_arg = self.check_expr(arg)?;
            let field_typ = self.get_field_typ_positional(span, variant_def, &typ_args, i)?;
            self.expect_allowing_coercion(&vir_arg.typ, &field_typ)?;
            let ident = positional_field_ident(i);
            ident_binders.push(ident_binder(&ident, &vir_arg));
        }

        let x = ExprX::Ctor(dt, variant_name, Arc::new(ident_binders), None);
        Ok(self.bctx.spanned_typed_new(span, &typ, x))
    }

    fn const_ctor(
        &mut self,
        span: Span,
        typ_args: &Typs,
        variant_def: &VariantDef,
        adt_def: &AdtDef,
        variant_name: vir::ast::Ident,
    ) -> Result<vir::ast::Expr, VirErr> {
        if variant_def.ctor_kind() != Some(CtorKind::Const) {
            return err_span(span, format!("this constructor is not a const-style constructor"));
        }
        assert!(variant_def.fields.len() == 0);

        let path = crate::rust_to_vir_base::def_id_to_vir_path(self.tcx,
            &self.bctx.ctxt.verus_items, adt_def.did());
        let dt = Dt::Path(path);
        let typ = Arc::new(TypX::Datatype(dt.clone(), typ_args.clone(), Arc::new(vec![])));

        let ident_binders = vec![];

        let x = ExprX::Ctor(dt, variant_name, Arc::new(ident_binders), None);
        Ok(self.bctx.spanned_typed_new(span, &typ, x))
    }

    fn def_id_to_friendly(&self, def_id: DefId) -> String {
        crate::rust_to_vir_base::def_id_to_friendly(self.tcx, Some(&self.bctx.ctxt.verus_items),
            def_id)
    }

    pub fn extract_quant(
        &mut self,
        span: Span,
        quant: vir::ast::Quant,
        expr: &'tcx Expr<'tcx>,
    ) -> Result<vir::ast::Expr, VirErr> {
        match &expr.kind {
            ExprKind::Closure(closure) => {
                let Closure {
                    def_id: _,
                    binder: ClosureBinder::Default,
                    constness: Constness::NotConst,
                    capture_clause: CaptureBy::Ref,
                    bound_generic_params: [],
                    fn_decl: FnDecl {
                        inputs, output: _, c_variadic: false, implicit_self: ImplicitSelfKind::None,
                            lifetime_elision_allowed: _,
                    },
                    body,
                    fn_decl_span: _,
                    fn_arg_span: _,
                    kind: ClosureKind::Closure
                } = closure else {
                    unsupported_err!(expr.span, "complex closure");
                };

                let mut binder_typs = vec![];
                for input in inputs.iter() {
                    binder_typs.push(self.check_ty(input)?);
                }

                let closure_body = self.tcx.hir().body(*body);
                let Body { params, value: _ } = closure_body;

                self.scope_map.push_scope(false);

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
                    self.scope_map.insert(name.clone(), binder_typs[i].clone()).expect("scope_map insert");
                    var_binders.push(Arc::new(VarBinderX { name, a: binder_typs[i].clone() }));
                }

                let body_expr = self.bctx.ctxt.spec_hir.bodies.get(&body).unwrap();
                let vir_expr = self.check_expr(body_expr)?;
                self.scope_map.pop_scope();

                self.expect_bool(&vir_expr.typ)?;

                Ok(self.bctx.spanned_typed_new(span, &bool_typ(),
                    ExprX::Quant(quant, Arc::new(var_binders), vir_expr)))
            }
            _ => err_span(expr.span, "Encoding error: argument to forall/exists must be a closure"),
        }
    }
}

enum LitIntSuffix {
    Normal(LitIntType),
    Int,
    Nat,
}
