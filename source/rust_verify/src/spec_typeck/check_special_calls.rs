use crate::spec_typeck::State;
use crate::fn_call_to_vir::get_string_lit_arg;
use crate::verus_items::{
    self, ArithItem, AssertItem, BinaryOpItem, BuiltinFunctionItem, ChainedItem, CompilableOprItem,
    DirectiveItem, EqualityItem, ExprItem, QuantItem, RustItem, SpecArithItem,
    SpecGhostTrackedItem, SpecItem, SpecLiteralItem, SpecOrdItem, UnaryOpItem, VerusItem,
};
use rustc_hir::def::Res;
use vir::ast::{Typ, TypX, VarBinderX, ExprX, BinaryOp, CallTarget, Mode, ArithOp, StmtX, IntRange, Constant, FunX, CallTargetKind, AutospecUsage, Dt, Ident, VirErr, InequalityOp, Typs, Quant, UnaryOpr, TypDecoration, VarAt, Exprs, UnaryOp, ModeCoercion};
use crate::{unsupported_err, unsupported_err_unless};
use vir::ast_util::{bool_typ, undecorate_typ, typ_to_diagnostic_str, str_ident, int_typ};
use rustc_hir::{Expr, ExprKind, Node, QPath};
use rustc_span::Span;
use rustc_hir::def_id::DefId;
use crate::util::err_span;
use vir::def::field_ident_from_rust;
use num_bigint::BigInt;
use crate::spec_typeck::check_expr::LitIntSuffix;
use crate::rust_to_vir_expr::mk_ty_clip;

impl<'a, 'tcx> State<'a, 'tcx> {
    pub fn check_call_rust_item(&mut self, _rust_item: RustItem) -> Result<vir::ast::Expr, VirErr> {
        todo!();
    }

    /// Check the call _before_ running 'normal' type checking.
    /// This completely ignores the type signature of the function being called.
    /// Only calls; no method calls
    pub fn check_call_verus_item_early(
        &mut self,
        def_id: DefId,
        verus_item: &VerusItem,
        expr: &'tcx Expr<'tcx>,
        args: &[&'tcx Expr<'tcx>],
    ) -> Result<Option<vir::ast::Expr>, VirErr> {
        let f_name = self.tcx.def_path_str(def_id);

        let bctx = self.bctx;
        let mk_expr = |typ: &Typ, x: ExprX| Ok(Some(bctx.spanned_typed_new(expr.span, typ, x)));

        match verus_item {
            VerusItem::UnaryOp(UnaryOpItem::SpecLiteral(spec_literal_item)) => {
                unsupported_err_unless!(args.len() == 1, expr.span, "expected spec_literal_*", &args);
                let arg = &args[0];
                let s = get_string_lit_arg(&args[0], &f_name)?;

                let is_num = s.chars().count() > 0 && s.chars().all(|c| c.is_digit(10));
                if !is_num {
                    return err_span(arg.span, "spec_literal_nat/spec_literal_int requires a string literal with only digits");
                }

                let i = BigInt::parse_bytes(s.as_bytes(), 10).unwrap();

                let suffix = match spec_literal_item {
                    SpecLiteralItem::Integer => panic!("SpecLiteralItem::Integer"),
                    SpecLiteralItem::Int => LitIntSuffix::Int,
                    SpecLiteralItem::Nat => LitIntSuffix::Nat,
                };

                let e = self.lit_int(expr.span, i, suffix)?;
                Ok(Some(e))
            }
            VerusItem::Quant(quant_item) => {
                unsupported_err_unless!(args.len() == 1, expr.span, "expected forall/exists", &args);
                let quant = match quant_item {
                    QuantItem::Forall => air::ast::Quant::Forall,
                    QuantItem::Exists => air::ast::Quant::Exists,
                };
                let quant = Quant { quant };
                Ok(Some(self.extract_quant(expr.span, quant, &args[0])?))
            }
            VerusItem::CompilableOpr(CompilableOprItem::Implies) => {
                let (lhs, rhs) = self.check_2_args(expr.span, args)?;
                self.expect_bool(&lhs.typ)?;
                self.expect_bool(&rhs.typ)?;
                let vop = BinaryOp::Implies;
                mk_expr(&bool_typ(), ExprX::Binary(vop, lhs, rhs))
            }
            VerusItem::BinaryOp(BinaryOpItem::Equality(EqualityItem::Equal)) => {
                unsupported_err_unless!(args.len() == 2, expr.span, "expected 2 arguments", &args);
                let e = self.check_equality(expr.span, &args[0], &args[1], false)?;
                Ok(Some(e))
            }
            VerusItem::Expr(ExprItem::IsVariant) => {
                unsupported_err_unless!(args.len() == 2, expr.span, "expected 2 arguments", &args);
                let adt_arg = self.check_expr(&args[0])?;
                let variant_name = get_string_lit_arg(&args[1], &f_name)?;

                let (adt_path, _) = self.check_is_variant(expr.span, &adt_arg, &variant_name, None)?;

                mk_expr(&bool_typ(), ExprX::UnaryOpr(
                    UnaryOpr::IsVariant { datatype: adt_path, variant: str_ident(&variant_name) },
                    adt_arg,
                ))
            }
            VerusItem::Expr(ExprItem::Old) => {
                if let ExprKind::Path(QPath::Resolved(
                    None,
                    rustc_hir::Path { res: Res::Local(id), .. },
                )) = &args[0].kind
                {
                    if let Node::Pat(pat) = self.tcx.hir_node(*id) {
                        let var = crate::rust_to_vir_expr::pat_to_var(pat)?;
                        let typ = match self.scope_map.get(&var) {
                            Some(t) => t,
                            None => {
                                return err_span(expr.span, format!("unrecognized local `{:}`", var));
                            }
                        };
                        if !matches!(&**typ, TypX::Decorate(TypDecoration::MutRef, None, _)) {
                            return err_span(expr.span, format!("the argument to `old` but be a `&mut` parameter"));
                        }
                        return mk_expr(
                            &typ,
                            ExprX::VarAt(var, VarAt::Pre),
                        );
                    }
                }
                err_span(expr.span, "only a variable binding is allowed as the argument to old")
            }

            VerusItem::BinaryOp(BinaryOpItem::Arith(arith_item)) => {
                let (l, r) = self.check_2_args(expr.span, args)?;

                self.expect_integer(&l.typ)?;
                self.expect_exact(&l.typ, &r.typ)?;
                self.concretize_integer_type_to_int_if_possible(&l.typ);
                let output_typ = self.get_typ_with_concrete_head_if_possible(&l.typ)?;

                let arith_op = match arith_item {
                    ArithItem::BuiltinAdd => ArithOp::Add,
                    ArithItem::BuiltinSub => ArithOp::Sub,
                    ArithItem::BuiltinMul => ArithOp::Mul,
                };

                let e = bctx.spanned_typed_new(expr.span, &int_typ(), 
                    ExprX::Binary(BinaryOp::Arith(arith_op, Mode::Spec), l, r));
                let e = mk_ty_clip(&output_typ, &e, true);
                mk_expr(&output_typ, e.x.clone())
            }

            _ => {
                dbg!(verus_item);
                todo!();
            }
        }
    }

    /// Check the call _after_ running 'normal' type checking.
    /// It can be assumed arguments are already checked to be the right type.
    /// Works for normal methods and method calls
    pub fn check_call_verus_item_late(
        &mut self,
        _def_id: DefId,
        verus_item: &VerusItem,
        expr: &'tcx Expr<'tcx>,
        vir_args: &Exprs,
        _typ_args: &Typs,
        output_typ: &Typ,
    ) -> Result<Option<vir::ast::Expr>, VirErr> {
        let bctx = self.bctx;
        let mk_expr = |x: ExprX| Ok(Some(bctx.spanned_typed_new(expr.span, output_typ, x)));

        match verus_item {
            VerusItem::CompilableOpr(CompilableOprItem::GhostNew)
            | VerusItem::UnaryOp(UnaryOpItem::SpecGhostTracked(
                SpecGhostTrackedItem::GhostView
                | SpecGhostTrackedItem::GhostBorrow
                | SpecGhostTrackedItem::TrackedView,
            )) => {
                assert!(vir_args.len() == 1);
                let is_ghost_new = verus_item == &VerusItem::CompilableOpr(CompilableOprItem::GhostNew);
                let op = UnaryOp::CoerceMode {
                    op_mode: Mode::Spec,
                    from_mode: Mode::Spec,
                    to_mode: if is_ghost_new { Mode::Proof } else { Mode::Spec },
                    kind: ModeCoercion::Other,
                };
                mk_expr(ExprX::Unary(op, vir_args[0].clone()))
            }
            _ => { Ok(None) }
        }
    }

    fn check_2_args(
        &mut self,
        span: Span,
        args: &[&'tcx Expr<'tcx>],
    ) -> Result<(vir::ast::Expr, vir::ast::Expr), VirErr> {
        unsupported_err_unless!(args.len() == 2, span, "expected 2 arguments", &args);
        let e0 = self.check_expr(args[0])?;
        let e1 = self.check_expr(args[1])?;
        Ok((e0, e1))
    }

    fn check_is_variant(
        &mut self,
        span: Span,
        vir_expr: &vir::ast::Expr,
        variant_name: &String,
        field_name_typ: Option<(String, &rustc_middle::ty::Ty<'tcx>)>,
    ) -> Result<(Dt, Option<(vir::ast::Ident, Typ)>), VirErr> {
        let tcx = self.tcx;

        let t = self.get_typ_with_concrete_head_if_possible(&vir_expr.typ)?;
        let t = undecorate_typ(&t);
        if let TypX::UnificationVar(_) = &*t {
            return err_span(span, format!("cannot infer the type of the LHS of 'is'"));
        }
        let TypX::Datatype(dt, typ_args, _) = &*t else {
            return err_span(span, format!("`{:}` is not a datatype and therefore doesn't have fields", typ_to_diagnostic_str(&t)));
        };
        let path = match dt {
            Dt::Path(path) => path,
            Dt::Tuple(_) => {
                return err_span(span, format!("expected enum, not a tuple"));
            }
        };

        let def_id = crate::rust_to_vir_base::def_id_of_vir_path(path);

        let adt = tcx.adt_def(def_id);
        if adt.is_union() {
            todo!();
            /*if field_name_typ.is_some() {
                // Don't use get_variant_field with unions
                return err_span(
                    span,
                    format!("this datatype is a union; consider `get_union_field` instead"),
                );
            }
            let variant = adt.non_enum_variant();
            let field_opt = variant.fields.iter().find(|f| f.ident(tcx).as_str() == variant_name);
            if field_opt.is_none() {
                return err_span(span, format!("no field `{variant_name:}` for this union"));
            }

            return Ok((adt_path, None));*/
        } else if adt.is_enum() {
            let variant_opt = adt.variants().iter().find(|v| v.ident(tcx).as_str() == variant_name);
            let Some(variant_def) = variant_opt else {
                return err_span(span, format!("no variant `{variant_name:}` for this datatype"));
            };

            match field_name_typ {
                None => Ok((dt.clone(), None)),
                Some((field_name, _expected_field_typ)) => {
                    // The 'get_variant_field' case
                    let vir_field_ty = self.get_field_typ(span, variant_def, typ_args, &field_name)?;

                    //let vir_expected_field_ty = mid_ty_to_vir(
                    //    tcx,
                    //    &bctx.ctxt.verus_items,
                    //    bctx.fun_id,
                    //    span,
                    //    &expected_field_typ,
                    //    false,
                    //)?;
                    //if !types_equal(&vir_field_ty, &vir_expected_field_ty) {
                    //    return err_span(span, "field has the wrong type");
                    //}

                    let field_ident = field_ident_from_rust(&field_name);

                    Ok((dt.clone(), Some((field_ident, vir_field_ty))))
                }
            }
        } else {
            todo!();
        }
    }
}
