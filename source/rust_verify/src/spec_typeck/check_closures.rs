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
    pub fn check_closure(
        &mut self,
        closure: &'tcx Closure,
        expr: &'tcx Expr<'tcx>,
    ) -> Result<vir::ast::Expr, VirErr> {
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

        let x = ExprX::Closure(Arc::new(var_binders), body);
        Ok(self.bctx.spanned_typed_new(expr.span, &fntype, x))
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
