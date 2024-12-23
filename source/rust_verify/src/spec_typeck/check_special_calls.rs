use crate::spec_typeck::State;
use crate::verus_items::{
    self, ArithItem, AssertItem, BinaryOpItem, BuiltinFunctionItem, ChainedItem, CompilableOprItem,
    DirectiveItem, EqualityItem, ExprItem, QuantItem, RustItem, SpecArithItem,
    SpecGhostTrackedItem, SpecItem, SpecLiteralItem, SpecOrdItem, UnaryOpItem, VerusItem,
};
use vir::ast::{Typ, TypX, VarBinderX, ExprX, BinaryOp, CallTarget, Mode, ArithOp, StmtX, IntRange, Constant, FunX, CallTargetKind, AutospecUsage, Dt, Ident, VirErr, InequalityOp, Typs, Quant};
use crate::{unsupported_err, unsupported_err_unless};
use rustc_hir::{Expr, ExprKind, Node, QPath};
use rustc_span::Span;
use vir::ast_util::bool_typ;

impl<'a, 'tcx> State<'a, 'tcx> {
    pub fn check_call_rust_item(&mut self, _rust_item: RustItem) -> Result<vir::ast::Expr, VirErr> {
        todo!();
    }

    pub fn check_call_verus_item(
        &mut self,
        verus_item: &VerusItem,
        expr: &'tcx Expr<'tcx>,
        args: &'tcx [Expr<'tcx>],
    ) -> Result<Option<vir::ast::Expr>, VirErr> {
        let bctx = self.bctx;
        let mk_expr = |typ: &Typ, x: ExprX| Ok(Some(bctx.spanned_typed_new(expr.span, typ, x)));

        match verus_item {
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
            _ => {
                dbg!(verus_item);
                todo!();
            }
        }
    }

    fn check_2_args(
        &mut self,
        span: Span,
        args: &'tcx [Expr<'tcx>],
    ) -> Result<(vir::ast::Expr, vir::ast::Expr), VirErr> {
        unsupported_err_unless!(args.len() == 2, span, "expected 2 arguments", &args);
        let e0 = self.check_expr(&args[0])?;
        let e1 = self.check_expr(&args[1])?;
        Ok((e0, e1))
    }
}
