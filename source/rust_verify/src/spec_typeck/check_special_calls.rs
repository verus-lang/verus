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
            _ => todo!(),
        }
    }
}
