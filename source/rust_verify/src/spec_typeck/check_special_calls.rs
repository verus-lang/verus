use crate::spec_typeck::State;
use crate::verus_items::{
    self, ArithItem, AssertItem, BinaryOpItem, BuiltinFunctionItem, ChainedItem, CompilableOprItem,
    DirectiveItem, EqualityItem, ExprItem, QuantItem, RustItem, SpecArithItem,
    SpecGhostTrackedItem, SpecItem, SpecLiteralItem, SpecOrdItem, UnaryOpItem, VerusItem,
};
use vir::ast::{Typ, TypX, VarBinderX, ExprX, BinaryOp, CallTarget, Mode, ArithOp, StmtX, IntRange, Constant, FunX, CallTargetKind, AutospecUsage, Dt, Ident, VirErr, InequalityOp, Typs};

impl<'a, 'tcx> State<'a, 'tcx> {
    pub fn check_call_rust_item(&mut self, _rust_item: RustItem) -> Result<vir::ast::Expr, VirErr> {
        todo!();
    }

    pub fn check_call_verus_item(&mut self, _verus_item: &VerusItem) -> Result<vir::ast::Expr, VirErr> {
        //match verus_item {
        //}
        todo!();
    }
}
