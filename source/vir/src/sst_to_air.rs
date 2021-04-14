use crate::ast::{BinaryOp, Ident, Params, Typ, UnaryOp};
use crate::sst::{Exp, ExpX, Stm, StmX};
use crate::util::box_slice_map;
use air::ast::{CommandX, Commands, DeclarationX, Expr, ExprX, LogicalOp, QueryX, Stmt, StmtX};
use std::rc::Rc;

pub const SUFFIX_USER_ID: &str = "@";

fn suffixed_id(ident: &Ident) -> Ident {
    Rc::new(ident.to_string() + SUFFIX_USER_ID)
}

fn exp_to_expr(exp: &Exp) -> Expr {
    match &exp.x {
        ExpX::Const(c) => {
            let expr = Rc::new(ExprX::Const(c.clone()));
            expr
        }
        ExpX::Var(x) => Rc::new(ExprX::Var(suffixed_id(x))),
        ExpX::Unary(op, exp) => match op {
            UnaryOp::Not => Rc::new(ExprX::Unary(air::ast::UnaryOp::Not, exp_to_expr(exp))),
        },
        ExpX::Binary(op, lhs, rhs) => {
            let lh = exp_to_expr(lhs);
            let rh = exp_to_expr(rhs);
            let expx = match op {
                BinaryOp::And => ExprX::Logical(LogicalOp::And, Rc::new(Box::new([lh, rh]))),
                BinaryOp::Or => ExprX::Logical(LogicalOp::Or, Rc::new(Box::new([lh, rh]))),
                BinaryOp::Ne => {
                    let eq = ExprX::Binary(air::ast::BinaryOp::Eq, lh, rh);
                    ExprX::Unary(air::ast::UnaryOp::Not, Rc::new(eq))
                }
                _ => {
                    let aop = match op {
                        BinaryOp::And => panic!("internal error"),
                        BinaryOp::Or => panic!("internal error"),
                        BinaryOp::Implies => air::ast::BinaryOp::Implies,
                        BinaryOp::Eq => air::ast::BinaryOp::Eq,
                        BinaryOp::Ne => panic!("internal error"),
                        BinaryOp::Le => air::ast::BinaryOp::Le,
                        BinaryOp::Ge => air::ast::BinaryOp::Ge,
                        BinaryOp::Lt => air::ast::BinaryOp::Lt,
                        BinaryOp::Gt => air::ast::BinaryOp::Gt,
                        BinaryOp::Add => air::ast::BinaryOp::Add,
                        BinaryOp::Sub => air::ast::BinaryOp::Sub,
                        BinaryOp::Mul => air::ast::BinaryOp::Mul,
                        BinaryOp::EuclideanDiv => air::ast::BinaryOp::EuclideanDiv,
                        BinaryOp::EuclideanMod => air::ast::BinaryOp::EuclideanMod,
                    };
                    ExprX::Binary(aop, lh, rh)
                }
            };
            Rc::new(expx)
        }
    }
}

pub fn stm_to_stmt(stm: &Stm) -> Stmt {
    match &stm.x {
        StmX::Assume(expr) => Rc::new(StmtX::Assume(exp_to_expr(&expr))),
        StmX::Assert(expr) => {
            let air_expr = exp_to_expr(&expr);
            let option_span = Rc::new(Some(stm.span.clone()));
            Rc::new(StmtX::Assert(option_span, air_expr))
        }
        StmX::Block(stms) => Rc::new(StmtX::Block(Rc::new(box_slice_map(stms, stm_to_stmt)))),
    }
}

pub fn typ_to_air(typ: &Typ) -> air::ast::Typ {
    match typ {
        Typ::Int => air::ast::Typ::Int,
        Typ::Bool => air::ast::Typ::Bool,
    }
}

pub fn stm_to_air(params: &Params, stm: &Stm) -> Commands {
    let local = box_slice_map(params, |param| {
        Rc::new(DeclarationX::Const(suffixed_id(&param.x.name), typ_to_air(&param.x.typ)))
    });
    let assertion = stm_to_stmt(&stm);
    let query = Rc::new(QueryX { local: Rc::new(local), assertion });
    let command = Rc::new(CommandX::CheckValid(query));
    Rc::new(Box::new([command]))
}
