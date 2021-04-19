use crate::ast::{BinaryOp, Ident, Params, Typ, UnaryOp};
use crate::sst::{Exp, ExpX, Stm, StmX};
use crate::util::box_slice_map;
use air::ast::{CommandX, Commands, Decl, DeclX, Expr, ExprX, MultiOp, QueryX, Stmt, StmtX};
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
        ExpX::Call(x, args) => {
            Rc::new(ExprX::Apply(x.clone(), Rc::new(box_slice_map(args, exp_to_expr))))
        }
        ExpX::Unary(op, exp) => match op {
            UnaryOp::Not => Rc::new(ExprX::Unary(air::ast::UnaryOp::Not, exp_to_expr(exp))),
        },
        ExpX::Binary(op, lhs, rhs) => {
            let lh = exp_to_expr(lhs);
            let rh = exp_to_expr(rhs);
            let expx = match op {
                BinaryOp::And => ExprX::Multi(MultiOp::And, Rc::new(Box::new([lh, rh]))),
                BinaryOp::Or => ExprX::Multi(MultiOp::Or, Rc::new(Box::new([lh, rh]))),
                BinaryOp::Add => ExprX::Multi(MultiOp::Add, Rc::new(Box::new([lh, rh]))),
                BinaryOp::Sub => ExprX::Multi(MultiOp::Sub, Rc::new(Box::new([lh, rh]))),
                BinaryOp::Mul => ExprX::Multi(MultiOp::Mul, Rc::new(Box::new([lh, rh]))),
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
                        BinaryOp::Add => panic!("internal error"),
                        BinaryOp::Sub => panic!("internal error"),
                        BinaryOp::Mul => panic!("internal error"),
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

pub fn stm_to_stmt(stm: &Stm, decls: &mut Vec<Decl>) -> Option<Stmt> {
    match &stm.x {
        StmX::Assume(expr) => Some(Rc::new(StmtX::Assume(exp_to_expr(&expr)))),
        StmX::Assert(expr) => {
            let air_expr = exp_to_expr(&expr);
            let option_span = Rc::new(Some(stm.span.clone()));
            Some(Rc::new(StmtX::Assert(option_span, air_expr)))
        }
        StmX::Block(stms) => {
            let stmts = stms.iter().filter_map(|s| stm_to_stmt(s, decls)).collect::<Vec<_>>();
            Some(Rc::new(StmtX::Block(Rc::new(stmts.into_boxed_slice()))))
        }
        StmX::Decl(ident, typ) => {
            decls.push(Rc::new(DeclX::Const(suffixed_id(&ident), typ_to_air(&typ))));
            None
        }
    }
}

pub fn typ_to_air(typ: &Typ) -> air::ast::Typ {
    match typ {
        Typ::Int => Rc::new(air::ast::TypX::Int),
        Typ::Bool => Rc::new(air::ast::TypX::Bool),
    }
}

pub fn stm_to_air(params: &Params, stm: &Stm) -> Commands {
    let mut local = params
        .iter()
        .map(|param| Rc::new(DeclX::Const(suffixed_id(&param.x.name), typ_to_air(&param.x.typ))))
        .collect::<Vec<Decl>>();
    let assertion = stm_to_stmt(&stm, &mut local)
        .unwrap_or(Rc::new(StmtX::Block(Rc::new(vec![].into_boxed_slice()))));
    let query = Rc::new(QueryX { local: Rc::new(local.into_boxed_slice()), assertion });
    let command = Rc::new(CommandX::CheckValid(query));
    Rc::new(Box::new([command]))
}
