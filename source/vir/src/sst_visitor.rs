use crate::def::Spanned;
use crate::sst::{Exp, ExpX};
use std::rc::Rc;

pub(crate) fn map_exp_visitor<F>(exp: &Exp, f: &mut F) -> Exp
where
    F: FnMut(&Exp) -> Exp,
{
    match &exp.x {
        ExpX::Const(_) => f(exp),
        ExpX::Var(_) => f(exp),
        ExpX::Call(x, es) => {
            let mut exps: Vec<Exp> = Vec::new();
            for e in es.iter() {
                exps.push(map_exp_visitor(e, f));
            }
            let exp = Spanned::new(exp.span.clone(), ExpX::Call(x.clone(), Rc::new(exps)));
            f(&exp)
        }
        ExpX::Field(lhs, name) => {
            let lhs1 = map_exp_visitor(lhs, f);
            let exp = Spanned::new(exp.span.clone(), ExpX::Field(lhs1, name.clone()));
            f(&exp)
        }
        ExpX::Unary(op, e1) => {
            let expr1 = map_exp_visitor(e1, f);
            let exp = Spanned::new(exp.span.clone(), ExpX::Unary(*op, expr1));
            f(&exp)
        }
        ExpX::Binary(op, e1, e2) => {
            let expr1 = map_exp_visitor(e1, f);
            let expr2 = map_exp_visitor(e2, f);
            let exp = Spanned::new(exp.span.clone(), ExpX::Binary(*op, expr1, expr2));
            f(&exp)
        }
    }
}
