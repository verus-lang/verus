use crate::ast::VirErr;
use crate::def::Spanned;
use crate::sst::{Bnd, BndX, Exp, ExpX, Trig};
use air::ast::{Binder, BinderX};
use std::rc::Rc;

pub(crate) fn map_exp_visitor_bind<FB, F>(exp: &Exp, fb: &mut FB, f: &mut F) -> Result<Exp, VirErr>
where
    FB: FnMut(&Bnd) -> Result<Bnd, VirErr>,
    F: FnMut(&Exp) -> Result<Exp, VirErr>,
{
    match &exp.x {
        ExpX::Const(_) => f(exp),
        ExpX::Var(_) => f(exp),
        ExpX::Old(_, _) => f(exp),
        ExpX::Call(x, es) => {
            let mut exps: Vec<Exp> = Vec::new();
            for e in es.iter() {
                exps.push(map_exp_visitor_bind(e, fb, f)?);
            }
            let exp = Spanned::new(exp.span.clone(), ExpX::Call(x.clone(), Rc::new(exps)));
            f(&exp)
        }
        ExpX::Field { lhs, datatype_name, field_name } => {
            let lhs1 = map_exp_visitor_bind(lhs, fb, f)?;
            let exp = Spanned::new(
                exp.span.clone(),
                ExpX::Field {
                    lhs: lhs1,
                    datatype_name: datatype_name.clone(),
                    field_name: field_name.clone(),
                },
            );
            f(&exp)
        }
        ExpX::Unary(op, e1) => {
            let expr1 = map_exp_visitor_bind(e1, fb, f)?;
            let exp = Spanned::new(exp.span.clone(), ExpX::Unary(*op, expr1));
            f(&exp)
        }
        ExpX::Binary(op, e1, e2) => {
            let expr1 = map_exp_visitor_bind(e1, fb, f)?;
            let expr2 = map_exp_visitor_bind(e2, fb, f)?;
            let exp = Spanned::new(exp.span.clone(), ExpX::Binary(*op, expr1, expr2));
            f(&exp)
        }
        ExpX::Ternary(op, e1, e2, e3) => {
            let expr1 = map_exp_visitor_bind(e1, fb, f)?;
            let expr2 = map_exp_visitor_bind(e2, fb, f)?;
            let expr3 = map_exp_visitor_bind(e3, fb, f)?;
            let exp = Spanned::new(exp.span.clone(), ExpX::Ternary(*op, expr1, expr2, expr3));
            f(&exp)
        }
        ExpX::Bind(bnd, e1) => {
            let bndx = match &bnd.x {
                BndX::Let(bs) => {
                    let mut binders: Vec<Binder<Exp>> = Vec::new();
                    for b in bs.iter() {
                        let a = map_exp_visitor_bind(&b.a, fb, f)?;
                        binders.push(Rc::new(BinderX { name: b.name.clone(), a }));
                    }
                    BndX::Let(Rc::new(binders))
                }
                BndX::Quant(quant, binders, ts) => {
                    let mut triggers: Vec<Trig> = Vec::new();
                    for t in ts.iter() {
                        let mut exprs: Vec<Exp> = Vec::new();
                        for exp in t.iter() {
                            exprs.push(map_exp_visitor_bind(exp, fb, f)?);
                        }
                        triggers.push(Rc::new(exprs));
                    }
                    BndX::Quant(*quant, binders.clone(), Rc::new(triggers))
                }
            };
            let bnd = fb(&Spanned::new(bnd.span.clone(), bndx))?;
            let e1 = map_exp_visitor_bind(e1, fb, f)?;
            let expx = ExpX::Bind(bnd, e1);
            let exp = Spanned::new(exp.span.clone(), expx);
            f(&exp)
        }
    }
}

pub(crate) fn map_exp_visitor<F>(exp: &Exp, f: &mut F) -> Exp
where
    F: FnMut(&Exp) -> Exp,
{
    map_exp_visitor_bind(exp, &mut |b| Ok(b.clone()), &mut |e| Ok(f(e))).unwrap()
}
