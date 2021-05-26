use crate::ast::{Ident, VirErr};
use crate::def::Spanned;
use crate::sst::{Bnd, BndX, Exp, ExpX, Stm, StmX, Trig};
use air::ast::{Binder, BinderX, Binders};
use std::collections::HashMap;
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
        ExpX::Call(x, typs, es) => {
            let mut exps: Vec<Exp> = Vec::new();
            for e in es.iter() {
                exps.push(map_exp_visitor_bind(e, fb, f)?);
            }
            let exp =
                Spanned::new(exp.span.clone(), ExpX::Call(x.clone(), typs.clone(), Rc::new(exps)));
            f(&exp)
        }
        ExpX::Ctor(path, ident, binders) => {
            let mapped_binders = binders
                .iter()
                .map(|b| b.map_result(|a| map_exp_visitor_bind(a, fb, f)))
                .collect::<Result<Vec<_>, _>>()?;
            let exp = Spanned::new(
                exp.span.clone(),
                ExpX::Ctor(path.clone(), ident.clone(), Rc::new(mapped_binders)),
            );
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
        ExpX::UnaryOpr(op, e1) => {
            let expr1 = map_exp_visitor_bind(e1, fb, f)?;
            let exp = Spanned::new(exp.span.clone(), ExpX::UnaryOpr(op.clone(), expr1));
            f(&exp)
        }
        ExpX::Binary(op, e1, e2) => {
            let expr1 = map_exp_visitor_bind(e1, fb, f)?;
            let expr2 = map_exp_visitor_bind(e2, fb, f)?;
            let exp = Spanned::new(exp.span.clone(), ExpX::Binary(*op, expr1, expr2));
            f(&exp)
        }
        ExpX::If(e1, e2, e3) => {
            let expr1 = map_exp_visitor_bind(e1, fb, f)?;
            let expr2 = map_exp_visitor_bind(e2, fb, f)?;
            let expr3 = map_exp_visitor_bind(e3, fb, f)?;
            let exp = Spanned::new(exp.span.clone(), ExpX::If(expr1, expr2, expr3));
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

fn bump_shadowed<A: Clone>(shadowed: &mut HashMap<Ident, i64>, incr: i64, binders: &Binders<A>) {
    for binder in binders.iter() {
        *shadowed.get_mut(&binder.name).unwrap() += incr;
    }
}

pub(crate) fn exp_rename_vars(exp: &Exp, map: &HashMap<Ident, Ident>) -> Exp {
    let shadowed: HashMap<Ident, i64> = map.iter().map(|(x, _)| (x.clone(), 0)).collect();
    let shadowed_cell = std::cell::RefCell::new(shadowed);
    map_exp_visitor_bind(
        exp,
        &mut |bnd| {
            let mut shadowed = shadowed_cell.borrow_mut();
            match &bnd.x {
                BndX::Let(bs) => {
                    bump_shadowed(&mut shadowed, 1, bs);
                }
                BndX::Quant(_, bs, _) => {
                    bump_shadowed(&mut shadowed, 1, bs);
                }
            }
            Ok(bnd.clone())
        },
        &mut |exp| {
            let mut shadowed = shadowed_cell.borrow_mut();
            match &exp.x {
                ExpX::Var(x) if map.contains_key(x) && shadowed[x] == 0 => {
                    Ok(Spanned::new(exp.span.clone(), ExpX::Var(map[x].clone())))
                }
                ExpX::Bind(bnd, _) => {
                    match &bnd.x {
                        BndX::Let(bs) => {
                            bump_shadowed(&mut shadowed, -1, bs);
                        }
                        BndX::Quant(_, bs, _) => {
                            bump_shadowed(&mut shadowed, -1, bs);
                        }
                    }
                    Ok(exp.clone())
                }
                _ => Ok(exp.clone()),
            }
        },
    )
    .unwrap()
}

pub(crate) fn map_stm_visitor<F>(stm: &Stm, f: &mut F) -> Result<Stm, VirErr>
where
    F: FnMut(&Stm) -> Result<Stm, VirErr>,
{
    match &stm.x {
        StmX::Call(_, _, _, _) => f(stm),
        StmX::Assert(_) => f(stm),
        StmX::Assume(_) => f(stm),
        StmX::Decl { .. } => f(stm),
        StmX::Assign(_, _) => f(stm),
        StmX::Fuel(_, _) => f(stm),
        StmX::If(cond, lhs, rhs) => {
            let lhs = map_stm_visitor(lhs, f)?;
            let rhs = rhs.as_ref().map(|rhs| map_stm_visitor(rhs, f)).transpose()?;
            let stm = Spanned::new(stm.span.clone(), StmX::If(cond.clone(), lhs, rhs));
            f(&stm)
        }
        StmX::While { cond, body, invs, typ_inv_vars, modified_vars } => {
            let body = map_stm_visitor(body, f)?;
            let stm = Spanned::new(
                stm.span.clone(),
                StmX::While {
                    cond: cond.clone(),
                    body,
                    invs: invs.clone(),
                    typ_inv_vars: typ_inv_vars.clone(),
                    modified_vars: modified_vars.clone(),
                },
            );
            f(&stm)
        }
        StmX::Block(ss) => {
            let mut stms: Vec<Stm> = Vec::new();
            for s in ss.iter() {
                stms.push(map_stm_visitor(s, f)?);
            }
            let stm = Spanned::new(stm.span.clone(), StmX::Block(Rc::new(stms)));
            f(&stm)
        }
    }
}
