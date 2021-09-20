use crate::ast::{Ident, VirErr};
use crate::def::Spanned;
use crate::sst::{BndX, Exp, ExpX, Stm, StmX, Trig};
use air::ast::{Binder, BinderX};
use air::scope_map::ScopeMap;
use std::collections::HashMap;
use std::sync::Arc;

pub(crate) fn map_exp_visitor_bind<F>(
    exp: &Exp,
    map: &mut ScopeMap<Ident, bool>,
    f: &mut F,
) -> Result<Exp, VirErr>
where
    F: FnMut(&Exp, &mut ScopeMap<Ident, bool>) -> Result<Exp, VirErr>,
{
    match &exp.x {
        ExpX::Const(_) => f(exp, map),
        ExpX::Var(_) => f(exp, map),
        ExpX::Old(_, _) => f(exp, map),
        ExpX::Call(rec, x, typs, es) => {
            let mut exps: Vec<Exp> = Vec::new();
            for e in es.iter() {
                exps.push(map_exp_visitor_bind(e, map, f)?);
            }
            let exp = Spanned::new(
                exp.span.clone(),
                ExpX::Call(*rec, x.clone(), typs.clone(), Arc::new(exps)),
            );
            f(&exp, map)
        }
        ExpX::Ctor(path, ident, binders) => {
            let mapped_binders = binders
                .iter()
                .map(|b| b.map_result(|a| map_exp_visitor_bind(a, map, f)))
                .collect::<Result<Vec<_>, _>>()?;
            let exp = Spanned::new(
                exp.span.clone(),
                ExpX::Ctor(path.clone(), ident.clone(), Arc::new(mapped_binders)),
            );
            f(&exp, map)
        }
        ExpX::Field { lhs, datatype, field_name } => {
            let lhs1 = map_exp_visitor_bind(lhs, map, f)?;
            let exp = Spanned::new(
                exp.span.clone(),
                ExpX::Field {
                    lhs: lhs1,
                    datatype: datatype.clone(),
                    field_name: field_name.clone(),
                },
            );
            f(&exp, map)
        }
        ExpX::Unary(op, e1) => {
            let expr1 = map_exp_visitor_bind(e1, map, f)?;
            let exp = Spanned::new(exp.span.clone(), ExpX::Unary(*op, expr1));
            f(&exp, map)
        }
        ExpX::UnaryOpr(op, e1) => {
            let expr1 = map_exp_visitor_bind(e1, map, f)?;
            let exp = Spanned::new(exp.span.clone(), ExpX::UnaryOpr(op.clone(), expr1));
            f(&exp, map)
        }
        ExpX::Binary(op, e1, e2) => {
            let expr1 = map_exp_visitor_bind(e1, map, f)?;
            let expr2 = map_exp_visitor_bind(e2, map, f)?;
            let exp = Spanned::new(exp.span.clone(), ExpX::Binary(*op, expr1, expr2));
            f(&exp, map)
        }
        ExpX::If(e1, e2, e3) => {
            let expr1 = map_exp_visitor_bind(e1, map, f)?;
            let expr2 = map_exp_visitor_bind(e2, map, f)?;
            let expr3 = map_exp_visitor_bind(e3, map, f)?;
            let exp = Spanned::new(exp.span.clone(), ExpX::If(expr1, expr2, expr3));
            f(&exp, map)
        }
        ExpX::Bind(bnd, e1) => {
            let mut bvars: Vec<(Ident, bool)> = Vec::new();
            let bndx = match &bnd.x {
                BndX::Let(bs) => {
                    let mut binders: Vec<Binder<Exp>> = Vec::new();
                    for b in bs.iter() {
                        let a = map_exp_visitor_bind(&b.a, map, f)?;
                        binders.push(Arc::new(BinderX { name: b.name.clone(), a }));
                        bvars.push((b.name.clone(), false));
                    }
                    BndX::Let(Arc::new(binders))
                }
                BndX::Quant(quant, binders, ts) => {
                    let mut triggers: Vec<Trig> = Vec::new();
                    for b in binders.iter() {
                        bvars.push((b.name.clone(), true));
                    }
                    for t in ts.iter() {
                        let mut exprs: Vec<Exp> = Vec::new();
                        for exp in t.iter() {
                            exprs.push(map_exp_visitor_bind(exp, map, f)?);
                        }
                        triggers.push(Arc::new(exprs));
                    }
                    BndX::Quant(*quant, binders.clone(), Arc::new(triggers))
                }
            };
            let bnd = Spanned::new(bnd.span.clone(), bndx);
            map.push_scope(true);
            for (x, is_quant) in bvars {
                let _ = map.insert(x, is_quant);
            }
            let e1 = map_exp_visitor_bind(e1, map, f)?;
            map.pop_scope();
            let expx = ExpX::Bind(bnd, e1);
            let exp = Spanned::new(exp.span.clone(), expx);
            f(&exp, map)
        }
    }
}

pub(crate) fn map_exp_visitor<F>(exp: &Exp, f: &mut F) -> Exp
where
    F: FnMut(&Exp) -> Exp,
{
    let mut map: ScopeMap<Ident, bool> = ScopeMap::new();
    map_exp_visitor_bind(exp, &mut map, &mut |e, _| Ok(f(e))).unwrap()
}

pub(crate) fn exp_rename_vars(exp: &Exp, map: &HashMap<Ident, Ident>) -> Exp {
    let mut shadows: ScopeMap<Ident, bool> = ScopeMap::new();
    map_exp_visitor_bind(exp, &mut shadows, &mut |exp, shadows| match &exp.x {
        ExpX::Var(x) if map.contains_key(x) && !shadows.contains_key(x) => {
            Ok(Spanned::new(exp.span.clone(), ExpX::Var(map[x].clone())))
        }
        _ => Ok(exp.clone()),
    })
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
            let stm = Spanned::new(stm.span.clone(), StmX::Block(Arc::new(stms)));
            f(&stm)
        }
    }
}
