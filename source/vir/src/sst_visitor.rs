use crate::ast::{Ident, SpannedTyped, VirErr};
use crate::def::Spanned;
use crate::sst::{BndX, Exp, ExpX, Stm, StmX, Trig, UniqueIdent};
use crate::util::vec_map;
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
    let exp_new = |e: ExpX| SpannedTyped::new(&exp.span, &exp.typ, e);
    match &exp.x {
        ExpX::Const(_) => f(exp, map),
        ExpX::Var(..) => f(exp, map),
        ExpX::VarAt(..) => f(exp, map),
        ExpX::Old(..) => f(exp, map),
        ExpX::Call(x, typs, es) => {
            let mut exps: Vec<Exp> = Vec::new();
            for e in es.iter() {
                exps.push(map_exp_visitor_bind(e, map, f)?);
            }
            let exp = exp_new(ExpX::Call(x.clone(), typs.clone(), Arc::new(exps)));
            f(&exp, map)
        }
        ExpX::CallLambda(typ, e0, es) => {
            let e0 = map_exp_visitor_bind(e0, map, f)?;
            let mut exps: Vec<Exp> = Vec::new();
            for e in es.iter() {
                exps.push(map_exp_visitor_bind(e, map, f)?);
            }
            let exp = exp_new(ExpX::CallLambda(typ.clone(), e0, Arc::new(exps)));
            f(&exp, map)
        }
        ExpX::Ctor(path, ident, binders) => {
            let mapped_binders = binders
                .iter()
                .map(|b| b.map_result(|a| map_exp_visitor_bind(a, map, f)))
                .collect::<Result<Vec<_>, _>>()?;
            let exp = exp_new(ExpX::Ctor(path.clone(), ident.clone(), Arc::new(mapped_binders)));
            f(&exp, map)
        }
        ExpX::Unary(op, e1) => {
            let expr1 = map_exp_visitor_bind(e1, map, f)?;
            let exp = exp_new(ExpX::Unary(*op, expr1));
            f(&exp, map)
        }
        ExpX::UnaryOpr(op, e1) => {
            let expr1 = map_exp_visitor_bind(e1, map, f)?;
            let exp = exp_new(ExpX::UnaryOpr(op.clone(), expr1));
            f(&exp, map)
        }
        ExpX::Binary(op, e1, e2) => {
            let expr1 = map_exp_visitor_bind(e1, map, f)?;
            let expr2 = map_exp_visitor_bind(e2, map, f)?;
            let exp = exp_new(ExpX::Binary(*op, expr1, expr2));
            f(&exp, map)
        }
        ExpX::If(e1, e2, e3) => {
            let expr1 = map_exp_visitor_bind(e1, map, f)?;
            let expr2 = map_exp_visitor_bind(e2, map, f)?;
            let expr3 = map_exp_visitor_bind(e3, map, f)?;
            let exp = exp_new(ExpX::If(expr1, expr2, expr3));
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
                BndX::Lambda(_) => bnd.x.clone(),
                BndX::Choose(binder, ts) => {
                    let mut triggers: Vec<Trig> = Vec::new();
                    bvars.push((binder.name.clone(), true));
                    for t in ts.iter() {
                        let mut exprs: Vec<Exp> = Vec::new();
                        for exp in t.iter() {
                            exprs.push(map_exp_visitor_bind(exp, map, f)?);
                        }
                        triggers.push(Arc::new(exprs));
                    }
                    BndX::Choose(binder.clone(), Arc::new(triggers))
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
            let exp = exp_new(expx);
            f(&exp, map)
        }
    }
}

pub(crate) fn map_exp_visitor_result<F>(exp: &Exp, f: &mut F) -> Result<Exp, VirErr>
where
    F: FnMut(&Exp) -> Result<Exp, VirErr>,
{
    let mut map: ScopeMap<Ident, bool> = ScopeMap::new();
    map_exp_visitor_bind(exp, &mut map, &mut |e, _| f(e))
}

pub(crate) fn map_exp_visitor<F>(exp: &Exp, f: &mut F) -> Exp
where
    F: FnMut(&Exp) -> Exp,
{
    let mut map: ScopeMap<Ident, bool> = ScopeMap::new();
    map_exp_visitor_bind(exp, &mut map, &mut |e, _| Ok(f(e))).unwrap()
}

pub(crate) fn exp_rename_vars(exp: &Exp, map: &HashMap<UniqueIdent, UniqueIdent>) -> Exp {
    map_exp_visitor(exp, &mut |exp| match &exp.x {
        ExpX::Var(x) if map.contains_key(x) => {
            SpannedTyped::new(&exp.span, &exp.typ, ExpX::Var(map[x].clone()))
        }
        _ => exp.clone(),
    })
}

pub(crate) fn map_stm_visitor<F>(stm: &Stm, f: &mut F) -> Result<Stm, VirErr>
where
    F: FnMut(&Stm) -> Result<Stm, VirErr>,
{
    match &stm.x {
        StmX::Call(..) => f(stm),
        StmX::Assert(_, _) => f(stm),
        StmX::Assume(_) => f(stm),
        StmX::Assign { .. } => f(stm),
        StmX::Fuel(..) => f(stm),
        StmX::DeadEnd(s) => {
            let s = map_stm_visitor(s, f)?;
            let stm = Spanned::new(stm.span.clone(), StmX::DeadEnd(s));
            f(&stm)
        }
        StmX::If(cond, lhs, rhs) => {
            let lhs = map_stm_visitor(lhs, f)?;
            let rhs = rhs.as_ref().map(|rhs| map_stm_visitor(rhs, f)).transpose()?;
            let stm = Spanned::new(stm.span.clone(), StmX::If(cond.clone(), lhs, rhs));
            f(&stm)
        }
        StmX::While { cond_stms, cond_exp, body, invs, typ_inv_vars, modified_vars } => {
            let mut cs: Vec<Stm> = Vec::new();
            for s in cond_stms.iter() {
                cs.push(map_stm_visitor(s, f)?);
            }
            let body = map_stm_visitor(body, f)?;
            let stm = Spanned::new(
                stm.span.clone(),
                StmX::While {
                    cond_stms: Arc::new(cs),
                    cond_exp: cond_exp.clone(),
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
        StmX::OpenInvariant(inv, ident, ty, body) => {
            let body = map_stm_visitor(body, f)?;
            let stm = Spanned::new(
                stm.span.clone(),
                StmX::OpenInvariant(inv.clone(), ident.clone(), ty.clone(), body),
            );
            f(&stm)
        }
    }
}

pub(crate) fn map_stm_exp_visitor<F>(stm: &Stm, f: &F) -> Result<Stm, VirErr>
where
    F: Fn(&Exp) -> Exp,
{
    map_stm_visitor(stm, &mut |stm| {
        let span = stm.span.clone();
        let stm = match &stm.x {
            StmX::Call(path, typs, exps, dest) => {
                let exps = Arc::new(vec_map(exps, f));
                Spanned::new(span, StmX::Call(path.clone(), typs.clone(), exps, (*dest).clone()))
            }
            StmX::Assert(span2, exp) => Spanned::new(span, StmX::Assert(span2.clone(), f(exp))),
            StmX::Assume(exp) => Spanned::new(span, StmX::Assume(f(exp))),
            StmX::Assign { lhs, rhs, is_init } => {
                let rhs = f(rhs);
                Spanned::new(span, StmX::Assign { lhs: lhs.clone(), rhs, is_init: *is_init })
            }
            StmX::Fuel(..) => stm.clone(),
            StmX::DeadEnd(..) => stm.clone(),
            StmX::If(exp, s1, s2) => {
                let exp = f(exp);
                Spanned::new(span, StmX::If(exp, s1.clone(), s2.clone()))
            }
            StmX::While { cond_stms, cond_exp, body, invs, typ_inv_vars, modified_vars } => {
                let cond_exp = f(cond_exp);
                let invs = Arc::new(vec_map(invs, f));
                Spanned::new(
                    span,
                    StmX::While {
                        cond_stms: cond_stms.clone(),
                        cond_exp,
                        body: body.clone(),
                        invs,
                        typ_inv_vars: typ_inv_vars.clone(),
                        modified_vars: modified_vars.clone(),
                    },
                )
            }
            StmX::Block(_) => stm.clone(),
            StmX::OpenInvariant(inv, ident, ty, body) => {
                let inv = f(inv);
                Spanned::new(
                    span,
                    StmX::OpenInvariant(inv, ident.clone(), ty.clone(), body.clone()),
                )
            }
        };
        Ok(stm)
    })
}
