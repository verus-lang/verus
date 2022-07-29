use crate::ast::{Ident, SpannedTyped, Typ, UnaryOpr, VirErr};
use crate::def::Spanned;
use crate::sst::{BndX, Dest, Exp, ExpX, Exps, Stm, StmX, Trig, Trigs, UniqueIdent};
use crate::util::vec_map_result;
use crate::visitor::expr_visitor_control_flow;
pub(crate) use crate::visitor::VisitorControlFlow;
use air::ast::{Binder, BinderX, Binders};
use air::scope_map::ScopeMap;
use std::collections::HashMap;
use std::sync::Arc;

pub type VisitorScopeMap = ScopeMap<Ident, bool>;

pub(crate) fn exp_visitor_check<E, MF>(
    expr: &Exp,
    map: &mut VisitorScopeMap,
    mf: &mut MF,
) -> Result<(), E>
where
    MF: FnMut(&Exp, &mut VisitorScopeMap) -> Result<(), E>,
{
    match exp_visitor_dfs(expr, map, &mut |expr, map| match mf(expr, map) {
        Ok(()) => VisitorControlFlow::Recurse,
        Err(e) => VisitorControlFlow::Stop(e),
    }) {
        VisitorControlFlow::Recurse => Ok(()),
        VisitorControlFlow::Return => unreachable!(),
        VisitorControlFlow::Stop(e) => Err(e),
    }
}

pub(crate) fn exp_visitor_dfs<T, F>(
    exp: &Exp,
    map: &mut VisitorScopeMap,
    f: &mut F,
) -> VisitorControlFlow<T>
where
    F: FnMut(&Exp, &mut VisitorScopeMap) -> VisitorControlFlow<T>,
{
    match f(exp, map) {
        VisitorControlFlow::Stop(val) => VisitorControlFlow::Stop(val),
        VisitorControlFlow::Return => VisitorControlFlow::Recurse,
        VisitorControlFlow::Recurse => {
            match &exp.x {
                ExpX::Const(_)
                | ExpX::Var(..)
                | ExpX::VarAt(..)
                | ExpX::Old(..)
                | ExpX::VarLoc(..) => (),
                ExpX::Loc(e0) => {
                    expr_visitor_control_flow!(exp_visitor_dfs(e0, map, f));
                }
                ExpX::Call(_x, _typs, es) => {
                    for e in es.iter() {
                        expr_visitor_control_flow!(exp_visitor_dfs(e, map, f));
                    }
                }
                ExpX::CallLambda(_typ, e0, es) => {
                    expr_visitor_control_flow!(exp_visitor_dfs(e0, map, f));
                    for e in es.iter() {
                        expr_visitor_control_flow!(exp_visitor_dfs(e, map, f));
                    }
                }
                ExpX::Ctor(_path, _ident, binders) => {
                    for binder in binders.iter() {
                        expr_visitor_control_flow!(exp_visitor_dfs(&binder.a, map, f));
                    }
                }
                ExpX::Unary(_op, e1) => {
                    expr_visitor_control_flow!(exp_visitor_dfs(e1, map, f));
                }
                ExpX::UnaryOpr(_op, e1) => {
                    expr_visitor_control_flow!(exp_visitor_dfs(e1, map, f));
                }
                ExpX::Binary(_op, e1, e2) => {
                    expr_visitor_control_flow!(exp_visitor_dfs(e1, map, f));
                    expr_visitor_control_flow!(exp_visitor_dfs(e2, map, f));
                }
                ExpX::If(e1, e2, e3) => {
                    expr_visitor_control_flow!(exp_visitor_dfs(e1, map, f));
                    expr_visitor_control_flow!(exp_visitor_dfs(e2, map, f));
                    expr_visitor_control_flow!(exp_visitor_dfs(e3, map, f));
                }
                ExpX::WithTriggers(triggers, body) => {
                    for trigger in triggers.iter() {
                        for term in trigger.iter() {
                            expr_visitor_control_flow!(exp_visitor_dfs(term, map, f));
                        }
                    }
                    expr_visitor_control_flow!(exp_visitor_dfs(body, map, f));
                }
                ExpX::Bind(bnd, e1) => {
                    let mut bvars: Vec<(Ident, bool)> = Vec::new();
                    let mut trigs: Trigs = Arc::new(vec![]);
                    match &bnd.x {
                        BndX::Let(bs) => {
                            for b in bs.iter() {
                                expr_visitor_control_flow!(exp_visitor_dfs(&b.a, map, f));
                                bvars.push((b.name.clone(), false));
                            }
                        }
                        BndX::Quant(_quant, binders, ts) => {
                            for b in binders.iter() {
                                bvars.push((b.name.clone(), true));
                            }
                            trigs = ts.clone();
                        }
                        BndX::Lambda(params) => {
                            for b in params.iter() {
                                bvars.push((b.name.clone(), false));
                            }
                        }
                        BndX::Choose(params, ts, _) => {
                            for b in params.iter() {
                                bvars.push((b.name.clone(), true));
                            }
                            trigs = ts.clone();
                        }
                    }
                    map.push_scope(true);
                    for (x, is_triggered) in bvars {
                        let _ = map.insert(x, is_triggered);
                    }
                    for t in trigs.iter() {
                        for exp in t.iter() {
                            expr_visitor_control_flow!(exp_visitor_dfs(exp, map, f));
                        }
                    }
                    if let BndX::Choose(_, _, cond) = &bnd.x {
                        expr_visitor_control_flow!(exp_visitor_dfs(cond, map, f));
                    }
                    expr_visitor_control_flow!(exp_visitor_dfs(e1, map, f));
                    map.pop_scope();
                }
            }
            VisitorControlFlow::Recurse
        }
    }
}

pub(crate) fn stm_visitor_dfs<T, F>(stm: &Stm, f: &mut F) -> VisitorControlFlow<T>
where
    F: FnMut(&Stm) -> VisitorControlFlow<T>,
{
    match f(stm) {
        VisitorControlFlow::Stop(val) => VisitorControlFlow::Stop(val),
        VisitorControlFlow::Return => VisitorControlFlow::Recurse,
        VisitorControlFlow::Recurse => {
            match &stm.x {
                StmX::Call(..)
                | StmX::Assert(_, _)
                | StmX::Assume(_)
                | StmX::Assign { .. }
                | StmX::AssertBV { .. }
                | StmX::AssertBitVector { .. }
                | StmX::Fuel(..) => (),
                StmX::DeadEnd(s) => {
                    expr_visitor_control_flow!(stm_visitor_dfs(s, f));
                }
                StmX::If(_cond, lhs, rhs) => {
                    expr_visitor_control_flow!(stm_visitor_dfs(lhs, f));
                    if let Some(rhs) = rhs {
                        expr_visitor_control_flow!(stm_visitor_dfs(rhs, f));
                    }
                }
                StmX::AssertQuery { body, mode: _, typ_inv_vars: _ } => {
                    expr_visitor_control_flow!(stm_visitor_dfs(body, f));
                }
                StmX::While {
                    cond_stms,
                    cond_exp: _,
                    body,
                    invs: _,
                    typ_inv_vars: _,
                    modified_vars: _,
                } => {
                    for s in cond_stms.iter() {
                        expr_visitor_control_flow!(stm_visitor_dfs(s, f));
                    }
                    expr_visitor_control_flow!(stm_visitor_dfs(body, f));
                }
                StmX::OpenInvariant(_inv, _ident, _ty, body, _atomicity) => {
                    expr_visitor_control_flow!(stm_visitor_dfs(body, f));
                }
                StmX::Block(ss) => {
                    for s in ss.iter() {
                        expr_visitor_control_flow!(stm_visitor_dfs(s, f));
                    }
                }
            }
            VisitorControlFlow::Recurse
        }
    }
}

#[allow(dead_code)]
pub(crate) fn stm_exp_visitor_dfs<T, F>(stm: &Stm, f: &mut F) -> VisitorControlFlow<T>
where
    F: FnMut(&Exp, &mut VisitorScopeMap) -> VisitorControlFlow<T>,
{
    stm_visitor_dfs(stm, &mut |stm| {
        match &stm.x {
            StmX::Call(_path, _mode, _typs, exps, _dest) => {
                for exp in exps.iter() {
                    expr_visitor_control_flow!(exp_visitor_dfs(exp, &mut ScopeMap::new(), f));
                }
            }
            StmX::Assert(_span2, exp) => {
                expr_visitor_control_flow!(exp_visitor_dfs(exp, &mut ScopeMap::new(), f))
            }
            StmX::AssertBV(exp) => {
                expr_visitor_control_flow!(exp_visitor_dfs(exp, &mut ScopeMap::new(), f))
            }
            StmX::AssertBitVector { requires, ensures } => {
                for req in requires.iter() {
                    expr_visitor_control_flow!(exp_visitor_dfs(req, &mut ScopeMap::new(), f));
                }
                for ens in ensures.iter() {
                    expr_visitor_control_flow!(exp_visitor_dfs(ens, &mut ScopeMap::new(), f));
                }
            }
            StmX::AssertQuery { body: _, typ_inv_vars: _, mode: _ } => (),
            StmX::Assume(exp) => {
                expr_visitor_control_flow!(exp_visitor_dfs(exp, &mut ScopeMap::new(), f))
            }
            StmX::Assign { lhs: Dest { dest, .. }, rhs } => {
                expr_visitor_control_flow!(exp_visitor_dfs(dest, &mut ScopeMap::new(), f));
                expr_visitor_control_flow!(exp_visitor_dfs(rhs, &mut ScopeMap::new(), f))
            }
            StmX::Fuel(..) | StmX::DeadEnd(..) => (),
            StmX::If(exp, _s1, _s2) => {
                expr_visitor_control_flow!(exp_visitor_dfs(exp, &mut ScopeMap::new(), f))
            }
            StmX::While {
                cond_stms: _,
                cond_exp,
                body: _,
                invs,
                typ_inv_vars: _,
                modified_vars: _,
            } => {
                expr_visitor_control_flow!(exp_visitor_dfs(cond_exp, &mut ScopeMap::new(), f));
                for inv in invs.iter() {
                    expr_visitor_control_flow!(exp_visitor_dfs(inv, &mut ScopeMap::new(), f));
                }
            }
            StmX::OpenInvariant(inv, _ident, _ty, _body, _atomicity) => {
                expr_visitor_control_flow!(exp_visitor_dfs(inv, &mut ScopeMap::new(), f))
            }
            StmX::Block(_) => (),
        }
        VisitorControlFlow::Recurse
    })
}

pub(crate) fn map_exp_visitor_bind<F>(
    exp: &Exp,
    map: &mut VisitorScopeMap,
    f: &mut F,
) -> Result<Exp, VirErr>
where
    F: FnMut(&Exp, &mut VisitorScopeMap) -> Result<Exp, VirErr>,
{
    let exp_new = |e: ExpX| SpannedTyped::new(&exp.span, &exp.typ, e);
    match &exp.x {
        ExpX::Const(_) => f(exp, map),
        ExpX::Var(..) => f(exp, map),
        ExpX::VarAt(..) => f(exp, map),
        ExpX::VarLoc(..) => f(exp, map),
        ExpX::Loc(e1) => {
            let expr1 = map_exp_visitor_bind(e1, map, f)?;
            let exp = exp_new(ExpX::Loc(expr1));
            f(&exp, map)
        }
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
            let mapped_binders: Result<Vec<_>, _> =
                binders.iter().map(|b| b.map_result(|a| map_exp_visitor_bind(a, map, f))).collect();
            let exp = exp_new(ExpX::Ctor(path.clone(), ident.clone(), Arc::new(mapped_binders?)));
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
        ExpX::WithTriggers(triggers, body) => {
            let mut trigs: Vec<Trig> = Vec::new();
            for trigger in triggers.iter() {
                let ts = vec_map_result(&**trigger, |e| map_exp_visitor_bind(e, map, f))?;
                trigs.push(Arc::new(ts));
            }
            let body = map_exp_visitor_bind(body, map, f)?;
            let exp = exp_new(ExpX::WithTriggers(Arc::new(trigs), body));
            f(&exp, map)
        }
        ExpX::Bind(bnd, e1) => {
            let bndx = match &bnd.x {
                BndX::Let(bs) => {
                    let mut binders: Vec<Binder<Exp>> = Vec::new();
                    for b in bs.iter() {
                        let a = map_exp_visitor_bind(&b.a, map, f)?;
                        binders.push(Arc::new(BinderX { name: b.name.clone(), a }));
                    }
                    map.push_scope(true);
                    for b in binders.iter() {
                        let _ = map.insert(b.name.clone(), false);
                    }
                    BndX::Let(Arc::new(binders))
                }
                BndX::Quant(quant, binders, ts) => {
                    map.push_scope(true);
                    for b in binders.iter() {
                        let _ = map.insert(b.name.clone(), true);
                    }
                    let mut triggers: Vec<Trig> = Vec::new();
                    for t in ts.iter() {
                        let mut exprs: Vec<Exp> = Vec::new();
                        for exp in t.iter() {
                            exprs.push(map_exp_visitor_bind(exp, map, f)?);
                        }
                        triggers.push(Arc::new(exprs));
                    }
                    BndX::Quant(*quant, binders.clone(), Arc::new(triggers))
                }
                BndX::Lambda(binders) => {
                    map.push_scope(true);
                    for b in binders.iter() {
                        let _ = map.insert(b.name.clone(), false);
                    }
                    bnd.x.clone()
                }
                BndX::Choose(binders, ts, cond) => {
                    map.push_scope(true);
                    for b in binders.iter() {
                        let _ = map.insert(b.name.clone(), true);
                    }
                    let mut triggers: Vec<Trig> = Vec::new();
                    for t in ts.iter() {
                        let mut exprs: Vec<Exp> = Vec::new();
                        for exp in t.iter() {
                            exprs.push(map_exp_visitor_bind(exp, map, f)?);
                        }
                        triggers.push(Arc::new(exprs));
                    }
                    let cond = map_exp_visitor_bind(cond, map, f)?;
                    BndX::Choose(binders.clone(), Arc::new(triggers), cond)
                }
            };
            let bnd = Spanned::new(bnd.span.clone(), bndx);
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
    let mut map: VisitorScopeMap = ScopeMap::new();
    map_exp_visitor_bind(exp, &mut map, &mut |e, _| f(e))
}

pub(crate) fn map_exp_visitor<F>(exp: &Exp, f: &mut F) -> Exp
where
    F: FnMut(&Exp) -> Exp,
{
    let mut map: VisitorScopeMap = ScopeMap::new();
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

// non-recursive visitor
pub(crate) fn map_shallow_exp<E, FT, FE>(
    exp: &Exp,
    env: &mut E,
    ft: &FT,
    fe: &FE,
) -> Result<Exp, VirErr>
where
    FT: Fn(&mut E, &Typ) -> Result<Typ, VirErr>,
    FE: Fn(&mut E, &Exp) -> Result<Exp, VirErr>,
{
    let typ = ft(env, &exp.typ)?;
    let ok_exp = |x: ExpX| Ok(SpannedTyped::new(&exp.span, &typ, x));
    let fs = |env: &mut E, exps: &Exps| -> Result<Exps, VirErr> {
        let exps: Result<Vec<Exp>, VirErr> = exps.iter().map(|e| fe(env, e)).collect();
        Ok(Arc::new(exps?))
    };
    let ftrigs = |env: &mut E, triggers: &Trigs| -> Result<Trigs, VirErr> {
        let mut trigs: Vec<Trig> = Vec::new();
        for trigger in triggers.iter() {
            trigs.push(fs(env, trigger)?);
        }
        Ok(Arc::new(trigs))
    };
    let fbndtyps = |env: &mut E, bs: &Binders<Typ>| -> Result<Binders<Typ>, VirErr> {
        let mut binders: Vec<Binder<Typ>> = Vec::new();
        for binder in bs.iter() {
            binders.push(binder.new_a(ft(env, &binder.a)?));
        }
        Ok(Arc::new(binders))
    };

    match &exp.x {
        ExpX::Const(..) => Ok(exp.clone()),
        ExpX::Var(..) => Ok(exp.clone()),
        ExpX::VarLoc(..) => Ok(exp.clone()),
        ExpX::VarAt(..) => Ok(exp.clone()),
        ExpX::Loc(e1) => ok_exp(ExpX::Loc(fe(env, e1)?)),
        ExpX::Old(..) => Ok(exp.clone()),
        ExpX::Call(fun, typs, es) => {
            let typs: Result<Vec<Typ>, VirErr> = typs.iter().map(|t| ft(env, t)).collect();
            ok_exp(ExpX::Call(fun.clone(), Arc::new(typs?), fs(env, es)?))
        }
        ExpX::CallLambda(typ, e1, es) => {
            ok_exp(ExpX::CallLambda(ft(env, typ)?, fe(env, e1)?, fs(env, es)?))
        }
        ExpX::Ctor(path, ident, bs) => {
            let mut binders: Vec<Binder<Exp>> = Vec::new();
            for b in bs.iter() {
                binders.push(b.new_a(fe(env, &b.a)?));
            }
            ok_exp(ExpX::Ctor(path.clone(), ident.clone(), Arc::new(binders)))
        }
        ExpX::Unary(op, e1) => ok_exp(ExpX::Unary(*op, fe(env, e1)?)),
        ExpX::UnaryOpr(op, e1) => {
            let op = match op {
                UnaryOpr::Box(t) => UnaryOpr::Box(ft(env, t)?),
                UnaryOpr::Unbox(t) => UnaryOpr::Unbox(ft(env, t)?),
                UnaryOpr::HasType(t) => UnaryOpr::HasType(ft(env, t)?),
                UnaryOpr::IsVariant { .. } => op.clone(),
                UnaryOpr::TupleField { .. } => op.clone(),
                UnaryOpr::Field { .. } => op.clone(),
            };
            ok_exp(ExpX::UnaryOpr(op.clone(), fe(env, e1)?))
        }
        ExpX::Binary(op, e1, e2) => ok_exp(ExpX::Binary(*op, fe(env, e1)?, fe(env, e2)?)),
        ExpX::If(e0, e1, e2) => ok_exp(ExpX::If(fe(env, e0)?, fe(env, e1)?, fe(env, e2)?)),
        ExpX::WithTriggers(ts, body) => {
            ok_exp(ExpX::WithTriggers(ftrigs(env, ts)?, fe(env, body)?))
        }
        ExpX::Bind(bnd, e1) => {
            let bnd = match &bnd.x {
                BndX::Let(bs) => {
                    let mut binders: Vec<Binder<Exp>> = Vec::new();
                    for b in bs.iter() {
                        binders.push(b.new_a(fe(env, &b.a)?));
                    }
                    let bndx = BndX::Let(Arc::new(binders));
                    Spanned::new(bnd.span.clone(), bndx)
                }
                BndX::Quant(quant, binders, ts) => {
                    let bndx = BndX::Quant(*quant, fbndtyps(env, binders)?, ftrigs(env, ts)?);
                    Spanned::new(bnd.span.clone(), bndx)
                }
                BndX::Lambda(binders) => {
                    let bndx = BndX::Lambda(fbndtyps(env, binders)?);
                    Spanned::new(bnd.span.clone(), bndx)
                }
                BndX::Choose(binders, ts, cond) => {
                    let bndx =
                        BndX::Choose(fbndtyps(env, binders)?, ftrigs(env, ts)?, fe(env, cond)?);
                    Spanned::new(bnd.span.clone(), bndx)
                }
            };
            ok_exp(ExpX::Bind(bnd, fe(env, e1)?))
        }
    }
}

pub(crate) fn map_stm_visitor<F>(stm: &Stm, fe: &mut F) -> Result<Stm, VirErr>
where
    F: FnMut(&Stm) -> Result<Stm, VirErr>,
{
    match &stm.x {
        StmX::Call(..) => fe(stm),
        StmX::Assert(_, _) => fe(stm),
        StmX::Assume(_) => fe(stm),
        StmX::Assign { .. } => fe(stm),
        StmX::AssertBV { .. } => fe(stm),
        StmX::AssertBitVector { .. } => fe(stm),
        StmX::Fuel(..) => fe(stm),
        StmX::DeadEnd(s) => {
            let s = map_stm_visitor(s, fe)?;
            let stm = Spanned::new(stm.span.clone(), StmX::DeadEnd(s));
            fe(&stm)
        }
        StmX::If(cond, lhs, rhs) => {
            let lhs = map_stm_visitor(lhs, fe)?;
            let rhs = rhs.as_ref().map(|rhs| map_stm_visitor(rhs, fe)).transpose()?;
            let stm = Spanned::new(stm.span.clone(), StmX::If(cond.clone(), lhs, rhs));
            fe(&stm)
        }
        StmX::While { cond_stms, cond_exp, body, invs, typ_inv_vars, modified_vars } => {
            let mut cs: Vec<Stm> = Vec::new();
            for s in cond_stms.iter() {
                cs.push(map_stm_visitor(s, fe)?);
            }
            let body = map_stm_visitor(body, fe)?;
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
            fe(&stm)
        }
        StmX::AssertQuery { mode, typ_inv_vars, body } => {
            let body = map_stm_visitor(body, fe)?;
            let stm = Spanned::new(
                stm.span.clone(),
                StmX::AssertQuery { mode: *mode, typ_inv_vars: typ_inv_vars.clone(), body },
            );
            fe(&stm)
        }
        StmX::OpenInvariant(inv, ident, ty, body, atomicity) => {
            let body = map_stm_visitor(body, fe)?;
            let stm = Spanned::new(
                stm.span.clone(),
                StmX::OpenInvariant(inv.clone(), ident.clone(), ty.clone(), body, *atomicity),
            );
            fe(&stm)
        }
        StmX::Block(ss) => {
            let mut stms: Vec<Stm> = Vec::new();
            for s in ss.iter() {
                stms.push(map_stm_visitor(s, fe)?);
            }
            let stm = Spanned::new(stm.span.clone(), StmX::Block(Arc::new(stms)));
            fe(&stm)
        }
    }
}

pub(crate) fn map_stm_exp_visitor<F>(stm: &Stm, fe: &F) -> Result<Stm, VirErr>
where
    F: Fn(&Exp) -> Result<Exp, VirErr>,
{
    map_stm_visitor(stm, &mut |stm| {
        let span = stm.span.clone();
        let stm = match &stm.x {
            StmX::Call(path, mode, typs, exps, dest) => {
                let exps = Arc::new(vec_map_result(exps, fe)?);
                Spanned::new(
                    span,
                    StmX::Call(path.clone(), *mode, typs.clone(), exps, (*dest).clone()),
                )
            }
            StmX::Assert(span2, exp) => Spanned::new(span, StmX::Assert(span2.clone(), fe(exp)?)),
            StmX::AssertBV(exp) => Spanned::new(span, StmX::AssertBV(fe(exp)?)),
            StmX::AssertBitVector { requires, ensures } => {
                let requires = Arc::new(vec_map_result(requires, fe)?);
                let ensures = Arc::new(vec_map_result(ensures, fe)?);
                Spanned::new(span, StmX::AssertBitVector { requires, ensures })
            }
            StmX::Assume(exp) => Spanned::new(span, StmX::Assume(fe(exp)?)),
            StmX::Assign { lhs: Dest { dest, is_init }, rhs } => {
                let dest = fe(dest)?;
                let rhs = fe(rhs)?;
                Spanned::new(span, StmX::Assign { lhs: Dest { dest, is_init: *is_init }, rhs })
            }
            StmX::AssertQuery { .. } => stm.clone(),
            StmX::Fuel(..) => stm.clone(),
            StmX::DeadEnd(..) => stm.clone(),
            StmX::If(exp, s1, s2) => {
                let exp = fe(exp)?;
                Spanned::new(span, StmX::If(exp, s1.clone(), s2.clone()))
            }
            StmX::While { cond_stms, cond_exp, body, invs, typ_inv_vars, modified_vars } => {
                let cond_exp = fe(cond_exp)?;
                let invs = Arc::new(vec_map_result(invs, fe)?);
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
            StmX::OpenInvariant(inv, ident, ty, body, atomicity) => {
                let inv = fe(inv)?;
                Spanned::new(
                    span,
                    StmX::OpenInvariant(inv, ident.clone(), ty.clone(), body.clone(), *atomicity),
                )
            }
            StmX::Block(_) => stm.clone(),
        };
        Ok(stm)
    })
}
