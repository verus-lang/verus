use crate::ast::{
    Arm, ArmX, CallTarget, Datatype, DatatypeX, Expr, ExprX, Field, Function, FunctionKind,
    FunctionX, GenericBound, GenericBoundX, Ident, MaskSpec, Param, ParamX, Pattern, PatternX,
    SpannedTyped, Stmt, StmtX, Typ, TypX, UnaryOpr, Variant, VirErr,
};
use crate::ast_util::err_str;
use crate::def::Spanned;
use crate::util::vec_map_result;
use crate::visitor::expr_visitor_control_flow;
pub(crate) use crate::visitor::VisitorControlFlow;
use air::scope_map::ScopeMap;
use std::sync::Arc;

pub type VisitorScopeMap = ScopeMap<Ident, Typ>;

pub(crate) fn typ_visitor_check<E, MF>(typ: &Typ, mf: &mut MF) -> Result<(), E>
where
    MF: FnMut(&Typ) -> Result<(), E>,
{
    match typ_visitor_dfs(typ, &mut |typ| match mf(typ) {
        Ok(()) => VisitorControlFlow::Recurse,
        Err(e) => VisitorControlFlow::Stop(e),
    }) {
        VisitorControlFlow::Recurse => Ok(()),
        VisitorControlFlow::Return => unreachable!(),
        VisitorControlFlow::Stop(e) => Err(e),
    }
}

pub(crate) fn typ_visitor_dfs<T, FT>(typ: &Typ, ft: &mut FT) -> VisitorControlFlow<T>
where
    FT: FnMut(&Typ) -> VisitorControlFlow<T>,
{
    match ft(typ) {
        VisitorControlFlow::Stop(val) => VisitorControlFlow::Stop(val),
        VisitorControlFlow::Return => VisitorControlFlow::Recurse,
        VisitorControlFlow::Recurse => {
            match &**typ {
                TypX::Bool | TypX::Int(_) | TypX::TypParam(_) | TypX::TypeId | TypX::Air(_) => (),
                TypX::Tuple(ts) => {
                    for t in ts.iter() {
                        expr_visitor_control_flow!(typ_visitor_dfs(t, ft));
                    }
                }
                TypX::Lambda(ts, tr) => {
                    for t in ts.iter() {
                        expr_visitor_control_flow!(typ_visitor_dfs(t, ft));
                    }
                    expr_visitor_control_flow!(typ_visitor_dfs(tr, ft));
                }
                TypX::Datatype(_path, ts) => {
                    for t in ts.iter() {
                        expr_visitor_control_flow!(typ_visitor_dfs(t, ft));
                    }
                }
                TypX::Boxed(t) => {
                    expr_visitor_control_flow!(typ_visitor_dfs(t, ft));
                }
            }
            VisitorControlFlow::Recurse
        }
    }
}

pub(crate) fn map_typ_visitor_env<E, FT>(typ: &Typ, env: &mut E, ft: &FT) -> Result<Typ, VirErr>
where
    FT: Fn(&mut E, &Typ) -> Result<Typ, VirErr>,
{
    match &**typ {
        TypX::Bool | TypX::Int(_) | TypX::TypParam(_) | TypX::TypeId | TypX::Air(_) => ft(env, typ),
        TypX::Tuple(ts) => {
            let ts = vec_map_result(&**ts, |t| map_typ_visitor_env(t, env, ft))?;
            ft(env, &Arc::new(TypX::Tuple(Arc::new(ts))))
        }
        TypX::Lambda(ts, tr) => {
            let ts = vec_map_result(&**ts, |t| map_typ_visitor_env(t, env, ft))?;
            let tr = map_typ_visitor_env(tr, env, ft)?;
            ft(env, &Arc::new(TypX::Lambda(Arc::new(ts), tr)))
        }
        TypX::Datatype(path, ts) => {
            let ts = vec_map_result(&**ts, |t| map_typ_visitor_env(t, env, ft))?;
            ft(env, &Arc::new(TypX::Datatype(path.clone(), Arc::new(ts))))
        }
        TypX::Boxed(t) => {
            let t = map_typ_visitor_env(t, env, ft)?;
            ft(env, &Arc::new(TypX::Boxed(t)))
        }
    }
}

pub(crate) fn map_pattern_visitor_env<E, FT>(
    pattern: &Pattern,
    env: &mut E,
    ft: &FT,
) -> Result<Pattern, VirErr>
where
    FT: Fn(&mut E, &Typ) -> Result<Typ, VirErr>,
{
    let patternx = match &pattern.x {
        PatternX::Wildcard => PatternX::Wildcard,
        PatternX::Var { name, mutable } => PatternX::Var { name: name.clone(), mutable: *mutable },
        PatternX::Tuple(ps) => {
            let ps = vec_map_result(&**ps, |p| map_pattern_visitor_env(p, env, ft))?;
            PatternX::Tuple(Arc::new(ps))
        }
        PatternX::Constructor(path, variant, binders) => {
            let binders = vec_map_result(&**binders, |b| {
                b.map_result(|p| map_pattern_visitor_env(p, env, ft))
            })?;
            PatternX::Constructor(path.clone(), variant.clone(), Arc::new(binders))
        }
    };
    Ok(SpannedTyped::new(&pattern.span, &map_typ_visitor_env(&pattern.typ, env, ft)?, patternx))
}

fn insert_pattern_vars(map: &mut VisitorScopeMap, pattern: &Pattern) {
    match &pattern.x {
        PatternX::Wildcard => {}
        PatternX::Var { name, mutable: _ } => {
            let _ = map.insert(name.clone(), pattern.typ.clone());
        }
        PatternX::Tuple(ps) => {
            for p in ps.iter() {
                insert_pattern_vars(map, p);
            }
        }
        PatternX::Constructor(_, _, binders) => {
            for binder in binders.iter() {
                insert_pattern_vars(map, &binder.a);
            }
        }
    }
}

pub(crate) fn expr_visitor_check<E, MF>(expr: &Expr, mf: &mut MF) -> Result<(), E>
where
    MF: FnMut(&Expr) -> Result<(), E>,
{
    let mut scope_map: VisitorScopeMap = ScopeMap::new();
    match expr_visitor_dfs(expr, &mut scope_map, &mut |_scope_map, expr| match mf(expr) {
        Ok(()) => VisitorControlFlow::Recurse,
        Err(e) => VisitorControlFlow::Stop(e),
    }) {
        VisitorControlFlow::Recurse => Ok(()),
        VisitorControlFlow::Return => unreachable!(),
        VisitorControlFlow::Stop(e) => Err(e),
    }
}

pub(crate) fn expr_visitor_dfs<T, MF>(
    expr: &Expr,
    map: &mut VisitorScopeMap,
    mf: &mut MF,
) -> VisitorControlFlow<T>
where
    MF: FnMut(&mut VisitorScopeMap, &Expr) -> VisitorControlFlow<T>,
{
    match mf(map, expr) {
        VisitorControlFlow::Stop(val) => VisitorControlFlow::Stop(val),
        VisitorControlFlow::Return => VisitorControlFlow::Recurse,
        VisitorControlFlow::Recurse => {
            match &expr.x {
                ExprX::Const(_)
                | ExprX::Var(_)
                | ExprX::VarLoc(_)
                | ExprX::VarAt(_, _)
                | ExprX::ConstVar(..) => (),
                ExprX::Loc(e) => {
                    expr_visitor_control_flow!(expr_visitor_dfs(e, map, mf));
                }
                ExprX::Call(target, es) => {
                    match target {
                        CallTarget::Static(_, _) => (),
                        CallTarget::FnSpec(fun) => {
                            expr_visitor_control_flow!(expr_visitor_dfs(fun, map, mf));
                        }
                    }
                    for e in es.iter() {
                        expr_visitor_control_flow!(expr_visitor_dfs(e, map, mf));
                    }
                }
                ExprX::Tuple(es) => {
                    for e in es.iter() {
                        expr_visitor_control_flow!(expr_visitor_dfs(e, map, mf));
                    }
                }
                ExprX::Ctor(_path, _ident, binders, update) => {
                    match update {
                        None => (),
                        Some(update) => {
                            expr_visitor_control_flow!(expr_visitor_dfs(update, map, mf))
                        }
                    }
                    for binder in binders.iter() {
                        expr_visitor_control_flow!(expr_visitor_dfs(&binder.a, map, mf));
                    }
                }
                ExprX::Unary(_op, e1) => {
                    expr_visitor_control_flow!(expr_visitor_dfs(e1, map, mf));
                }
                ExprX::UnaryOpr(_op, e1) => {
                    expr_visitor_control_flow!(expr_visitor_dfs(e1, map, mf));
                }
                ExprX::Binary(_op, e1, e2) => {
                    expr_visitor_control_flow!(expr_visitor_dfs(e1, map, mf));
                    expr_visitor_control_flow!(expr_visitor_dfs(e2, map, mf));
                }
                ExprX::Multi(_op, es) => {
                    for e in es.iter() {
                        expr_visitor_control_flow!(expr_visitor_dfs(e, map, mf));
                    }
                }
                ExprX::Quant(_quant, binders, e1) => {
                    map.push_scope(true);
                    for binder in binders.iter() {
                        let _ = map.insert(binder.name.clone(), binder.a.clone());
                    }
                    expr_visitor_control_flow!(expr_visitor_dfs(e1, map, mf));
                    map.pop_scope();
                }
                ExprX::Closure(params, body) => {
                    map.push_scope(true);
                    for binder in params.iter() {
                        let _ = map.insert(binder.name.clone(), binder.a.clone());
                    }
                    expr_visitor_control_flow!(expr_visitor_dfs(body, map, mf));
                    map.pop_scope();
                }
                ExprX::Choose { params, cond, body } => {
                    map.push_scope(true);
                    for binder in params.iter() {
                        let _ = map.insert(binder.name.clone(), binder.a.clone());
                    }
                    expr_visitor_control_flow!(expr_visitor_dfs(cond, map, mf));
                    expr_visitor_control_flow!(expr_visitor_dfs(body, map, mf));
                    map.pop_scope();
                }
                ExprX::WithTriggers { triggers, body } => {
                    for trigger in triggers.iter() {
                        for term in trigger.iter() {
                            expr_visitor_control_flow!(expr_visitor_dfs(term, map, mf));
                        }
                    }
                    expr_visitor_control_flow!(expr_visitor_dfs(body, map, mf));
                }
                ExprX::Assign { init_not_mut: _, lhs: e1, rhs: e2 } => {
                    expr_visitor_control_flow!(expr_visitor_dfs(e1, map, mf));
                    expr_visitor_control_flow!(expr_visitor_dfs(e2, map, mf));
                }
                ExprX::AssertBV(e) => {
                    expr_visitor_control_flow!(expr_visitor_dfs(e, map, mf));
                }
                ExprX::Fuel(_, _) => (),
                ExprX::Header(_) => {
                    panic!("header expression not allowed here: {:?}", &expr.span);
                }
                ExprX::Admit => (),
                ExprX::Forall { vars, require, ensure, proof } => {
                    map.push_scope(true);
                    for binder in vars.iter() {
                        let _ = map.insert(binder.name.clone(), binder.a.clone());
                    }
                    expr_visitor_control_flow!(expr_visitor_dfs(require, map, mf));
                    expr_visitor_control_flow!(expr_visitor_dfs(ensure, map, mf));
                    expr_visitor_control_flow!(expr_visitor_dfs(proof, map, mf));
                    map.pop_scope();
                }
                ExprX::AssertQuery { requires, ensures, proof, mode: _ } => {
                    for req in requires.iter() {
                        expr_visitor_control_flow!(expr_visitor_dfs(req, map, mf));
                    }
                    for ens in ensures.iter() {
                        expr_visitor_control_flow!(expr_visitor_dfs(ens, map, mf));
                    }
                    expr_visitor_control_flow!(expr_visitor_dfs(proof, map, mf));
                }
                ExprX::If(e1, e2, e3) => {
                    expr_visitor_control_flow!(expr_visitor_dfs(e1, map, mf));
                    expr_visitor_control_flow!(expr_visitor_dfs(e2, map, mf));
                    if let Some(e3) = &e3 {
                        expr_visitor_control_flow!(expr_visitor_dfs(e3, map, mf));
                    }
                }
                ExprX::Match(e1, arms) => {
                    expr_visitor_control_flow!(expr_visitor_dfs(e1, map, mf));
                    for arm in arms.iter() {
                        map.push_scope(true);
                        insert_pattern_vars(map, &arm.x.pattern);
                        expr_visitor_control_flow!(expr_visitor_dfs(&arm.x.guard, map, mf));
                        expr_visitor_control_flow!(expr_visitor_dfs(&arm.x.body, map, mf));
                        map.pop_scope();
                    }
                }
                ExprX::While { cond, body, invs } => {
                    expr_visitor_control_flow!(expr_visitor_dfs(cond, map, mf));
                    expr_visitor_control_flow!(expr_visitor_dfs(body, map, mf));
                    for inv in invs.iter() {
                        expr_visitor_control_flow!(expr_visitor_dfs(inv, map, mf));
                    }
                }
                ExprX::OpenInvariant(inv, binder, body, _atomicity) => {
                    expr_visitor_control_flow!(expr_visitor_dfs(inv, map, mf));
                    map.push_scope(true);
                    let _ = map.insert(binder.name.clone(), binder.a.clone());
                    expr_visitor_control_flow!(expr_visitor_dfs(body, map, mf));
                    map.pop_scope();
                }
                ExprX::Return(e1) => match e1 {
                    None => (),
                    Some(e) => expr_visitor_control_flow!(expr_visitor_dfs(e, map, mf)),
                },
                ExprX::Ghost { alloc_wrapper: _, tracked: _, expr: e1 } => {
                    expr_visitor_control_flow!(expr_visitor_dfs(e1, map, mf))
                }
                ExprX::Block(ss, e1) => {
                    for stmt in ss.iter() {
                        expr_visitor_control_flow!(stmt_visitor_dfs(stmt, map, mf));
                    }
                    match e1 {
                        None => (),
                        Some(e) => expr_visitor_control_flow!(expr_visitor_dfs(e, map, mf)),
                    };
                    for stmt in ss.iter() {
                        match &stmt.x {
                            StmtX::Expr(_) => {}
                            StmtX::Decl { .. } => map.pop_scope(),
                        }
                    }
                }
            }
            VisitorControlFlow::Recurse
        }
    }
}

pub(crate) fn stmt_visitor_dfs<T, MF>(
    stmt: &Stmt,
    map: &mut VisitorScopeMap,
    mf: &mut MF,
) -> VisitorControlFlow<T>
where
    MF: FnMut(&mut VisitorScopeMap, &Expr) -> VisitorControlFlow<T>,
{
    match &stmt.x {
        StmtX::Expr(e) => {
            expr_visitor_control_flow!(expr_visitor_dfs(e, map, mf));
        }
        StmtX::Decl { pattern, mode: _, init } => {
            map.push_scope(true);
            if let Some(init) = init {
                expr_visitor_control_flow!(expr_visitor_dfs(init, map, mf));
            }
            insert_pattern_vars(map, &pattern);
        }
    }
    VisitorControlFlow::Recurse
}

pub(crate) fn function_visitor_dfs<T, MF>(
    function: &Function,
    map: &mut VisitorScopeMap,
    mf: &mut MF,
) -> VisitorControlFlow<T>
where
    MF: FnMut(&mut VisitorScopeMap, &Expr) -> VisitorControlFlow<T>,
{
    let FunctionX {
        name: _,
        kind: _,
        visibility: _,
        mode: _,
        fuel: _,
        typ_bounds: _,
        params,
        ret: _,
        require,
        ensure,
        decrease,
        decrease_when,
        decrease_by: _,
        broadcast_forall,
        mask_spec,
        is_const: _,
        is_string_literal: _,
        publish: _,
        attrs: _,
        body,
        extra_dependencies: _,
    } = &function.x;
    map.push_scope(true);
    for p in params.iter() {
        let _ = map.insert(p.x.name.clone(), p.x.typ.clone());
    }
    for e in require.iter() {
        expr_visitor_control_flow!(expr_visitor_dfs(e, map, mf));
    }
    for e in ensure.iter() {
        expr_visitor_control_flow!(expr_visitor_dfs(e, map, mf));
    }
    for e in decrease.iter() {
        expr_visitor_control_flow!(expr_visitor_dfs(e, map, mf));
    }
    if let Some(e) = decrease_when {
        expr_visitor_control_flow!(expr_visitor_dfs(e, map, mf));
    }
    match mask_spec {
        MaskSpec::NoSpec => {}
        MaskSpec::InvariantOpens(es) | MaskSpec::InvariantOpensExcept(es) => {
            for e in es.iter() {
                expr_visitor_control_flow!(expr_visitor_dfs(e, map, mf));
            }
        }
    }
    if let Some(e) = body {
        expr_visitor_control_flow!(expr_visitor_dfs(e, map, mf));
    }
    map.pop_scope();

    if let Some((params, req_ens)) = broadcast_forall {
        map.push_scope(true);
        for p in params.iter() {
            let _ = map.insert(p.x.name.clone(), p.x.typ.clone());
        }
        expr_visitor_control_flow!(expr_visitor_dfs(req_ens, map, mf));
        map.pop_scope();
    }

    VisitorControlFlow::Recurse
}

pub(crate) fn function_visitor_check<E, MF>(function: &Function, mf: &mut MF) -> Result<(), E>
where
    MF: FnMut(&Expr) -> Result<(), E>,
{
    let mut scope_map: VisitorScopeMap = ScopeMap::new();
    match function_visitor_dfs(function, &mut scope_map, &mut |_scope_map, expr| match mf(expr) {
        Ok(()) => VisitorControlFlow::Recurse,
        Err(e) => VisitorControlFlow::Stop(e),
    }) {
        VisitorControlFlow::Recurse => Ok(()),
        VisitorControlFlow::Return => unreachable!(),
        VisitorControlFlow::Stop(e) => Err(e),
    }
}

pub(crate) fn map_expr_visitor_env<E, FE, FS, FT>(
    expr: &Expr,
    map: &mut VisitorScopeMap,
    env: &mut E,
    fe: &FE,
    fs: &FS,
    ft: &FT,
) -> Result<Expr, VirErr>
where
    FE: Fn(&mut E, &mut VisitorScopeMap, &Expr) -> Result<Expr, VirErr>,
    FS: Fn(&mut E, &mut VisitorScopeMap, &Stmt) -> Result<Vec<Stmt>, VirErr>,
    FT: Fn(&mut E, &Typ) -> Result<Typ, VirErr>,
{
    let exprx = match &expr.x {
        ExprX::Const(c) => ExprX::Const(c.clone()),
        ExprX::Var(x) => ExprX::Var(x.clone()),
        ExprX::VarLoc(x) => ExprX::VarLoc(x.clone()),
        ExprX::VarAt(x, at) => ExprX::VarAt(x.clone(), at.clone()),
        ExprX::ConstVar(x) => ExprX::ConstVar(x.clone()),
        ExprX::Loc(e) => ExprX::Loc(map_expr_visitor_env(e, map, env, fe, fs, ft)?),
        ExprX::Call(target, es) => {
            let target = match target {
                CallTarget::Static(x, typs) => {
                    let typs = vec_map_result(&**typs, |t| (map_typ_visitor_env(t, env, ft)))?;
                    CallTarget::Static(x.clone(), Arc::new(typs))
                }
                CallTarget::FnSpec(fun) => {
                    let fun = map_expr_visitor_env(fun, map, env, fe, fs, ft)?;
                    CallTarget::FnSpec(fun)
                }
            };
            let mut exprs: Vec<Expr> = Vec::new();
            for e in es.iter() {
                exprs.push(map_expr_visitor_env(e, map, env, fe, fs, ft)?);
            }
            ExprX::Call(target, Arc::new(exprs))
        }
        ExprX::Tuple(es) => {
            let mut exprs: Vec<Expr> = Vec::new();
            for e in es.iter() {
                exprs.push(map_expr_visitor_env(e, map, env, fe, fs, ft)?);
            }
            ExprX::Tuple(Arc::new(exprs))
        }
        ExprX::Ctor(path, ident, binders, update) => {
            let update = match update {
                None => None,
                Some(update) => Some(map_expr_visitor_env(update, map, env, fe, fs, ft)?),
            };
            let mapped_binders = binders
                .iter()
                .map(|b| b.map_result(|a| map_expr_visitor_env(a, map, env, fe, fs, ft)))
                .collect::<Result<Vec<_>, _>>()?;
            ExprX::Ctor(path.clone(), ident.clone(), Arc::new(mapped_binders), update)
        }
        ExprX::Unary(op, e1) => {
            let expr1 = map_expr_visitor_env(e1, map, env, fe, fs, ft)?;
            ExprX::Unary(*op, expr1)
        }
        ExprX::UnaryOpr(op, e1) => {
            let op = match op {
                UnaryOpr::Box(t) => UnaryOpr::Box(map_typ_visitor_env(t, env, ft)?),
                UnaryOpr::Unbox(t) => UnaryOpr::Unbox(map_typ_visitor_env(t, env, ft)?),
                UnaryOpr::HasType(t) => UnaryOpr::HasType(map_typ_visitor_env(t, env, ft)?),
                UnaryOpr::IsVariant { .. } => op.clone(),
                UnaryOpr::TupleField { .. } => op.clone(),
                UnaryOpr::Field { .. } => op.clone(),
            };
            let expr1 = map_expr_visitor_env(e1, map, env, fe, fs, ft)?;
            ExprX::UnaryOpr(op.clone(), expr1)
        }
        ExprX::Binary(op, e1, e2) => {
            let expr1 = map_expr_visitor_env(e1, map, env, fe, fs, ft)?;
            let expr2 = map_expr_visitor_env(e2, map, env, fe, fs, ft)?;
            ExprX::Binary(*op, expr1, expr2)
        }
        ExprX::Multi(op, es) => {
            let mut exprs: Vec<Expr> = Vec::new();
            for e in es.iter() {
                exprs.push(map_expr_visitor_env(e, map, env, fe, fs, ft)?);
            }
            ExprX::Multi(op.clone(), Arc::new(exprs))
        }
        ExprX::Quant(quant, binders, e1) => {
            let binders =
                vec_map_result(&**binders, |b| b.map_result(|t| map_typ_visitor_env(t, env, ft)))?;
            map.push_scope(true);
            for binder in binders.iter() {
                let _ = map.insert(binder.name.clone(), binder.a.clone());
            }
            let expr1 = map_expr_visitor_env(e1, map, env, fe, fs, ft)?;
            map.pop_scope();
            ExprX::Quant(*quant, Arc::new(binders), expr1)
        }
        ExprX::Closure(params, body) => {
            let params =
                vec_map_result(&**params, |b| b.map_result(|t| map_typ_visitor_env(t, env, ft)))?;
            map.push_scope(true);
            for binder in params.iter() {
                let _ = map.insert(binder.name.clone(), binder.a.clone());
            }
            let body = map_expr_visitor_env(body, map, env, fe, fs, ft)?;
            map.pop_scope();
            ExprX::Closure(Arc::new(params), body)
        }
        ExprX::Choose { params, cond, body } => {
            let params =
                vec_map_result(&**params, |b| b.map_result(|t| map_typ_visitor_env(t, env, ft)))?;
            map.push_scope(true);
            for binder in params.iter() {
                let _ = map.insert(binder.name.clone(), binder.a.clone());
            }
            let cond = map_expr_visitor_env(cond, map, env, fe, fs, ft)?;
            let body = map_expr_visitor_env(body, map, env, fe, fs, ft)?;
            map.pop_scope();
            ExprX::Choose { params: Arc::new(params), cond, body }
        }
        ExprX::WithTriggers { triggers, body } => {
            let mut trigs: Vec<crate::ast::Exprs> = Vec::new();
            for trigger in triggers.iter() {
                let terms =
                    vec_map_result(&**trigger, |e| map_expr_visitor_env(e, map, env, fe, fs, ft))?;
                trigs.push(Arc::new(terms));
            }
            let triggers = Arc::new(trigs);
            let body = map_expr_visitor_env(body, map, env, fe, fs, ft)?;
            ExprX::WithTriggers { triggers, body }
        }
        ExprX::Assign { init_not_mut, lhs: e1, rhs: e2 } => {
            let expr1 = map_expr_visitor_env(e1, map, env, fe, fs, ft)?;
            let expr2 = map_expr_visitor_env(e2, map, env, fe, fs, ft)?;
            ExprX::Assign { init_not_mut: *init_not_mut, lhs: expr1, rhs: expr2 }
        }
        ExprX::Fuel(path, fuel) => ExprX::Fuel(path.clone(), *fuel),
        ExprX::Header(_) => {
            return err_str(&expr.span, "header expression not allowed here");
        }
        ExprX::Admit => ExprX::Admit,
        ExprX::Forall { vars, require, ensure, proof } => {
            let vars =
                vec_map_result(&**vars, |x| x.map_result(|t| map_typ_visitor_env(t, env, ft)))?;
            map.push_scope(true);
            for binder in vars.iter() {
                let _ = map.insert(binder.name.clone(), binder.a.clone());
            }
            let require = map_expr_visitor_env(require, map, env, fe, fs, ft)?;
            let ensure = map_expr_visitor_env(ensure, map, env, fe, fs, ft)?;
            let proof = map_expr_visitor_env(proof, map, env, fe, fs, ft)?;
            map.pop_scope();
            ExprX::Forall { vars: Arc::new(vars), require, ensure, proof }
        }
        ExprX::AssertQuery { requires, ensures, proof, mode } => {
            let requires = Arc::new(vec_map_result(requires, |e| {
                map_expr_visitor_env(e, map, env, fe, fs, ft)
            })?);
            let ensures = Arc::new(vec_map_result(ensures, |e| {
                map_expr_visitor_env(e, map, env, fe, fs, ft)
            })?);
            let proof = map_expr_visitor_env(proof, map, env, fe, fs, ft)?;
            ExprX::AssertQuery { requires, ensures, proof, mode: *mode }
        }
        ExprX::AssertBV(e) => {
            let expr1 = map_expr_visitor_env(e, map, env, fe, fs, ft)?;
            ExprX::AssertBV(expr1)
        }
        ExprX::If(e1, e2, e3) => {
            let expr1 = map_expr_visitor_env(e1, map, env, fe, fs, ft)?;
            let expr2 = map_expr_visitor_env(e2, map, env, fe, fs, ft)?;
            let expr3 =
                e3.as_ref().map(|e| map_expr_visitor_env(e, map, env, fe, fs, ft)).transpose()?;
            ExprX::If(expr1, expr2, expr3)
        }
        ExprX::Match(e1, arms) => {
            let expr1 = map_expr_visitor_env(e1, map, env, fe, fs, ft)?;
            let arms: Result<Vec<Arm>, VirErr> = vec_map_result(arms, |arm| {
                map.push_scope(true);
                let pattern = map_pattern_visitor_env(&arm.x.pattern, env, ft)?;
                insert_pattern_vars(map, &pattern);
                let guard = map_expr_visitor_env(&arm.x.guard, map, env, fe, fs, ft)?;
                let body = map_expr_visitor_env(&arm.x.body, map, env, fe, fs, ft)?;
                map.pop_scope();
                Ok(Spanned::new(arm.span.clone(), ArmX { pattern, guard, body }))
            });
            ExprX::Match(expr1, Arc::new(arms?))
        }
        ExprX::While { cond, body, invs } => {
            let cond = map_expr_visitor_env(cond, map, env, fe, fs, ft)?;
            let body = map_expr_visitor_env(body, map, env, fe, fs, ft)?;
            let invs =
                Arc::new(vec_map_result(invs, |e| map_expr_visitor_env(e, map, env, fe, fs, ft))?);
            ExprX::While { cond, body, invs }
        }
        ExprX::Return(e1) => {
            let e1 = match e1 {
                None => None,
                Some(e) => Some(map_expr_visitor_env(e, map, env, fe, fs, ft)?),
            };
            ExprX::Return(e1)
        }
        ExprX::Ghost { alloc_wrapper, tracked, expr: e1 } => {
            let expr = map_expr_visitor_env(e1, map, env, fe, fs, ft)?;
            ExprX::Ghost { alloc_wrapper: alloc_wrapper.clone(), tracked: *tracked, expr }
        }
        ExprX::Block(ss, e1) => {
            let mut stmts: Vec<Stmt> = Vec::new();
            for s in ss.iter() {
                match &s.x {
                    StmtX::Expr(_) => {}
                    StmtX::Decl { .. } => map.push_scope(true),
                }
                stmts.append(&mut map_stmt_visitor_env(s, map, env, fe, fs, ft)?);
            }
            let expr1 = match e1 {
                None => None,
                Some(e) => Some(map_expr_visitor_env(e, map, env, fe, fs, ft)?),
            };
            for s in ss.iter() {
                match &s.x {
                    StmtX::Expr(_) => {}
                    StmtX::Decl { .. } => map.pop_scope(),
                }
            }
            ExprX::Block(Arc::new(stmts), expr1)
        }
        ExprX::OpenInvariant(e1, binder, e2, atomicity) => {
            let expr1 = map_expr_visitor_env(e1, map, env, fe, fs, ft)?;
            let binder = binder.map_result(|t| map_typ_visitor_env(t, env, ft))?;
            map.push_scope(true);
            let _ = map.insert(binder.name.clone(), binder.a.clone());
            let expr2 = map_expr_visitor_env(e2, map, env, fe, fs, ft)?;
            map.pop_scope();
            ExprX::OpenInvariant(expr1, binder, expr2, *atomicity)
        }
    };
    let expr = SpannedTyped::new(&expr.span, &map_typ_visitor_env(&expr.typ, env, ft)?, exprx);
    fe(env, map, &expr)
}

pub(crate) fn map_stmt_visitor_env<E, FE, FS, FT>(
    stmt: &Stmt,
    map: &mut ScopeMap<Ident, Typ>,
    env: &mut E,
    fe: &FE,
    fs: &FS,
    ft: &FT,
) -> Result<Vec<Stmt>, VirErr>
where
    FE: Fn(&mut E, &mut ScopeMap<Ident, Typ>, &Expr) -> Result<Expr, VirErr>,
    FS: Fn(&mut E, &mut ScopeMap<Ident, Typ>, &Stmt) -> Result<Vec<Stmt>, VirErr>,
    FT: Fn(&mut E, &Typ) -> Result<Typ, VirErr>,
{
    match &stmt.x {
        StmtX::Expr(e) => {
            let expr = map_expr_visitor_env(e, map, env, fe, fs, ft)?;
            fs(env, map, &Spanned::new(stmt.span.clone(), StmtX::Expr(expr)))
        }
        StmtX::Decl { pattern, mode, init } => {
            let pattern = map_pattern_visitor_env(pattern, env, ft)?;
            let init =
                init.as_ref().map(|e| map_expr_visitor_env(e, map, env, fe, fs, ft)).transpose()?;
            insert_pattern_vars(map, &pattern);
            let decl = StmtX::Decl { pattern, mode: *mode, init };
            fs(env, map, &Spanned::new(stmt.span.clone(), decl))
        }
    }
}

pub(crate) fn map_param_visitor<E, FT>(param: &Param, env: &mut E, ft: &FT) -> Result<Param, VirErr>
where
    FT: Fn(&mut E, &Typ) -> Result<Typ, VirErr>,
{
    let typ = map_typ_visitor_env(&param.x.typ, env, ft)?;
    let paramx =
        ParamX { name: param.x.name.clone(), typ, mode: param.x.mode, is_mut: param.x.is_mut };
    Ok(Spanned::new(param.span.clone(), paramx))
}

pub(crate) fn map_generic_bound_visitor<E, FT>(
    bound: &GenericBound,
    env: &mut E,
    ft: &FT,
) -> Result<GenericBound, VirErr>
where
    FT: Fn(&mut E, &Typ) -> Result<Typ, VirErr>,
{
    match &**bound {
        GenericBoundX::Traits(_) => Ok(bound.clone()),
        GenericBoundX::FnSpec(typs, typ) => {
            let typs = Arc::new(vec_map_result(&**typs, |t| (map_typ_visitor_env(t, env, ft)))?);
            let typ = map_typ_visitor_env(typ, env, ft)?;
            Ok(Arc::new(GenericBoundX::FnSpec(typs, typ)))
        }
    }
}

pub(crate) fn map_function_visitor_env<E, FE, FS, FT>(
    function: &Function,
    map: &mut ScopeMap<Ident, Typ>,
    env: &mut E,
    fe: &FE,
    fs: &FS,
    ft: &FT,
) -> Result<Function, VirErr>
where
    FE: Fn(&mut E, &mut ScopeMap<Ident, Typ>, &Expr) -> Result<Expr, VirErr>,
    FS: Fn(&mut E, &mut ScopeMap<Ident, Typ>, &Stmt) -> Result<Vec<Stmt>, VirErr>,
    FT: Fn(&mut E, &Typ) -> Result<Typ, VirErr>,
{
    let FunctionX {
        name,
        kind,
        visibility,
        mode,
        fuel,
        typ_bounds,
        params,
        ret,
        require,
        ensure,
        decrease,
        decrease_when,
        decrease_by,
        broadcast_forall,
        mask_spec,
        is_const,
        is_string_literal,
        publish,
        attrs,
        body,
        extra_dependencies,
    } = &function.x;
    let name = name.clone();
    let kind = match kind {
        FunctionKind::Static | FunctionKind::TraitMethodDecl { trait_path: _ } => kind.clone(),
        FunctionKind::TraitMethodImpl {
            method,
            trait_path,
            trait_typ_args,
            datatype,
            datatype_typ_args,
        } => {
            let trait_typ_args =
                Arc::new(vec_map_result(&**trait_typ_args, |t| map_typ_visitor_env(t, env, ft))?);
            let datatype_typ_args = Arc::new(vec_map_result(&**datatype_typ_args, |t| {
                map_typ_visitor_env(t, env, ft)
            })?);
            FunctionKind::TraitMethodImpl {
                method: method.clone(),
                trait_path: trait_path.clone(),
                trait_typ_args,
                datatype: datatype.clone(),
                datatype_typ_args,
            }
        }
    };
    let visibility = visibility.clone();
    let mode = *mode;
    let fuel = *fuel;
    let mut type_bounds: Vec<(Ident, GenericBound)> = Vec::new();
    for (x, bound) in typ_bounds.iter() {
        type_bounds.push((x.clone(), map_generic_bound_visitor(bound, env, ft)?));
    }
    map.push_scope(true);
    let params = Arc::new(vec_map_result(params, |p| map_param_visitor(p, env, ft))?);
    for p in params.iter() {
        let _ = map.insert(p.x.name.clone(), p.x.typ.clone());
    }
    let ret = map_param_visitor(ret, env, ft)?;
    let require =
        Arc::new(vec_map_result(require, |e| map_expr_visitor_env(e, map, env, fe, fs, ft))?);

    map.push_scope(true);
    if function.x.has_return() {
        let _ = map.insert(ret.x.name.clone(), ret.x.typ.clone());
    }
    let ensure =
        Arc::new(vec_map_result(ensure, |e| map_expr_visitor_env(e, map, env, fe, fs, ft))?);
    map.pop_scope();

    let decrease =
        Arc::new(vec_map_result(decrease, |e| map_expr_visitor_env(e, map, env, fe, fs, ft))?);
    let decrease_when = decrease_when
        .as_ref()
        .map(|e| map_expr_visitor_env(e, map, env, fe, fs, ft))
        .transpose()?;
    let decrease_by = decrease_by.clone();

    let mask_spec = match mask_spec {
        MaskSpec::NoSpec => MaskSpec::NoSpec,
        MaskSpec::InvariantOpens(es) => {
            MaskSpec::InvariantOpens(Arc::new(vec_map_result(es, |e| {
                map_expr_visitor_env(e, map, env, fe, fs, ft)
            })?))
        }
        MaskSpec::InvariantOpensExcept(es) => {
            MaskSpec::InvariantOpensExcept(Arc::new(vec_map_result(es, |e| {
                map_expr_visitor_env(e, map, env, fe, fs, ft)
            })?))
        }
    };
    let attrs = attrs.clone();
    let extra_dependencies = extra_dependencies.clone();
    let is_const = *is_const;
    let is_string_literal = *is_string_literal;
    let publish = *publish;
    let body = body.as_ref().map(|e| map_expr_visitor_env(e, map, env, fe, fs, ft)).transpose()?;
    map.pop_scope();

    let broadcast_forall = if let Some((params, req_ens)) = broadcast_forall {
        map.push_scope(true);
        let params = Arc::new(vec_map_result(params, |p| map_param_visitor(p, env, ft))?);
        for p in params.iter() {
            let _ = map.insert(p.x.name.clone(), p.x.typ.clone());
        }
        let req_ens = map_expr_visitor_env(req_ens, map, env, fe, fs, ft)?;
        map.pop_scope();
        Some((params, req_ens))
    } else {
        None
    };

    let functionx = FunctionX {
        name,
        kind,
        visibility,
        mode,
        fuel,
        typ_bounds: Arc::new(type_bounds),
        params,
        ret,
        require,
        ensure,
        decrease,
        decrease_when,
        decrease_by,
        broadcast_forall,
        mask_spec,
        is_const,
        is_string_literal,
        publish,
        attrs,
        body,
        extra_dependencies,
    };
    Ok(Spanned::new(function.span.clone(), functionx))
}

pub(crate) fn map_datatype_visitor_env<E, FT>(
    datatype: &Datatype,
    env: &mut E,
    ft: &FT,
) -> Result<Datatype, VirErr>
where
    FT: Fn(&mut E, &Typ) -> Result<Typ, VirErr>,
{
    let datatypex = datatype.x.clone();
    let mut variants: Vec<Variant> = Vec::new();
    for variant in datatypex.variants.iter() {
        let mut fields: Vec<Field> = Vec::new();
        for field in variant.a.iter() {
            let (typ, mode, vis) = &field.a;
            let typ = map_typ_visitor_env(typ, env, ft)?;
            fields.push(field.new_a((typ, *mode, vis.clone())));
        }
        variants.push(variant.new_a(Arc::new(fields)));
    }
    let variants = Arc::new(variants);
    Ok(Spanned::new(datatype.span.clone(), DatatypeX { variants, ..datatypex }))
}
