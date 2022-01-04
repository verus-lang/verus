use crate::ast::{
    Arm, ArmX, CallTarget, Datatype, DatatypeX, Expr, ExprX, Field, Function, FunctionX,
    GenericBound, GenericBoundX, Ident, MaskSpec, Param, ParamX, Pattern, PatternX, SpannedTyped,
    Stmt, StmtX, Typ, TypX, UnaryOpr, Variant, VirErr,
};
use crate::ast_util::err_str;
use crate::def::Spanned;
use crate::util::vec_map_result;
use air::scope_map::ScopeMap;
use std::sync::Arc;

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

fn insert_pattern_vars(map: &mut ScopeMap<Ident, Typ>, pattern: &Pattern) {
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

pub(crate) fn map_expr_visitor_env<E, FE, FS, FT>(
    expr: &Expr,
    map: &mut ScopeMap<Ident, Typ>,
    env: &mut E,
    fe: &FE,
    fs: &FS,
    ft: &FT,
) -> Result<Expr, VirErr>
where
    FE: Fn(&mut E, &mut ScopeMap<Ident, Typ>, &Expr) -> Result<Expr, VirErr>,
    FS: Fn(&mut E, &mut ScopeMap<Ident, Typ>, &Stmt) -> Result<Vec<Stmt>, VirErr>,
    FT: Fn(&mut E, &Typ) -> Result<Typ, VirErr>,
{
    let exprx = match &expr.x {
        ExprX::Const(c) => ExprX::Const(c.clone()),
        ExprX::Var(x) => ExprX::Var(x.clone()),
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
        ExprX::Choose(binder, e1) => {
            let binder = binder.map_result(|t| map_typ_visitor_env(t, env, ft))?;
            map.push_scope(true);
            let _ = map.insert(binder.name.clone(), binder.a.clone());
            let expr1 = map_expr_visitor_env(e1, map, env, fe, fs, ft)?;
            map.pop_scope();
            ExprX::Choose(binder, expr1)
        }
        ExprX::Assign(e1, e2) => {
            let expr1 = map_expr_visitor_env(e1, map, env, fe, fs, ft)?;
            let expr2 = map_expr_visitor_env(e2, map, env, fe, fs, ft)?;
            ExprX::Assign(expr1, expr2)
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
        ExprX::OpenInvariant(e1, binder, e2) => {
            let expr1 = map_expr_visitor_env(e1, map, env, fe, fs, ft)?;
            let binder = binder.map_result(|t| map_typ_visitor_env(t, env, ft))?;
            map.push_scope(true);
            let _ = map.insert(binder.name.clone(), binder.a.clone());
            let expr2 = map_expr_visitor_env(e2, map, env, fe, fs, ft)?;
            map.pop_scope();
            ExprX::OpenInvariant(expr1, binder, expr2)
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

pub(crate) fn map_expr_visitor<F>(expr: &Expr, f: &mut F) -> Result<Expr, VirErr>
where
    F: FnMut(&Expr) -> Result<Expr, VirErr>,
{
    let mut map: ScopeMap<Ident, Typ> = ScopeMap::new();
    map_expr_visitor_env(
        expr,
        &mut map,
        f,
        &|f, _, e| f(e),
        &|_, _, s| Ok(vec![s.clone()]),
        &|_, t| Ok(t.clone()),
    )
}

pub(crate) fn map_param_visitor<E, FT>(param: &Param, env: &mut E, ft: &FT) -> Result<Param, VirErr>
where
    FT: Fn(&mut E, &Typ) -> Result<Typ, VirErr>,
{
    let typ = map_typ_visitor_env(&param.x.typ, env, ft)?;
    let paramx = ParamX { name: param.x.name.clone(), typ, mode: param.x.mode };
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
        GenericBoundX::None => Ok(bound.clone()),
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
        visibility,
        mode,
        fuel,
        typ_bounds,
        params,
        ret,
        require,
        ensure,
        decrease,
        mask_spec,
        is_abstract,
        attrs,
        body,
    } = &function.x;
    let name = name.clone();
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
    let ensure =
        Arc::new(vec_map_result(ensure, |e| map_expr_visitor_env(e, map, env, fe, fs, ft))?);
    let decrease =
        Arc::new(vec_map_result(decrease, |e| map_expr_visitor_env(e, map, env, fe, fs, ft))?);
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
    let is_abstract = *is_abstract;
    let body = body.as_ref().map(|e| map_expr_visitor_env(e, map, env, fe, fs, ft)).transpose()?;
    map.pop_scope();
    let functionx = FunctionX {
        name,
        visibility,
        mode,
        fuel,
        typ_bounds: Arc::new(type_bounds),
        params,
        ret,
        require,
        ensure,
        decrease,
        mask_spec,
        is_abstract,
        attrs,
        body,
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
            let (typ, mode) = &field.a;
            let typ = map_typ_visitor_env(typ, env, ft)?;
            fields.push(field.new_a((typ, *mode)));
        }
        variants.push(variant.new_a(Arc::new(fields)));
    }
    let variants = Arc::new(variants);
    Ok(Spanned::new(datatype.span.clone(), DatatypeX { variants, ..datatypex }))
}
