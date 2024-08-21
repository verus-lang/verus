use crate::ast::{
    Arm, ArmX, AssocTypeImpl, AssocTypeImplX, CallTarget, Datatype, DatatypeX, Expr, ExprX, Field,
    Function, FunctionKind, FunctionX, GenericBound, GenericBoundX, MaskSpec, Param, ParamX,
    Params, Pattern, PatternX, SpannedTyped, Stmt, StmtX, TraitImpl, TraitImplX, Typ,
    TypDecorationArg, TypX, Typs, UnaryOpr, UnwindSpec, VarIdent, Variant, VirErr,
};
use crate::def::Spanned;
use crate::messages::error;
use crate::util::vec_map_result;
use crate::visitor::expr_visitor_control_flow;
pub(crate) use crate::visitor::{Returner, Rewrite, VisitorControlFlow, Walk};
use air::scope_map::ScopeMap;
use std::sync::Arc;

pub struct ScopeEntry {
    pub typ: Typ,
    pub is_mut: bool,
    pub init: bool,
    pub is_outer_param_or_ret: bool,
}

pub type VisitorScopeMap = ScopeMap<VarIdent, ScopeEntry>;

impl ScopeEntry {
    fn new(typ: &Typ, is_mut: bool, init: bool) -> Self {
        ScopeEntry { typ: typ.clone(), is_mut, init, is_outer_param_or_ret: false }
    }
    fn new_outer_param_ret(typ: &Typ, is_mut: bool, init: bool) -> Self {
        ScopeEntry { typ: typ.clone(), is_mut, init, is_outer_param_or_ret: true }
    }
}

pub(crate) trait TypVisitor<R: Returner, Err> {
    fn visit_typ(&mut self, typ: &Typ) -> Result<R::Ret<Typ>, Err>;

    fn visit_typs(&mut self, typs: &Vec<Typ>) -> Result<R::Vec<Typ>, Err> {
        R::map_vec(typs, &mut |t| self.visit_typ(t))
    }

    fn visit_typ_rec(&mut self, typ: &Typ) -> Result<R::Ret<Typ>, Err> {
        match &**typ {
            TypX::Bool => R::ret(|| typ.clone()),
            TypX::Int(_) => R::ret(|| typ.clone()),
            TypX::TypParam(_) => R::ret(|| typ.clone()),
            TypX::TypeId => R::ret(|| typ.clone()),
            TypX::ConstInt(_) => R::ret(|| typ.clone()),
            TypX::Air(_) => R::ret(|| typ.clone()),
            TypX::Tuple(ts) => {
                let ts = self.visit_typs(ts)?;
                R::ret(|| Arc::new(TypX::Tuple(R::get_vec_a(ts))))
            }
            TypX::SpecFn(ts, tr) => {
                let ts = self.visit_typs(ts)?;
                let tr = self.visit_typ(tr)?;
                R::ret(|| Arc::new(TypX::SpecFn(R::get_vec_a(ts), R::get(tr))))
            }
            TypX::AnonymousClosure(ts, tr, id) => {
                let ts = self.visit_typs(ts)?;
                let tr = self.visit_typ(tr)?;
                R::ret(|| Arc::new(TypX::AnonymousClosure(R::get_vec_a(ts), R::get(tr), *id)))
            }
            TypX::FnDef(fun, ts, res_fun) => {
                let ts = self.visit_typs(ts)?;
                R::ret(|| Arc::new(TypX::FnDef(fun.clone(), R::get_vec_a(ts), res_fun.clone())))
            }
            TypX::Datatype(path, ts, impl_paths) => {
                let ts = self.visit_typs(ts)?;
                R::ret(|| {
                    Arc::new(TypX::Datatype(path.clone(), R::get_vec_a(ts), impl_paths.clone()))
                })
            }
            TypX::Primitive(p, ts) => {
                let ts = self.visit_typs(ts)?;
                R::ret(|| Arc::new(TypX::Primitive(p.clone(), R::get_vec_a(ts))))
            }
            TypX::Decorate(d, targ, t) => {
                let targ = if let Some(TypDecorationArg { allocator_typ }) = targ {
                    let allocator_typ = self.visit_typ(allocator_typ)?;
                    R::ret(|| Some(TypDecorationArg { allocator_typ: R::get(allocator_typ) }))
                } else {
                    R::ret(|| None)
                }?;
                let t = self.visit_typ(t)?;
                R::ret(|| Arc::new(TypX::Decorate(*d, R::get(targ), R::get(t))))
            }
            TypX::Boxed(t) => {
                let t = self.visit_typ(t)?;
                R::ret(|| Arc::new(TypX::Boxed(R::get(t))))
            }
            TypX::Projection { trait_typ_args, trait_path, name } => {
                let trait_typ_args = self.visit_typs(trait_typ_args)?;
                R::ret(|| {
                    Arc::new(TypX::Projection {
                        trait_typ_args: R::get_vec_a(trait_typ_args),
                        trait_path: trait_path.clone(),
                        name: name.clone(),
                    })
                })
            }
        }
    }
}

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

struct TypVisitorDfs<'a, FT>(&'a mut FT);

impl<'a, T, FT> TypVisitor<Walk, T> for TypVisitorDfs<'a, FT>
where
    FT: FnMut(&Typ) -> VisitorControlFlow<T>,
{
    fn visit_typ(&mut self, typ: &Typ) -> Result<(), T> {
        match (self.0)(typ) {
            VisitorControlFlow::Stop(val) => Err(val),
            VisitorControlFlow::Return => Ok(()),
            VisitorControlFlow::Recurse => self.visit_typ_rec(typ),
        }
    }
}

pub(crate) fn typ_visitor_dfs<T, FT>(typ: &Typ, ft: &mut FT) -> VisitorControlFlow<T>
where
    FT: FnMut(&Typ) -> VisitorControlFlow<T>,
{
    let mut visitor = TypVisitorDfs(ft);
    match visitor.visit_typ(typ) {
        Ok(()) => VisitorControlFlow::Recurse,
        Err(val) => VisitorControlFlow::Stop(val),
    }
}

struct MapTypVisitorEnv<'a, E, FT> {
    env: &'a mut E,
    ft: &'a FT,
}

impl<'a, E, FT> TypVisitor<Rewrite, VirErr> for MapTypVisitorEnv<'a, E, FT>
where
    FT: Fn(&mut E, &Typ) -> Result<Typ, VirErr>,
{
    fn visit_typ(&mut self, typ: &Typ) -> Result<Typ, VirErr> {
        let typ = self.visit_typ_rec(typ)?;
        (self.ft)(&mut self.env, &typ)
    }
}

pub(crate) fn map_typ_visitor_env<E, FT>(typ: &Typ, env: &mut E, ft: &FT) -> Result<Typ, VirErr>
where
    FT: Fn(&mut E, &Typ) -> Result<Typ, VirErr>,
{
    let mut visitor = MapTypVisitorEnv { env, ft };
    visitor.visit_typ(typ)
}

pub(crate) fn map_typs_visitor_env<E, FT>(typs: &Typs, env: &mut E, ft: &FT) -> Result<Typs, VirErr>
where
    FT: Fn(&mut E, &Typ) -> Result<Typ, VirErr>,
{
    let mut visitor = MapTypVisitorEnv { env, ft };
    Ok(Arc::new(visitor.visit_typs(typs)?))
}

struct MapTypVisitor<'a, FT>(&'a FT);

impl<'a, FT> TypVisitor<Rewrite, VirErr> for MapTypVisitor<'a, FT>
where
    FT: Fn(&Typ) -> Result<Typ, VirErr>,
{
    fn visit_typ(&mut self, typ: &Typ) -> Result<Typ, VirErr> {
        let typ = self.visit_typ_rec(typ)?;
        (self.0)(&typ)
    }
}

pub(crate) fn map_typ_visitor<FT>(typ: &Typ, ft: &FT) -> Result<Typ, VirErr>
where
    FT: Fn(&Typ) -> Result<Typ, VirErr>,
{
    let mut visitor = MapTypVisitor(ft);
    visitor.visit_typ(typ)
}

pub(crate) fn map_pattern_visitor_env<E, FE, FS, FT>(
    pattern: &Pattern,
    map: &mut VisitorScopeMap,
    env: &mut E,
    fe: &FE,
    fs: &FS,
    ft: &FT,
) -> Result<Pattern, VirErr>
where
    FE: Fn(&mut E, &mut VisitorScopeMap, &Expr) -> Result<Expr, VirErr>,
    FS: Fn(&mut E, &mut VisitorScopeMap, &Stmt) -> Result<Vec<Stmt>, VirErr>,
    FT: Fn(&mut E, &Typ) -> Result<Typ, VirErr>,
{
    let patternx = match &pattern.x {
        PatternX::Wildcard(dd) => PatternX::Wildcard(*dd),
        PatternX::Var { name, mutable } => PatternX::Var { name: name.clone(), mutable: *mutable },
        PatternX::Binding { name, mutable, sub_pat } => {
            let p = map_pattern_visitor_env(sub_pat, map, env, fe, fs, ft)?;
            PatternX::Binding { name: name.clone(), mutable: *mutable, sub_pat: p }
        }
        PatternX::Tuple(ps) => {
            let ps = vec_map_result(&**ps, |p| map_pattern_visitor_env(p, map, env, fe, fs, ft))?;
            PatternX::Tuple(Arc::new(ps))
        }
        PatternX::Constructor(path, variant, binders) => {
            let binders = vec_map_result(&**binders, |b| {
                b.map_result(|p| map_pattern_visitor_env(p, map, env, fe, fs, ft))
            })?;
            PatternX::Constructor(path.clone(), variant.clone(), Arc::new(binders))
        }
        PatternX::Or(pat1, pat2) => {
            let p1 = map_pattern_visitor_env(pat1, map, env, fe, fs, ft)?;
            let p2 = map_pattern_visitor_env(pat2, map, env, fe, fs, ft)?;
            PatternX::Or(p1, p2)
        }
        PatternX::Expr(expr) => {
            let e = map_expr_visitor_env(expr, map, env, fe, fs, ft)?;
            PatternX::Expr(e)
        }
        PatternX::Range(expr1, expr2) => {
            let e1 = match expr1 {
                Some(expr1) => Some(map_expr_visitor_env(expr1, map, env, fe, fs, ft)?),
                None => None,
            };
            let e2 = match expr2 {
                Some((expr2, op)) => {
                    let e2 = map_expr_visitor_env(expr2, map, env, fe, fs, ft)?;
                    Some((e2, *op))
                }
                None => None,
            };
            PatternX::Range(e1, e2)
        }
    };
    Ok(SpannedTyped::new(&pattern.span, &map_typ_visitor_env(&pattern.typ, env, ft)?, patternx))
}

fn insert_pattern_vars(map: &mut VisitorScopeMap, pattern: &Pattern, init: bool) {
    match &pattern.x {
        PatternX::Wildcard(_) => {}
        PatternX::Var { name, mutable } => {
            let _ = map.insert(name.clone(), ScopeEntry::new(&pattern.typ, *mutable, init));
        }
        PatternX::Binding { name, mutable, sub_pat } => {
            insert_pattern_vars(map, sub_pat, init);
            let _ = map.insert(name.clone(), ScopeEntry::new(&pattern.typ, *mutable, init));
        }
        PatternX::Tuple(ps) => {
            for p in ps.iter() {
                insert_pattern_vars(map, p, init);
            }
        }
        PatternX::Constructor(_, _, binders) => {
            for binder in binders.iter() {
                insert_pattern_vars(map, &binder.a, init);
            }
        }
        PatternX::Or(pat1, _) => {
            insert_pattern_vars(map, pat1, init);
            // pat2 should bind an identical set of variables
        }
        PatternX::Expr(_) => {}
        PatternX::Range(_, _) => {}
    }
}

pub(crate) fn expr_visitor_traverse<MF>(expr: &Expr, map: &mut VisitorScopeMap, mf: &mut MF)
where
    MF: FnMut(&mut VisitorScopeMap, &Expr) -> (),
{
    let _ = expr_visitor_dfs::<(), _>(expr, map, &mut |scope_map, expr| {
        mf(scope_map, expr);
        VisitorControlFlow::Recurse
    });
}

pub(crate) fn expr_visitor_check<E, MF>(expr: &Expr, mf: &mut MF) -> Result<(), E>
where
    MF: FnMut(&VisitorScopeMap, &Expr) -> Result<(), E>,
{
    let mut scope_map: VisitorScopeMap = ScopeMap::new();
    match expr_visitor_dfs(expr, &mut scope_map, &mut |scope_map, expr| match mf(scope_map, expr) {
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
                | ExprX::ConstVar(..)
                | ExprX::StaticVar(..)
                | ExprX::AirStmt(_) => (),
                ExprX::Loc(e) => {
                    expr_visitor_control_flow!(expr_visitor_dfs(e, map, mf));
                }
                ExprX::Call(target, es) => {
                    match target {
                        CallTarget::Fun(_, _, _, _, _) => (),
                        CallTarget::BuiltinSpecFun(_, _, _) => (),
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
                ExprX::ArrayLiteral(es) => {
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
                ExprX::NullaryOpr(_op) => (),
                ExprX::Unary(_op, e1) => {
                    expr_visitor_control_flow!(expr_visitor_dfs(e1, map, mf));
                }
                ExprX::UnaryOpr(_op, e1) => {
                    expr_visitor_control_flow!(expr_visitor_dfs(e1, map, mf));
                }
                ExprX::Binary(_, e1, e2) | ExprX::BinaryOpr(_, e1, e2) => {
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
                        let _ = map
                            .insert(binder.name.clone(), ScopeEntry::new(&binder.a, false, true));
                    }
                    expr_visitor_control_flow!(expr_visitor_dfs(e1, map, mf));
                    map.pop_scope();
                }
                ExprX::Closure(params, body) => {
                    map.push_scope(true);
                    for binder in params.iter() {
                        let _ = map
                            .insert(binder.name.clone(), ScopeEntry::new(&binder.a, false, true));
                    }
                    expr_visitor_control_flow!(expr_visitor_dfs(body, map, mf));
                    map.pop_scope();
                }
                ExprX::ExecClosure { params, ret, requires, ensures, body, external_spec } => {
                    map.push_scope(true);
                    for binder in params.iter() {
                        let _ = map
                            .insert(binder.name.clone(), ScopeEntry::new(&binder.a, false, true));
                    }
                    for req in requires.iter() {
                        expr_visitor_control_flow!(expr_visitor_dfs(req, map, mf));
                    }
                    map.push_scope(true);
                    let _ = map.insert(ret.name.clone(), ScopeEntry::new(&ret.a, false, true));
                    for ens in ensures.iter() {
                        expr_visitor_control_flow!(expr_visitor_dfs(ens, map, mf));
                    }
                    map.pop_scope();
                    expr_visitor_control_flow!(expr_visitor_dfs(body, map, mf));
                    map.pop_scope();

                    match external_spec {
                        None => {}
                        Some((cid, cexpr)) => {
                            map.push_scope(true);
                            let _ =
                                map.insert(cid.clone(), ScopeEntry::new(&expr.typ, false, true));
                            expr_visitor_control_flow!(expr_visitor_dfs(&cexpr, map, mf));
                            map.pop_scope();
                        }
                    }
                }
                ExprX::ExecFnByName(_fun) => {}
                ExprX::Choose { params, cond, body } => {
                    map.push_scope(true);
                    for binder in params.iter() {
                        let _ = map
                            .insert(binder.name.clone(), ScopeEntry::new(&binder.a, false, true));
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
                ExprX::Assign { init_not_mut: _, lhs: e1, rhs: e2, op: _ } => {
                    expr_visitor_control_flow!(expr_visitor_dfs(e1, map, mf));
                    expr_visitor_control_flow!(expr_visitor_dfs(e2, map, mf));
                }
                ExprX::AssertCompute(e, _) => {
                    expr_visitor_control_flow!(expr_visitor_dfs(e, map, mf));
                }
                ExprX::Fuel(_, _, _) => (),
                ExprX::RevealString(_) => (),
                ExprX::Header(_) => {
                    panic!("header expression not allowed here: {:?}", &expr.span);
                }
                ExprX::AssertAssume { is_assume: _, expr: e1 } => {
                    expr_visitor_control_flow!(expr_visitor_dfs(e1, map, mf));
                }
                ExprX::AssertAssumeUserDefinedTypeInvariant { is_assume: _, expr: e1, fun: _ } => {
                    expr_visitor_control_flow!(expr_visitor_dfs(e1, map, mf));
                }
                ExprX::AssertBy { vars, require, ensure, proof } => {
                    map.push_scope(true);
                    for binder in vars.iter() {
                        let _ = map
                            .insert(binder.name.clone(), ScopeEntry::new(&binder.a, false, true));
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
                        insert_pattern_vars(map, &arm.x.pattern, true);
                        expr_visitor_control_flow!(pat_visitor_dfs(&arm.x.pattern, map, mf));
                        expr_visitor_control_flow!(expr_visitor_dfs(&arm.x.guard, map, mf));
                        expr_visitor_control_flow!(expr_visitor_dfs(&arm.x.body, map, mf));
                        map.pop_scope();
                    }
                }
                ExprX::Loop {
                    loop_isolation: _,
                    is_for_loop: _,
                    label: _,
                    cond,
                    body,
                    invs,
                    decrease,
                } => {
                    if let Some(cond) = cond {
                        expr_visitor_control_flow!(expr_visitor_dfs(cond, map, mf));
                    }
                    expr_visitor_control_flow!(expr_visitor_dfs(body, map, mf));
                    for inv in invs.iter() {
                        expr_visitor_control_flow!(expr_visitor_dfs(&inv.inv, map, mf));
                    }
                    for dec in decrease.iter() {
                        expr_visitor_control_flow!(expr_visitor_dfs(dec, map, mf));
                    }
                }
                ExprX::OpenInvariant(inv, binder, body, _atomicity) => {
                    expr_visitor_control_flow!(expr_visitor_dfs(inv, map, mf));
                    map.push_scope(true);
                    let _ = map.insert(binder.name.clone(), ScopeEntry::new(&binder.a, true, true));
                    expr_visitor_control_flow!(expr_visitor_dfs(body, map, mf));
                    map.pop_scope();
                }
                ExprX::Return(e1) => match e1 {
                    None => (),
                    Some(e) => expr_visitor_control_flow!(expr_visitor_dfs(e, map, mf)),
                },
                ExprX::BreakOrContinue { label: _, is_break: _ } => (),
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

pub(crate) fn expr_visitor_walk<MF>(expr: &Expr, mf: &mut MF)
where
    MF: FnMut(&Expr) -> VisitorControlFlow<()>,
{
    let mut scope_map: VisitorScopeMap = ScopeMap::new();
    expr_visitor_dfs(expr, &mut scope_map, &mut |_scope_map, expr| mf(expr));
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
            insert_pattern_vars(map, &pattern, init.is_some());
            expr_visitor_control_flow!(pat_visitor_dfs(&pattern, map, mf));
        }
    }
    VisitorControlFlow::Recurse
}

pub(crate) fn pat_visitor_dfs<T, MF>(
    pat: &Pattern,
    map: &mut VisitorScopeMap,
    mf: &mut MF,
) -> VisitorControlFlow<T>
where
    MF: FnMut(&mut VisitorScopeMap, &Expr) -> VisitorControlFlow<T>,
{
    match &pat.x {
        PatternX::Wildcard(_dd) => {}
        PatternX::Var { name: _, mutable: _ } => {}
        PatternX::Binding { name: _, mutable: _, sub_pat } => {
            expr_visitor_control_flow!(pat_visitor_dfs(sub_pat, map, mf));
        }
        PatternX::Tuple(ps) => {
            for p in ps.iter() {
                expr_visitor_control_flow!(pat_visitor_dfs(p, map, mf));
            }
        }
        PatternX::Constructor(_path, _variant, binders) => {
            for binder in binders.iter() {
                expr_visitor_control_flow!(pat_visitor_dfs(&binder.a, map, mf));
            }
        }
        PatternX::Or(pat1, pat2) => {
            expr_visitor_control_flow!(pat_visitor_dfs(pat1, map, mf));
            expr_visitor_control_flow!(pat_visitor_dfs(pat2, map, mf));
        }
        PatternX::Expr(expr) => {
            expr_visitor_control_flow!(expr_visitor_dfs(expr, map, mf));
        }
        PatternX::Range(expr1, expr2) => {
            if let Some(expr1) = expr1 {
                expr_visitor_control_flow!(expr_visitor_dfs(expr1, map, mf));
            }
            if let Some((expr2, _ineq_op)) = expr2 {
                expr_visitor_control_flow!(expr_visitor_dfs(expr2, map, mf));
            }
        }
    };
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
        proxy: _,
        kind: _,
        visibility: _,
        owning_module: _,
        mode: _,
        fuel: _,
        typ_params: _,
        typ_bounds: _,
        params,
        ret,
        require,
        ensure,
        decrease,
        decrease_when,
        decrease_by: _,
        broadcast_forall,
        fndef_axioms,
        mask_spec,
        unwind_spec,
        item_kind: _,
        publish: _,
        attrs: _,
        body,
        extra_dependencies: _,
    } = &function.x;

    map.push_scope(true);
    for p in params.iter() {
        let _ = map
            .insert(p.x.name.clone(), ScopeEntry::new_outer_param_ret(&p.x.typ, p.x.is_mut, true));
    }
    for e in require.iter() {
        expr_visitor_control_flow!(expr_visitor_dfs(e, map, mf));
    }

    map.push_scope(true);
    if function.x.has_return_name() {
        let _ = map
            .insert(ret.x.name.clone(), ScopeEntry::new_outer_param_ret(&ret.x.typ, false, true));
    }
    for e in ensure.iter() {
        expr_visitor_control_flow!(expr_visitor_dfs(e, map, mf));
    }
    map.pop_scope();

    for e in decrease.iter() {
        expr_visitor_control_flow!(expr_visitor_dfs(e, map, mf));
    }
    if let Some(e) = decrease_when {
        expr_visitor_control_flow!(expr_visitor_dfs(e, map, mf));
    }
    match mask_spec {
        None => {}
        Some(MaskSpec::InvariantOpens(es) | MaskSpec::InvariantOpensExcept(es)) => {
            for e in es.iter() {
                expr_visitor_control_flow!(expr_visitor_dfs(e, map, mf));
            }
        }
    }
    match unwind_spec {
        None => {}
        Some(UnwindSpec::MayUnwind) => {}
        Some(UnwindSpec::NoUnwind) => {}
        Some(UnwindSpec::NoUnwindWhen(e)) => {
            expr_visitor_control_flow!(expr_visitor_dfs(e, map, mf));
        }
    }

    if let Some(e) = body {
        expr_visitor_control_flow!(expr_visitor_dfs(e, map, mf));
    }
    map.pop_scope();

    if let Some((params, req_ens)) = broadcast_forall {
        map.push_scope(true);
        for p in params.iter() {
            let _ = map.insert(p.x.name.clone(), ScopeEntry::new(&p.x.typ, p.x.is_mut, true));
        }
        expr_visitor_control_flow!(expr_visitor_dfs(req_ens, map, mf));
        map.pop_scope();
    }

    if let Some(es) = fndef_axioms {
        for e in es.iter() {
            expr_visitor_control_flow!(expr_visitor_dfs(e, map, mf));
        }
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
        ExprX::ConstVar(x, a) => ExprX::ConstVar(x.clone(), *a),
        ExprX::StaticVar(x) => ExprX::StaticVar(x.clone()),
        ExprX::Loc(e) => ExprX::Loc(map_expr_visitor_env(e, map, env, fe, fs, ft)?),
        ExprX::Call(target, es) => {
            let target = match target {
                CallTarget::Fun(kind, x, typs, impl_paths, autospec_usage) => {
                    use crate::ast::CallTargetKind;
                    let kind = match kind {
                        CallTargetKind::Static | CallTargetKind::Dynamic => kind.clone(),
                        CallTargetKind::DynamicResolved {
                            resolved,
                            typs,
                            impl_paths,
                            is_trait_default,
                        } => {
                            let typs = map_typs_visitor_env(typs, env, ft)?;
                            CallTargetKind::DynamicResolved {
                                resolved: resolved.clone(),
                                typs,
                                impl_paths: impl_paths.clone(),
                                is_trait_default: *is_trait_default,
                            }
                        }
                    };
                    CallTarget::Fun(
                        kind.clone(),
                        x.clone(),
                        map_typs_visitor_env(typs, env, ft)?,
                        impl_paths.clone(),
                        *autospec_usage,
                    )
                }
                CallTarget::BuiltinSpecFun(x, typs, impl_paths) => CallTarget::BuiltinSpecFun(
                    x.clone(),
                    map_typs_visitor_env(typs, env, ft)?,
                    impl_paths.clone(),
                ),
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
        ExprX::ArrayLiteral(es) => {
            let mut exprs: Vec<Expr> = Vec::new();
            for e in es.iter() {
                exprs.push(map_expr_visitor_env(e, map, env, fe, fs, ft)?);
            }
            ExprX::ArrayLiteral(Arc::new(exprs))
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
        ExprX::NullaryOpr(crate::ast::NullaryOpr::ConstGeneric(t)) => {
            let t = map_typ_visitor_env(t, env, ft)?;
            ExprX::NullaryOpr(crate::ast::NullaryOpr::ConstGeneric(t))
        }
        ExprX::NullaryOpr(crate::ast::NullaryOpr::TraitBound(p, ts)) => {
            let ts = map_typs_visitor_env(ts, env, ft)?;
            ExprX::NullaryOpr(crate::ast::NullaryOpr::TraitBound(p.clone(), ts))
        }
        ExprX::NullaryOpr(crate::ast::NullaryOpr::TypEqualityBound(p, ts, x, t)) => {
            let ts = map_typs_visitor_env(ts, env, ft)?;
            let t = map_typ_visitor_env(t, env, ft)?;
            ExprX::NullaryOpr(crate::ast::NullaryOpr::TypEqualityBound(p.clone(), ts, x.clone(), t))
        }
        ExprX::NullaryOpr(crate::ast::NullaryOpr::ConstTypBound(t1, t2)) => {
            let t1 = map_typ_visitor_env(t1, env, ft)?;
            let t2 = map_typ_visitor_env(t2, env, ft)?;
            ExprX::NullaryOpr(crate::ast::NullaryOpr::ConstTypBound(t1, t2))
        }
        ExprX::NullaryOpr(crate::ast::NullaryOpr::NoInferSpecForLoopIter) => {
            ExprX::NullaryOpr(crate::ast::NullaryOpr::NoInferSpecForLoopIter)
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
                UnaryOpr::IntegerTypeBound(_kind, _) => op.clone(),
                UnaryOpr::CustomErr(_) => op.clone(),
            };
            let expr1 = map_expr_visitor_env(e1, map, env, fe, fs, ft)?;
            ExprX::UnaryOpr(op.clone(), expr1)
        }
        ExprX::Binary(op, e1, e2) => {
            let expr1 = map_expr_visitor_env(e1, map, env, fe, fs, ft)?;
            let expr2 = map_expr_visitor_env(e2, map, env, fe, fs, ft)?;
            ExprX::Binary(*op, expr1, expr2)
        }
        ExprX::BinaryOpr(crate::ast::BinaryOpr::ExtEq(deep, t), e1, e2) => {
            let t = map_typ_visitor_env(t, env, ft)?;
            let expr1 = map_expr_visitor_env(e1, map, env, fe, fs, ft)?;
            let expr2 = map_expr_visitor_env(e2, map, env, fe, fs, ft)?;
            ExprX::BinaryOpr(crate::ast::BinaryOpr::ExtEq(*deep, t), expr1, expr2)
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
                let _ = map.insert(binder.name.clone(), ScopeEntry::new(&binder.a, false, true));
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
                let _ = map.insert(binder.name.clone(), ScopeEntry::new(&binder.a, false, true));
            }
            let body = map_expr_visitor_env(body, map, env, fe, fs, ft)?;
            map.pop_scope();
            ExprX::Closure(Arc::new(params), body)
        }
        ExprX::ExecClosure { params, ret, requires, ensures, body, external_spec } => {
            let params =
                vec_map_result(&**params, |b| b.map_result(|t| map_typ_visitor_env(t, env, ft)))?;
            let ret = ret.map_result(|t| map_typ_visitor_env(t, env, ft))?;

            map.push_scope(true);
            for binder in params.iter() {
                let _ = map.insert(binder.name.clone(), ScopeEntry::new(&binder.a, false, true));
            }
            let requires =
                vec_map_result(&**requires, |req| map_expr_visitor_env(req, map, env, fe, fs, ft))?;
            map.push_scope(true);
            let _ = map.insert(ret.name.clone(), ScopeEntry::new(&ret.a, false, true));
            let ensures =
                vec_map_result(&**ensures, |ens| map_expr_visitor_env(ens, map, env, fe, fs, ft))?;
            map.pop_scope();
            let body = map_expr_visitor_env(body, map, env, fe, fs, ft)?;
            map.pop_scope();

            let external_spec = match external_spec {
                None => None,
                Some((cid, cexpr)) => {
                    map.push_scope(true);
                    let _ = map.insert(cid.clone(), ScopeEntry::new(&expr.typ, false, true));
                    let cexpr0 = map_expr_visitor_env(cexpr, map, env, fe, fs, ft)?;
                    map.pop_scope();

                    Some((cid.clone(), cexpr0))
                }
            };

            ExprX::ExecClosure {
                params: Arc::new(params),
                ret,
                requires: Arc::new(requires),
                ensures: Arc::new(ensures),
                body,
                external_spec,
            }
        }
        ExprX::ExecFnByName(fun) => ExprX::ExecFnByName(fun.clone()),
        ExprX::Choose { params, cond, body } => {
            let params =
                vec_map_result(&**params, |b| b.map_result(|t| map_typ_visitor_env(t, env, ft)))?;
            map.push_scope(true);
            for binder in params.iter() {
                let _ = map.insert(binder.name.clone(), ScopeEntry::new(&binder.a, false, true));
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
        ExprX::Assign { init_not_mut, lhs: e1, rhs: e2, op } => {
            let expr1 = map_expr_visitor_env(e1, map, env, fe, fs, ft)?;
            let expr2 = map_expr_visitor_env(e2, map, env, fe, fs, ft)?;
            ExprX::Assign { init_not_mut: *init_not_mut, lhs: expr1, rhs: expr2, op: *op }
        }
        ExprX::Fuel(path, fuel, is_broadcast_use) => {
            ExprX::Fuel(path.clone(), *fuel, *is_broadcast_use)
        }
        ExprX::RevealString(path) => ExprX::RevealString(path.clone()),
        ExprX::Header(_) => {
            return Err(error(&expr.span, "header expression not allowed here"));
        }
        ExprX::AssertAssume { is_assume, expr: e1 } => {
            let expr1 = map_expr_visitor_env(e1, map, env, fe, fs, ft)?;
            ExprX::AssertAssume { is_assume: *is_assume, expr: expr1 }
        }
        ExprX::AssertAssumeUserDefinedTypeInvariant { is_assume, expr: e1, fun } => {
            let expr1 = map_expr_visitor_env(e1, map, env, fe, fs, ft)?;
            ExprX::AssertAssumeUserDefinedTypeInvariant {
                is_assume: *is_assume,
                expr: expr1,
                fun: fun.clone(),
            }
        }
        ExprX::AssertBy { vars, require, ensure, proof } => {
            let vars =
                vec_map_result(&**vars, |x| x.map_result(|t| map_typ_visitor_env(t, env, ft)))?;
            map.push_scope(true);
            for binder in vars.iter() {
                let _ = map.insert(binder.name.clone(), ScopeEntry::new(&binder.a, false, true));
            }
            let require = map_expr_visitor_env(require, map, env, fe, fs, ft)?;
            let ensure = map_expr_visitor_env(ensure, map, env, fe, fs, ft)?;
            let proof = map_expr_visitor_env(proof, map, env, fe, fs, ft)?;
            map.pop_scope();
            ExprX::AssertBy { vars: Arc::new(vars), require, ensure, proof }
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
        ExprX::AssertCompute(e, m) => {
            let expr1 = map_expr_visitor_env(e, map, env, fe, fs, ft)?;
            ExprX::AssertCompute(expr1, *m)
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
                let pattern = map_pattern_visitor_env(&arm.x.pattern, map, env, fe, fs, ft)?;
                insert_pattern_vars(map, &pattern, true);
                let guard = map_expr_visitor_env(&arm.x.guard, map, env, fe, fs, ft)?;
                let body = map_expr_visitor_env(&arm.x.body, map, env, fe, fs, ft)?;
                map.pop_scope();
                Ok(Spanned::new(arm.span.clone(), ArmX { pattern, guard, body }))
            });
            ExprX::Match(expr1, Arc::new(arms?))
        }
        ExprX::Loop { loop_isolation, is_for_loop, label, cond, body, invs, decrease } => {
            let cond =
                cond.as_ref().map(|e| map_expr_visitor_env(e, map, env, fe, fs, ft)).transpose()?;
            let body = map_expr_visitor_env(body, map, env, fe, fs, ft)?;
            let mut invs1: Vec<crate::ast::LoopInvariant> = Vec::new();
            for inv in invs.iter() {
                let e1 = map_expr_visitor_env(&inv.inv, map, env, fe, fs, ft)?;
                invs1.push(crate::ast::LoopInvariant { inv: e1, ..inv.clone() });
            }
            let decrease = Arc::new(vec_map_result(decrease, |e| {
                map_expr_visitor_env(e, map, env, fe, fs, ft)
            })?);
            ExprX::Loop {
                loop_isolation: *loop_isolation,
                is_for_loop: *is_for_loop,
                label: label.clone(),
                cond,
                body,
                invs: Arc::new(invs1),
                decrease,
            }
        }
        ExprX::Return(e1) => {
            let e1 = match e1 {
                None => None,
                Some(e) => Some(map_expr_visitor_env(e, map, env, fe, fs, ft)?),
            };
            ExprX::Return(e1)
        }
        ExprX::BreakOrContinue { label, is_break } => {
            ExprX::BreakOrContinue { label: label.clone(), is_break: *is_break }
        }
        ExprX::Ghost { alloc_wrapper, tracked, expr: e1 } => {
            let expr = map_expr_visitor_env(e1, map, env, fe, fs, ft)?;
            ExprX::Ghost { alloc_wrapper: *alloc_wrapper, tracked: *tracked, expr }
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
            let _ = map.insert(binder.name.clone(), ScopeEntry::new(&binder.a, true, true));
            let expr2 = map_expr_visitor_env(e2, map, env, fe, fs, ft)?;
            map.pop_scope();
            ExprX::OpenInvariant(expr1, binder, expr2, *atomicity)
        }
        ExprX::AirStmt(s) => ExprX::AirStmt(s.clone()),
    };
    let expr = SpannedTyped::new(&expr.span, &map_typ_visitor_env(&expr.typ, env, ft)?, exprx);
    fe(env, map, &expr)
}

pub(crate) fn map_expr_visitor<FE>(expr: &Expr, fe: &FE) -> Result<Expr, VirErr>
where
    FE: Fn(&Expr) -> Result<Expr, VirErr>,
{
    map_expr_visitor_env(
        expr,
        &mut air::scope_map::ScopeMap::new(),
        &mut (),
        &|_state, _, expr| fe(expr),
        &|_state, _, stmt| Ok(vec![stmt.clone()]),
        &|_state, typ| Ok(typ.clone()),
    )
}

pub(crate) fn map_stmt_visitor_env<E, FE, FS, FT>(
    stmt: &Stmt,
    map: &mut VisitorScopeMap,
    env: &mut E,
    fe: &FE,
    fs: &FS,
    ft: &FT,
) -> Result<Vec<Stmt>, VirErr>
where
    FE: Fn(&mut E, &mut VisitorScopeMap, &Expr) -> Result<Expr, VirErr>,
    FS: Fn(&mut E, &mut VisitorScopeMap, &Stmt) -> Result<Vec<Stmt>, VirErr>,
    FT: Fn(&mut E, &Typ) -> Result<Typ, VirErr>,
{
    match &stmt.x {
        StmtX::Expr(e) => {
            let expr = map_expr_visitor_env(e, map, env, fe, fs, ft)?;
            fs(env, map, &Spanned::new(stmt.span.clone(), StmtX::Expr(expr)))
        }
        StmtX::Decl { pattern, mode, init } => {
            let pattern = map_pattern_visitor_env(pattern, map, env, fe, fs, ft)?;
            let init =
                init.as_ref().map(|e| map_expr_visitor_env(e, map, env, fe, fs, ft)).transpose()?;
            insert_pattern_vars(map, &pattern, init.is_some());
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
    let paramx = ParamX {
        name: param.x.name.clone(),
        typ,
        mode: param.x.mode,
        is_mut: param.x.is_mut,
        unwrapped_info: param.x.unwrapped_info.clone(),
    };
    Ok(Spanned::new(param.span.clone(), paramx))
}

pub(crate) fn map_params_visitor<E, FT>(
    params: &Params,
    env: &mut E,
    ft: &FT,
) -> Result<Params, VirErr>
where
    FT: Fn(&mut E, &Typ) -> Result<Typ, VirErr>,
{
    Ok(Arc::new(vec_map_result(params, |p| map_param_visitor(p, env, ft))?))
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
        GenericBoundX::Trait(trait_path, ts) => {
            let ts = map_typs_visitor_env(ts, env, ft)?;
            Ok(Arc::new(GenericBoundX::Trait(trait_path.clone(), ts)))
        }
        GenericBoundX::TypEquality(trait_path, ts, name, t) => {
            let ts = map_typs_visitor_env(ts, env, ft)?;
            let t = map_typ_visitor_env(t, env, ft)?;
            Ok(Arc::new(GenericBoundX::TypEquality(trait_path.clone(), ts, name.clone(), t)))
        }
        GenericBoundX::ConstTyp(t, s) => {
            let t = map_typ_visitor_env(t, env, ft)?;
            let s = map_typ_visitor_env(s, env, ft)?;
            Ok(Arc::new(GenericBoundX::ConstTyp(t, s)))
        }
    }
}

pub(crate) fn map_generic_bounds_visitor<E, FT>(
    bounds: &crate::ast::GenericBounds,
    env: &mut E,
    ft: &FT,
) -> Result<crate::ast::GenericBounds, VirErr>
where
    FT: Fn(&mut E, &Typ) -> Result<Typ, VirErr>,
{
    Ok(Arc::new(vec_map_result(&**bounds, |b| map_generic_bound_visitor(b, env, ft))?))
}

pub(crate) fn map_function_visitor_env<E, FE, FS, FT>(
    function: &Function,
    map: &mut VisitorScopeMap,
    env: &mut E,
    fe: &FE,
    fs: &FS,
    ft: &FT,
) -> Result<Function, VirErr>
where
    FE: Fn(&mut E, &mut VisitorScopeMap, &Expr) -> Result<Expr, VirErr>,
    FS: Fn(&mut E, &mut VisitorScopeMap, &Stmt) -> Result<Vec<Stmt>, VirErr>,
    FT: Fn(&mut E, &Typ) -> Result<Typ, VirErr>,
{
    let FunctionX {
        name,
        proxy,
        kind,
        visibility,
        owning_module,
        mode,
        fuel,
        typ_params,
        typ_bounds,
        params,
        ret,
        require,
        ensure,
        decrease,
        decrease_when,
        decrease_by,
        broadcast_forall,
        fndef_axioms,
        mask_spec,
        unwind_spec,
        item_kind,
        publish,
        attrs,
        body,
        extra_dependencies,
    } = &function.x;
    let name = name.clone();
    let proxy = proxy.clone();
    let kind = match kind {
        FunctionKind::Static | FunctionKind::TraitMethodDecl { trait_path: _ } => kind.clone(),
        FunctionKind::TraitMethodImpl {
            method,
            impl_path,
            trait_path,
            trait_typ_args,
            inherit_body_from,
        } => FunctionKind::TraitMethodImpl {
            method: method.clone(),
            impl_path: impl_path.clone(),
            trait_path: trait_path.clone(),
            trait_typ_args: map_typs_visitor_env(trait_typ_args, env, ft)?,
            inherit_body_from: inherit_body_from.clone(),
        },
        FunctionKind::ForeignTraitMethodImpl { method, impl_path, trait_path, trait_typ_args } => {
            FunctionKind::ForeignTraitMethodImpl {
                method: method.clone(),
                impl_path: impl_path.clone(),
                trait_path: trait_path.clone(),
                trait_typ_args: map_typs_visitor_env(trait_typ_args, env, ft)?,
            }
        }
    };
    let visibility = visibility.clone();
    let owning_module = owning_module.clone();
    let mode = *mode;
    let fuel = *fuel;
    let typ_bounds = map_generic_bounds_visitor(typ_bounds, env, ft)?;
    map.push_scope(true);
    let params = map_params_visitor(params, env, ft)?;
    for p in params.iter() {
        let _ = map
            .insert(p.x.name.clone(), ScopeEntry::new_outer_param_ret(&p.x.typ, p.x.is_mut, true));
    }
    let ret = map_param_visitor(ret, env, ft)?;
    let require =
        Arc::new(vec_map_result(require, |e| map_expr_visitor_env(e, map, env, fe, fs, ft))?);

    map.push_scope(true);
    if function.x.has_return_name() {
        let _ = map
            .insert(ret.x.name.clone(), ScopeEntry::new_outer_param_ret(&ret.x.typ, false, true));
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
        None => None,
        Some(MaskSpec::InvariantOpens(es)) => {
            Some(MaskSpec::InvariantOpens(Arc::new(vec_map_result(es, |e| {
                map_expr_visitor_env(e, map, env, fe, fs, ft)
            })?)))
        }
        Some(MaskSpec::InvariantOpensExcept(es)) => {
            Some(MaskSpec::InvariantOpensExcept(Arc::new(vec_map_result(es, |e| {
                map_expr_visitor_env(e, map, env, fe, fs, ft)
            })?)))
        }
    };
    let unwind_spec = match unwind_spec {
        None => None,
        Some(UnwindSpec::MayUnwind) => Some(UnwindSpec::MayUnwind),
        Some(UnwindSpec::NoUnwind) => Some(UnwindSpec::NoUnwind),
        Some(UnwindSpec::NoUnwindWhen(e)) => {
            Some(UnwindSpec::NoUnwindWhen(map_expr_visitor_env(e, map, env, fe, fs, ft)?))
        }
    };
    let attrs = attrs.clone();
    let extra_dependencies = extra_dependencies.clone();
    let item_kind = *item_kind;
    let publish = *publish;
    let body = body.as_ref().map(|e| map_expr_visitor_env(e, map, env, fe, fs, ft)).transpose()?;
    map.pop_scope();

    let broadcast_forall = if let Some((params, req_ens)) = broadcast_forall {
        map.push_scope(true);
        let params = map_params_visitor(params, env, ft)?;
        for p in params.iter() {
            let _ = map.insert(p.x.name.clone(), ScopeEntry::new(&p.x.typ, p.x.is_mut, true));
        }
        let req_ens = map_expr_visitor_env(req_ens, map, env, fe, fs, ft)?;
        map.pop_scope();
        Some((params, req_ens))
    } else {
        None
    };

    let fndef_axioms = if let Some(es) = fndef_axioms {
        let mut es2 = vec![];
        for e in es.iter() {
            let e2 = map_expr_visitor_env(e, map, env, fe, fs, ft)?;
            es2.push(e2);
        }
        Some(Arc::new(es2))
    } else {
        None
    };

    let functionx = FunctionX {
        name,
        proxy,
        kind,
        visibility,
        owning_module,
        mode,
        fuel,
        typ_params: typ_params.clone(),
        typ_bounds,
        params,
        ret,
        require,
        ensure,
        decrease,
        decrease_when,
        decrease_by,
        broadcast_forall,
        fndef_axioms,
        mask_spec,
        unwind_spec,
        item_kind,
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
    let typ_bounds = map_generic_bounds_visitor(&datatypex.typ_bounds, env, ft)?;
    let mut variants: Vec<Variant> = Vec::new();
    for variant in datatypex.variants.iter() {
        let mut fields: Vec<Field> = Vec::new();
        for field in variant.fields.iter() {
            let (typ, mode, vis) = &field.a;
            let typ = map_typ_visitor_env(typ, env, ft)?;
            fields.push(field.new_a((typ, *mode, vis.clone())));
        }
        let variant = Variant { fields: Arc::new(fields), ..variant.clone() };
        variants.push(variant);
    }
    let variants = Arc::new(variants);
    Ok(Spanned::new(datatype.span.clone(), DatatypeX { variants, typ_bounds, ..datatypex }))
}

pub(crate) fn map_trait_impl_visitor_env<E, FT>(
    imp: &TraitImpl,
    env: &mut E,
    ft: &FT,
) -> Result<TraitImpl, VirErr>
where
    FT: Fn(&mut E, &Typ) -> Result<Typ, VirErr>,
{
    let TraitImplX {
        impl_path,
        typ_params,
        typ_bounds,
        trait_path,
        trait_typ_args,
        trait_typ_arg_impls,
        owning_module,
        auto_imported,
    } = &imp.x;
    let impx = TraitImplX {
        impl_path: impl_path.clone(),
        typ_params: typ_params.clone(),
        typ_bounds: map_generic_bounds_visitor(typ_bounds, env, ft)?,
        trait_path: trait_path.clone(),
        trait_typ_args: map_typs_visitor_env(trait_typ_args, env, ft)?,
        trait_typ_arg_impls: trait_typ_arg_impls.clone(),
        owning_module: owning_module.clone(),
        auto_imported: *auto_imported,
    };
    Ok(Spanned::new(imp.span.clone(), impx))
}

pub(crate) fn map_assoc_type_impl_visitor_env<E, FT>(
    assoc: &AssocTypeImpl,
    env: &mut E,
    ft: &FT,
) -> Result<AssocTypeImpl, VirErr>
where
    FT: Fn(&mut E, &Typ) -> Result<Typ, VirErr>,
{
    let AssocTypeImplX {
        name,
        impl_path,
        typ_params,
        typ_bounds,
        trait_path,
        trait_typ_args,
        typ,
        impl_paths,
    } = &assoc.x;
    let typ = map_typ_visitor_env(typ, env, ft)?;
    let assocx = AssocTypeImplX {
        name: name.clone(),
        impl_path: impl_path.clone(),
        typ_params: typ_params.clone(),
        typ_bounds: map_generic_bounds_visitor(typ_bounds, env, ft)?,
        trait_path: trait_path.clone(),
        trait_typ_args: map_typs_visitor_env(trait_typ_args, env, ft)?,
        typ,
        impl_paths: impl_paths.clone(),
    };
    Ok(Spanned::new(assoc.span.clone(), assocx))
}
