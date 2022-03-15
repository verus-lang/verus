//! VIR-AST -> VIR-AST transformation to simplify away some complicated features

use crate::ast::{
    BinaryOp, Binder, CallTarget, Constant, Datatype, DatatypeTransparency, DatatypeX, Expr, ExprX,
    Field, Function, GenericBound, GenericBoundX, Ident, Krate, KrateX, Mode, Path, Pattern,
    PatternX, SpannedTyped, Stmt, StmtX, Typ, TypX, UnaryOp, UnaryOpr, VirErr, Visibility,
};
use crate::ast_util::{err_str, err_string};
use crate::context::GlobalCtx;
use crate::def::{prefix_tuple_field, prefix_tuple_param, prefix_tuple_variant, Spanned};
use crate::util::vec_map_result;
use air::ast::Span;
use air::ast_util::ident_binder;
use air::scope_map::ScopeMap;
use std::collections::HashMap;
use std::sync::Arc;

struct State {
    // Counter to generate temporary variables
    next_var: u64,
    // Name of a datatype to represent each tuple arity
    tuple_typs: HashMap<usize, Path>,
}

impl State {
    fn new() -> Self {
        State { next_var: 0, tuple_typs: HashMap::new() }
    }

    fn reset_for_function(&mut self) {
        self.next_var = 0;
    }

    fn next_temp(&mut self) -> Ident {
        self.next_var += 1;
        crate::def::prefix_simplify_temp_var(self.next_var)
    }

    fn tuple_type_name(&mut self, arity: usize) -> Path {
        if !self.tuple_typs.contains_key(&arity) {
            self.tuple_typs.insert(arity, crate::def::prefix_tuple_type(arity));
        }
        self.tuple_typs[&arity].clone()
    }
}

struct LocalCtxt {
    span: Span,
    typ_params: Vec<Ident>,
    bounds: HashMap<Ident, GenericBound>,
}

fn is_small_expr(expr: &Expr) -> bool {
    match &expr.x {
        ExprX::Const(_) | ExprX::Var(_) | ExprX::VarAt(..) => true,
        ExprX::Unary(UnaryOp::Not | UnaryOp::Clip(_), e) => is_small_expr(e),
        ExprX::UnaryOpr(UnaryOpr::Box(_) | UnaryOpr::Unbox(_), e) => is_small_expr(e),
        ExprX::Loc(_) => panic!("expr contains a location"),
        _ => false,
    }
}

fn temp_expr(state: &mut State, expr: &Expr) -> (Stmt, Expr) {
    // put expr into a temp variable to avoid duplicating it
    let temp = state.next_temp();
    let name = temp.clone();
    let patternx = PatternX::Var { name, mutable: false };
    let pattern = SpannedTyped::new(&expr.span, &expr.typ, patternx);
    let decl = StmtX::Decl { pattern, mode: Mode::Exec, init: Some(expr.clone()) };
    let temp_decl = Spanned::new(expr.span.clone(), decl);
    (temp_decl, SpannedTyped::new(&expr.span, &expr.typ, ExprX::Var(temp)))
}

struct SmallLocOrTemp(Vec<Stmt>, Expr, bool);

fn small_loc_or_temp_exprs(state: &mut State, es: &[Expr]) -> (Vec<Stmt>, Vec<Expr>, bool) {
    let mut stmts: Vec<Stmt> = Vec::new();
    let mut exprs: Vec<Expr> = Vec::new();
    let mut contains_loc = false;
    for e in es.iter() {
        let SmallLocOrTemp(ss, ee, cl) = small_loc_or_temp(state, e);
        stmts.extend(ss.into_iter());
        exprs.push(ee);
        contains_loc |= cl;
    }
    (stmts, exprs, contains_loc)
}

impl SmallLocOrTemp {
    fn map_expr(self, f: impl Fn(Expr) -> Expr) -> SmallLocOrTemp {
        let SmallLocOrTemp(ss, ee, cl) = self;
        SmallLocOrTemp(ss, f(ee), cl)
    }

    fn to_opt(self) -> Option<(Vec<Stmt>, Expr)> {
        let SmallLocOrTemp(ss, ee, cl) = self;
        cl.then(|| (ss, ee))
    }
}

fn small_or_temp(state: &mut State, expr: &Expr) -> (Vec<Stmt>, Expr) {
    let SmallLocOrTemp(stmts, expr, _) = small_loc_or_temp(state, expr);
    (stmts, expr)
}

/// Returns (statements for temp expressions, simplified expr, contains location)
fn small_loc_or_temp(state: &mut State, expr: &Expr) -> SmallLocOrTemp {
    let contains_loc = match &expr.x {
        ExprX::Const(..) => None,
        ExprX::ConstVar(..) => None,
        ExprX::Var(..) => None,
        ExprX::VarLoc(..) => Some((vec![], expr.clone())),
        ExprX::VarAt(..) => None,
        ExprX::Loc(e) => {
            let SmallLocOrTemp(stmts, ee, _contains_loc) = small_loc_or_temp(state, e);
            Some((stmts, expr.new_x(ExprX::Loc(ee))))
        }
        ExprX::Call(target, es) => {
            let (stmts, exprs, contains_loc) = small_loc_or_temp_exprs(state, es);
            contains_loc.then(|| (stmts, expr.new_x(ExprX::Call(target.clone(), Arc::new(exprs)))))
        }
        ExprX::Tuple(es) => {
            let (stmts, exprs, contains_loc) = small_loc_or_temp_exprs(state, es);
            contains_loc.then(|| (stmts, expr.new_x(ExprX::Tuple(Arc::new(exprs)))))
        }
        ExprX::Ctor(path, ident, binders, update) => {
            let (mut stmts, update, mut contains_loc) = match update {
                None => (vec![], None, false),
                Some(update) => {
                    let SmallLocOrTemp(s, u, c) = small_loc_or_temp(state, update);
                    (s, Some(u), c)
                }
            };
            let mut mapped_binders = Vec::new();
            for b in binders.iter() {
                let SmallLocOrTemp(ss, ee, cl) = small_loc_or_temp(state, &b.a);
                stmts.extend(ss.into_iter());
                mapped_binders.push(b.new_a(ee));
                contains_loc |= cl;
            }
            contains_loc.then(|| {
                (
                    stmts,
                    expr.new_x(ExprX::Ctor(
                        path.clone(),
                        ident.clone(),
                        Arc::new(mapped_binders),
                        update,
                    )),
                )
            })
        }
        ExprX::Unary(op, e1) => {
            small_loc_or_temp(state, e1).map_expr(|e| expr.new_x(ExprX::Unary(*op, e))).to_opt()
        }
        ExprX::UnaryOpr(op, e1) => small_loc_or_temp(state, e1)
            .map_expr(|e| expr.new_x(ExprX::UnaryOpr(op.clone(), e)))
            .to_opt(),
        ExprX::Binary(op, e1, e2) => {
            let (stmts, exprs, contains_loc) =
                small_loc_or_temp_exprs(state, &[e1.clone(), e2.clone()]);
            let mut exprs = exprs.into_iter();
            let expr1 = exprs.next().unwrap();
            let expr2 = exprs.next().unwrap();
            contains_loc.then(|| (stmts, expr.new_x(ExprX::Binary(*op, expr1, expr2))))
        }
        ExprX::Quant(..) => None,
        ExprX::Closure(params, body) => small_loc_or_temp(state, body)
            .map_expr(|b| expr.new_x(ExprX::Closure(params.clone(), b)))
            .to_opt(),
        ExprX::Choose { .. } => None,
        ExprX::Assign(e1, e2) => {
            let (stmts, exprs, contains_loc) =
                small_loc_or_temp_exprs(state, &[e1.clone(), e2.clone()]);
            let mut exprs = exprs.into_iter();
            let expr1 = exprs.next().unwrap();
            let expr2 = exprs.next().unwrap();
            contains_loc.then(|| (stmts, expr.new_x(ExprX::Assign(expr1, expr2))))
        }
        ExprX::Fuel(..) => None,
        ExprX::Admit => None,
        ExprX::If(e1, e2, e3) => {
            let mut es = vec![e1.clone(), e2.clone()];
            if let Some(e3) = e3.as_ref() {
                es.push(e3.clone());
            }
            let (stmts, exprs, contains_loc) = small_loc_or_temp_exprs(state, &es);
            let mut exprs = exprs.into_iter();
            let expr1 = exprs.next().unwrap();
            let expr2 = exprs.next().unwrap();
            let expr3 = exprs.next();
            contains_loc.then(|| (stmts, expr.new_x(ExprX::If(expr1, expr2, expr3))))
        }
        ExprX::Forall { .. }
        | ExprX::AssertBV(..)
        | ExprX::Header(_)
        | ExprX::Match(..)
        | ExprX::While { .. }
        | ExprX::Return(..)
        | ExprX::Block(..)
        | ExprX::OpenInvariant(..) => {
            panic!("{:?} expression not expected here", &expr.x);
        }
    };
    if let Some((stmts, simplified_expr)) = contains_loc {
        SmallLocOrTemp(stmts, simplified_expr, true)
    } else {
        if is_small_expr(&expr) {
            SmallLocOrTemp(vec![], expr.clone(), false)
        } else {
            let (ts, te) = temp_expr(state, expr);
            SmallLocOrTemp(vec![ts], te, false)
        }
    }
}

fn keep_bound(bound: &GenericBound) -> bool {
    // Remove FnSpec type bounds
    match &**bound {
        GenericBoundX::Traits(_) => true,
        GenericBoundX::FnSpec(..) => false,
    }
}

fn pattern_field_expr(span: &Span, expr: &Expr, pat_typ: &Typ, field_op: UnaryOpr) -> Expr {
    let field = ExprX::UnaryOpr(field_op, expr.clone());
    SpannedTyped::new(span, pat_typ, field)
}

// Compute:
// - expression that tests whether exp matches pattern
// - bindings of pattern variables to fields of exp
fn pattern_to_exprs(
    ctx: &GlobalCtx,
    state: &mut State,
    expr: &Expr,
    pattern: &Pattern,
    decls: &mut Vec<Stmt>,
) -> Result<Expr, VirErr> {
    let t_bool = Arc::new(TypX::Bool);
    match &pattern.x {
        PatternX::Wildcard => {
            Ok(SpannedTyped::new(&pattern.span, &t_bool, ExprX::Const(Constant::Bool(true))))
        }
        PatternX::Var { name: x, mutable } => {
            let patternx = PatternX::Var { name: x.clone(), mutable: *mutable };
            let pattern = SpannedTyped::new(&expr.span, &expr.typ, patternx);
            let decl = StmtX::Decl { pattern, mode: Mode::Exec, init: Some(expr.clone()) };
            decls.push(Spanned::new(expr.span.clone(), decl));
            Ok(SpannedTyped::new(&expr.span, &t_bool, ExprX::Const(Constant::Bool(true))))
        }
        PatternX::Tuple(patterns) => {
            let arity = patterns.len();
            let path = state.tuple_type_name(arity);
            let variant = prefix_tuple_variant(arity);
            let mut test =
                SpannedTyped::new(&pattern.span, &t_bool, ExprX::Const(Constant::Bool(true)));
            for (i, pat) in patterns.iter().enumerate() {
                let field_op = UnaryOpr::Field {
                    datatype: path.clone(),
                    variant: variant.clone(),
                    field: prefix_tuple_field(i),
                };
                let field_exp = pattern_field_expr(&pattern.span, expr, &pat.typ, field_op);
                let pattern_test = pattern_to_exprs(ctx, state, &field_exp, pat, decls)?;
                let and = ExprX::Binary(BinaryOp::And, test, pattern_test);
                test = SpannedTyped::new(&pattern.span, &t_bool, and);
            }
            Ok(test)
        }
        PatternX::Constructor(path, variant, patterns) => {
            let is_variant_opr =
                UnaryOpr::IsVariant { datatype: path.clone(), variant: variant.clone() };
            let test_variant = ExprX::UnaryOpr(is_variant_opr, expr.clone());
            let mut test = SpannedTyped::new(&pattern.span, &t_bool, test_variant);
            for binder in patterns.iter() {
                let field_op = UnaryOpr::Field {
                    datatype: path.clone(),
                    variant: variant.clone(),
                    field: binder.name.clone(),
                };
                let field_exp = pattern_field_expr(&pattern.span, expr, &binder.a.typ, field_op);
                let pattern_test = pattern_to_exprs(ctx, state, &field_exp, &binder.a, decls)?;
                let and = ExprX::Binary(BinaryOp::And, test, pattern_test);
                test = SpannedTyped::new(&pattern.span, &t_bool, and);
            }
            Ok(test)
        }
    }
}

fn simplify_one_expr(ctx: &GlobalCtx, state: &mut State, expr: &Expr) -> Result<Expr, VirErr> {
    match &expr.x {
        ExprX::ConstVar(x) => {
            let call =
                ExprX::Call(CallTarget::Static(x.clone(), Arc::new(vec![])), Arc::new(vec![]));
            Ok(SpannedTyped::new(&expr.span, &expr.typ, call))
        }
        ExprX::Call(CallTarget::Static(tgt, typs), args) => {
            // Remove FnSpec type arguments
            let bounds = &ctx.fun_bounds[tgt];
            let typs: Vec<Typ> = typs
                .iter()
                .zip(bounds.iter())
                .filter(|(_, bound)| keep_bound(bound))
                .map(|(t, _)| t.clone())
                .collect();
            let call = ExprX::Call(CallTarget::Static(tgt.clone(), Arc::new(typs)), args.clone());
            Ok(SpannedTyped::new(&expr.span, &expr.typ, call))
        }
        ExprX::Tuple(args) => {
            let arity = args.len();
            let datatype = state.tuple_type_name(arity);
            let variant = prefix_tuple_variant(arity);
            let mut binders: Vec<Binder<Expr>> = Vec::new();
            for (i, arg) in args.iter().enumerate() {
                let field = prefix_tuple_field(i);
                binders.push(ident_binder(&field, &arg));
            }
            let binders = Arc::new(binders);
            let exprx = ExprX::Ctor(datatype, variant, binders, None);
            Ok(SpannedTyped::new(&expr.span, &expr.typ, exprx))
        }
        ExprX::Ctor(path, variant, partial_binders, Some(update)) => {
            let (temp_decl, update) = small_or_temp(state, update);
            let mut decls: Vec<Stmt> = Vec::new();
            let mut binders: Vec<Binder<Expr>> = Vec::new();
            if temp_decl.len() == 0 {
                for binder in partial_binders.iter() {
                    binders.push(binder.clone());
                }
            } else {
                // Because of Rust's order of evaluation here,
                // we have to put binders in temp vars, too.
                for binder in partial_binders.iter() {
                    let (temp_decl_inner, e) = small_or_temp(state, &binder.a);
                    decls.extend(temp_decl_inner.into_iter());
                    binders.push(binder.map_a(|_| e));
                }
                decls.extend(temp_decl.into_iter());
            }
            let datatype = &ctx.datatypes[path];
            assert_eq!(datatype.len(), 1);
            let fields = &datatype[0].a;
            // replace ..update
            // with f1: update.f1, f2: update.f2, ...
            for field in fields.iter() {
                if binders.iter().find(|b| b.name == field.name).is_none() {
                    let op = UnaryOpr::Field {
                        datatype: path.clone(),
                        variant: variant.clone(),
                        field: field.name.clone(),
                    };
                    let exprx = ExprX::UnaryOpr(op, update.clone());
                    let field_exp = SpannedTyped::new(&expr.span, &field.a.0, exprx);
                    binders.push(ident_binder(&field.name, &field_exp));
                }
            }
            let ctorx = ExprX::Ctor(path.clone(), variant.clone(), Arc::new(binders), None);
            let ctor = SpannedTyped::new(&expr.span, &expr.typ, ctorx);
            if decls.len() == 0 {
                Ok(ctor)
            } else {
                let block = ExprX::Block(Arc::new(decls), Some(ctor));
                Ok(SpannedTyped::new(&expr.span, &expr.typ, block))
            }
        }
        ExprX::UnaryOpr(UnaryOpr::TupleField { tuple_arity, field }, expr0) => {
            let datatype = state.tuple_type_name(*tuple_arity);
            let variant = prefix_tuple_variant(*tuple_arity);
            let field = prefix_tuple_field(*field);
            let op = UnaryOpr::Field { datatype, variant, field };
            let field_exp =
                SpannedTyped::new(&expr.span, &expr.typ, ExprX::UnaryOpr(op, expr0.clone()));
            Ok(field_exp)
        }
        ExprX::Match(expr0, arms1) => {
            let (temp_decl, expr0) = small_or_temp(state, &expr0);
            // Translate into If expression
            let t_bool = Arc::new(TypX::Bool);
            let mut if_expr: Option<Expr> = None;
            for arm in arms1.iter().rev() {
                let mut decls: Vec<Stmt> = Vec::new();
                let test_pattern =
                    pattern_to_exprs(ctx, state, &expr0, &arm.x.pattern, &mut decls)?;
                let test = match &arm.x.guard.x {
                    ExprX::Const(Constant::Bool(true)) => test_pattern,
                    _ => {
                        let guard = arm.x.guard.clone();
                        let test_exp = ExprX::Binary(BinaryOp::And, test_pattern, guard);
                        let test = SpannedTyped::new(&arm.x.pattern.span, &t_bool, test_exp);
                        let block = ExprX::Block(Arc::new(decls.clone()), Some(test));
                        SpannedTyped::new(&arm.x.pattern.span, &t_bool, block)
                    }
                };
                let block = ExprX::Block(Arc::new(decls), Some(arm.x.body.clone()));
                let body = SpannedTyped::new(&arm.x.pattern.span, &t_bool, block);
                if let Some(prev) = if_expr {
                    // if pattern && guard then body else prev
                    let ifx = ExprX::If(test.clone(), body, Some(prev));
                    if_expr = Some(SpannedTyped::new(&test.span, &expr.typ.clone(), ifx));
                } else {
                    // last arm is unconditional
                    if_expr = Some(body);
                }
            }
            if let Some(if_expr) = if_expr {
                let if_expr = if temp_decl.len() != 0 {
                    let block = ExprX::Block(Arc::new(temp_decl), Some(if_expr));
                    SpannedTyped::new(&expr.span, &expr.typ, block)
                } else {
                    if_expr
                };
                Ok(if_expr)
            } else {
                err_str(&expr.span, "not yet implemented: zero-arm match expressions")
            }
        }
        _ => Ok(expr.clone()),
    }
}

fn simplify_one_stmt(ctx: &GlobalCtx, state: &mut State, stmt: &Stmt) -> Result<Vec<Stmt>, VirErr> {
    match &stmt.x {
        StmtX::Decl { pattern, mode: _, init: None } => match &pattern.x {
            PatternX::Var { .. } => Ok(vec![stmt.clone()]),
            _ => err_str(&stmt.span, "let-pattern declaration must have an initializer"),
        },
        StmtX::Decl { pattern, mode: _, init: Some(init) }
            if !matches!(pattern.x, PatternX::Var { .. }) =>
        {
            let mut decls: Vec<Stmt> = Vec::new();
            let (temp_decl, init) = small_or_temp(state, init);
            decls.extend(temp_decl.into_iter());
            let _ = pattern_to_exprs(ctx, state, &init, &pattern, &mut decls)?;
            Ok(decls)
        }
        _ => Ok(vec![stmt.clone()]),
    }
}

fn simplify_one_typ(local: &LocalCtxt, state: &mut State, typ: &Typ) -> Result<Typ, VirErr> {
    match &**typ {
        TypX::Tuple(typs) => {
            let path = state.tuple_type_name(typs.len());
            Ok(Arc::new(TypX::Datatype(path, typs.clone())))
        }
        TypX::TypParam(x) => {
            if !local.bounds.contains_key(x) {
                return err_string(
                    &local.span,
                    format!("type parameter {} used before being declared", x),
                );
            }
            match &*local.bounds[x] {
                GenericBoundX::Traits(_) => Ok(typ.clone()),
                GenericBoundX::FnSpec(ts, tr) => Ok(Arc::new(TypX::Lambda(ts.clone(), tr.clone()))),
            }
        }
        _ => Ok(typ.clone()),
    }
}

fn simplify_function(
    ctx: &GlobalCtx,
    state: &mut State,
    function: &Function,
) -> Result<Function, VirErr> {
    state.reset_for_function();
    let mut functionx = function.x.clone();
    let mut local =
        LocalCtxt { span: function.span.clone(), typ_params: Vec::new(), bounds: HashMap::new() };
    for (x, bound) in functionx.typ_bounds.iter() {
        match &**bound {
            GenericBoundX::Traits(_) => local.typ_params.push(x.clone()),
            GenericBoundX::FnSpec(..) => {}
        }
        // simplify types in bounds and disallow recursive bounds like F: FnSpec(F, F) -> F
        let bound = crate::ast_visitor::map_generic_bound_visitor(bound, state, &|state, typ| {
            simplify_one_typ(&local, state, typ)
        })?;
        local.bounds.insert(x.clone(), bound.clone());
    }

    // remove FnSpec from typ_params
    functionx.typ_bounds = Arc::new(
        functionx
            .typ_bounds
            .iter()
            .filter(|(_, bound)| keep_bound(bound))
            .map(|x| x.clone())
            .collect(),
    );

    let function = Spanned::new(function.span.clone(), functionx);
    let mut map: ScopeMap<Ident, Typ> = ScopeMap::new();
    crate::ast_visitor::map_function_visitor_env(
        &function,
        &mut map,
        state,
        &|state, _, expr| simplify_one_expr(ctx, state, expr),
        &|state, _, stmt| simplify_one_stmt(ctx, state, stmt),
        &|state, typ| simplify_one_typ(&local, state, typ),
    )
}

fn simplify_datatype(state: &mut State, datatype: &Datatype) -> Result<Datatype, VirErr> {
    let mut local =
        LocalCtxt { span: datatype.span.clone(), typ_params: Vec::new(), bounds: HashMap::new() };
    for (x, bound, _strict_pos) in datatype.x.typ_params.iter() {
        local.typ_params.push(x.clone());
        local.bounds.insert(x.clone(), bound.clone());
    }
    crate::ast_visitor::map_datatype_visitor_env(datatype, state, &|state, typ| {
        simplify_one_typ(&local, state, typ)
    })
}

/*
fn mk_fun_decl(
    span: &Span,
    path: &Path,
    typ_params: &Idents,
    params: &Params,
    ret: &Param,
) -> Function {
    let mut attrs: crate::ast::FunctionAttrsX = Default::default();
    attrs.no_auto_trigger = true;
    Spanned::new(
        span.clone(),
        FunctionX {
            name: Arc::new(FunX { path: path.clone(), trait_path: None }),
            visibility: Visibility { owning_module: None, is_private: false },
            mode: Mode::Spec,
            fuel: 0,
            typ_bounds: Arc::new(vec_map(typ_params, |x| {
                (x.clone(), Arc::new(GenericBoundX::None))
            })),
            params: params.clone(),
            ret: ret.clone(),
            require: Arc::new(vec![]),
            ensure: Arc::new(vec![]),
            decrease: None,
            is_const: false,
            is_abstract: false,
            attrs: Arc::new(attrs),
            body: None,
        },
    )
}
*/

pub fn simplify_krate(ctx: &mut GlobalCtx, krate: &Krate) -> Result<Krate, VirErr> {
    let KrateX { functions, datatypes, traits, module_ids } = &**krate;
    let mut state = State::new();
    let functions = vec_map_result(functions, |f| simplify_function(ctx, &mut state, f))?;
    let mut datatypes = vec_map_result(&datatypes, |d| simplify_datatype(&mut state, d))?;

    // Add a generic datatype to represent each tuple arity
    for (arity, path) in state.tuple_typs {
        let visibility = Visibility { owning_module: None, is_private: false };
        let transparency = DatatypeTransparency::Always;
        let bound = Arc::new(GenericBoundX::Traits(vec![]));
        let typ_params =
            Arc::new((0..arity).map(|i| (prefix_tuple_param(i), bound.clone(), true)).collect());
        let mut fields: Vec<Field> = Vec::new();
        for i in 0..arity {
            let typ = Arc::new(TypX::TypParam(prefix_tuple_param(i)));
            let vis = Visibility { owning_module: None, is_private: false };
            // Note: the mode is irrelevant at this stage, so we arbitrarily use Mode::Exec
            fields.push(ident_binder(&prefix_tuple_field(i), &(typ, Mode::Exec, vis)));
        }
        let variant = ident_binder(&prefix_tuple_variant(arity), &Arc::new(fields));
        let variants = Arc::new(vec![variant]);
        let datatypex = DatatypeX {
            path,
            visibility,
            transparency,
            typ_params,
            variants,
            mode: Mode::Exec,
            unforgeable: false,
        };
        datatypes.push(Spanned::new(ctx.no_span.clone(), datatypex));
    }

    let traits = traits.clone();
    let module_ids = module_ids.clone();
    let krate = Arc::new(KrateX { functions, datatypes, traits, module_ids });
    *ctx = crate::context::GlobalCtx::new(&krate, ctx.no_span.clone())?;
    Ok(krate)
}
