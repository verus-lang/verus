//! VIR-AST -> VIR-AST transformation to simplify away some complicated features

use crate::ast::{
    BinaryOp, Binder, Binders, CallTarget, Constant, Datatype, DatatypeTransparency, DatatypeX,
    Expr, ExprX, Field, Function, FunctionX, GenericBound, GenericBoundX, Ident, Idents, Krate,
    KrateX, Mode, Param, ParamX, Params, Path, Pattern, PatternX, SpannedTyped, Stmt, StmtX, Typ,
    TypX, UnaryOp, UnaryOpr, VirErr, Visibility,
};
use crate::ast_util::{err_str, err_string, fnspec_type};
use crate::context::GlobalCtx;
use crate::def::{
    prefix_fnspec_param, prefix_fnspec_tparam, prefix_tuple_field, prefix_tuple_param,
    prefix_tuple_variant, Spanned,
};
use crate::util::{vec_map, vec_map_result};
use air::ast::{Quant, Span};
use air::ast_util::ident_binder;
use std::collections::HashMap;
use std::sync::Arc;

struct State {
    // Counter to generate temporary variables
    next_var: u64,
    // Counter to generate closure names
    next_closure: u64,
    // Name of a datatype to represent each tuple arity
    tuple_typs: HashMap<usize, Path>,
    // Name of an apply function for each function arity
    fnspec_applies: HashMap<usize, Path>,
    // Each closure's generated name and captured variables
    closures: Vec<(Path, Binders<Typ>)>,
}

impl State {
    fn new() -> Self {
        State {
            next_var: 0,
            next_closure: 0,
            tuple_typs: HashMap::new(),
            fnspec_applies: HashMap::new(),
            closures: Vec::new(),
        }
    }

    fn reset_for_function(&mut self) {
        self.next_var = 0;
    }

    fn next_temp(&mut self) -> Ident {
        self.next_var += 1;
        crate::def::prefix_simplify_temp_var(self.next_var)
    }

    fn next_closure(&mut self) -> Path {
        self.next_closure += 1;
        crate::def::prefix_closure(self.next_closure)
    }

    fn tuple_type_name(&mut self, arity: usize) -> Path {
        if !self.tuple_typs.contains_key(&arity) {
            self.tuple_typs.insert(arity, crate::def::prefix_tuple_type(arity));
        }
        self.tuple_typs[&arity].clone()
    }

    fn fnspec_apply_name(&mut self, arity: usize) -> Path {
        if !self.fnspec_applies.contains_key(&arity) {
            self.fnspec_applies.insert(arity, crate::def::prefix_fnspec_apply_name(arity));
        }
        self.fnspec_applies[&arity].clone()
    }
}

struct LocalCtxt {
    span: Span,
    bounds: HashMap<Ident, GenericBound>,
}

fn is_small_expr(expr: &Expr) -> bool {
    match &expr.x {
        ExprX::Const(_) => true,
        ExprX::Var(_) => true,
        ExprX::Unary(UnaryOp::Not | UnaryOp::Clip(_), e) => is_small_expr(e),
        ExprX::UnaryOpr(UnaryOpr::Box(_) | UnaryOpr::Unbox(_), e) => is_small_expr(e),
        _ => false,
    }
}

fn small_or_temp(state: &mut State, expr: &Expr) -> (Option<Stmt>, Expr) {
    if is_small_expr(&expr) {
        (None, expr.clone())
    } else {
        // put expr into a temp variable to avoid duplicating it
        let temp = state.next_temp();
        let name = temp.clone();
        let patternx = PatternX::Var { name, mutable: false };
        let pattern = SpannedTyped::new(&expr.span, &expr.typ, patternx);
        let decl = StmtX::Decl { pattern, mode: Mode::Exec, init: Some(expr.clone()) };
        let temp_decl = Some(Spanned::new(expr.span.clone(), decl));
        (temp_decl, SpannedTyped::new(&expr.span, &expr.typ, ExprX::Var(temp)))
    }
}

fn is_removed(bound: &GenericBound) -> bool {
    // Remove FnSpec type bounds
    match &**bound {
        GenericBoundX::None => true,
        GenericBoundX::FnSpec(..) => false,
    }
}

fn datatype_field_typ(ctx: &GlobalCtx, path: &Path, variant: &Ident, field: &Ident) -> Typ {
    let fields =
        &ctx.datatypes[path].iter().find(|v| v.name == *variant).expect("couldn't find variant").a;
    let (typ, _) = &fields.iter().find(|f| f.name == *field).expect("couldn't find field").a;
    typ.clone()
}

fn pattern_field_expr(
    span: &Span,
    expr: &Expr,
    field_typ: Typ,
    pat_typ: &Typ,
    field_op: UnaryOpr,
) -> Expr {
    let field = ExprX::UnaryOpr(field_op, expr.clone());
    let field_exp = SpannedTyped::new(span, &field_typ, field);
    match (&*field_typ, &**pat_typ) {
        (TypX::TypParam(_), TypX::TypParam(_)) => field_exp,
        (TypX::TypParam(_), TypX::Boxed(_)) => field_exp,
        (TypX::TypParam(_), _) => {
            let op = UnaryOpr::Unbox(pat_typ.clone());
            let unbox = ExprX::UnaryOpr(op, field_exp);
            SpannedTyped::new(span, &pat_typ, unbox)
        }
        _ => field_exp,
    }
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
                let field_typ = Arc::new(TypX::TypParam(prefix_tuple_param(i)));
                let field_exp =
                    pattern_field_expr(&pattern.span, expr, field_typ, &pat.typ, field_op);
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
                let field_typ = datatype_field_typ(ctx, path, variant, &binder.name);
                let field_exp =
                    pattern_field_expr(&pattern.span, expr, field_typ, &binder.a.typ, field_op);
                let pattern_test = pattern_to_exprs(ctx, state, &field_exp, &binder.a, decls)?;
                let and = ExprX::Binary(BinaryOp::And, test, pattern_test);
                test = SpannedTyped::new(&pattern.span, &t_bool, and);
            }
            Ok(test)
        }
    }
}

fn simplify_one_expr(
    ctx: &GlobalCtx,
    local: &LocalCtxt,
    state: &mut State,
    expr: &Expr,
) -> Result<Expr, VirErr> {
    match &expr.x {
        ExprX::Call(CallTarget::FnSpec { typ_param, fun }, args) => {
            // target(args) --> apply(target, args)
            let path = state.fnspec_apply_name(args.len());
            let mut typ_args: Vec<Typ> = Vec::new();
            let (tparams, tret) = match &*local.bounds[typ_param] {
                GenericBoundX::FnSpec(tparams, tret) => (tparams.clone(), tret.clone()),
                _ => panic!("expected function type"),
            };
            typ_args.push(tret);
            for t in tparams.iter() {
                typ_args.push(t.clone());
            }
            let mut expr_args = vec![fun.clone()];
            for arg in args.iter() {
                expr_args.push(arg.clone());
            }
            let call = ExprX::Call(CallTarget::Path(path, Arc::new(typ_args)), Arc::new(expr_args));
            Ok(SpannedTyped::new(&expr.span, &expr.typ, call))
        }
        ExprX::Call(CallTarget::Path(path, typs), args) => {
            // Remove FnSpec type arguments
            let bounds = &ctx.fun_bounds[path];
            let typs: Vec<Typ> = typs
                .iter()
                .zip(bounds.iter())
                .filter(|(_, bound)| is_removed(bound))
                .map(|(t, _)| t.clone())
                .collect();
            let call = ExprX::Call(CallTarget::Path(path.clone(), Arc::new(typs)), args.clone());
            Ok(SpannedTyped::new(&expr.span, &expr.typ, call))
        }
        ExprX::Tuple(args) => {
            let arity = args.len();
            let datatype = state.tuple_type_name(arity);
            let variant = prefix_tuple_variant(arity);
            let mut binders: Vec<Binder<Expr>> = Vec::new();
            for (i, arg) in args.iter().enumerate() {
                let exp = match &*arg.typ {
                    TypX::TypParam(_) => arg.clone(),
                    TypX::Boxed(_) => arg.clone(),
                    _ => {
                        let op = UnaryOpr::Box(arg.typ.clone());
                        let box_arg = ExprX::UnaryOpr(op, arg.clone());
                        SpannedTyped::new(&arg.span, &arg.typ, box_arg)
                    }
                };
                let field = prefix_tuple_field(i);
                binders.push(ident_binder(&field, &exp));
            }
            let binders = Arc::new(binders);
            Ok(SpannedTyped::new(&expr.span, &expr.typ, ExprX::Ctor(datatype, variant, binders)))
        }
        ExprX::UnaryOpr(UnaryOpr::TupleField { tuple_arity, field }, expr0) => {
            let datatype = state.tuple_type_name(*tuple_arity);
            let variant = prefix_tuple_variant(*tuple_arity);
            let field = prefix_tuple_field(*field);
            let op = UnaryOpr::Field { datatype, variant, field };
            let field_exp =
                SpannedTyped::new(&expr.span, &expr.typ, ExprX::UnaryOpr(op, expr0.clone()));
            let exp = match &*expr.typ {
                TypX::TypParam(_) => field_exp,
                TypX::Boxed(_) => field_exp,
                _ => {
                    let op = UnaryOpr::Unbox(expr.typ.clone());
                    let unbox = ExprX::UnaryOpr(op, field_exp);
                    SpannedTyped::new(&expr.span, &expr.typ, unbox)
                }
            };
            Ok(exp)
        }
        ExprX::Closure { params, body, call, axiom } => {
            assert!(call.is_none());
            assert!(axiom.is_none());
            let path = state.next_closure();
            let tbool = Arc::new(TypX::Bool);
            let captures: Vec<Binder<Typ>> = Vec::new();
            let mut binders: Vec<Binder<Typ>> = Vec::new();
            for binder in captures.iter() {
                binders.push(binder.clone());
            }
            for binder in params.iter() {
                binders.push(binder.clone());
            }
            // TODO: compute captures

            // call: f(captures)
            let target = CallTarget::Path(path.clone(), Arc::new(vec![]));
            let args = vec_map(&captures, |p| {
                SpannedTyped::new(&expr.span, &p.a, ExprX::Var(p.name.clone()))
            });
            let callx = ExprX::Call(target, Arc::new(args));
            let call = SpannedTyped::new(&expr.span, &fnspec_type(), callx);

            // axiom: forall captures, params. apply(call, params) == body
            let apply = state.fnspec_apply_name(params.len());
            let mut targs: Vec<Typ> = Vec::new();
            let mut args: Vec<Expr> = Vec::new();
            targs.push(body.typ.clone());
            args.push(call.clone());
            for p in params.iter() {
                targs.push(p.a.clone());
                let arg = SpannedTyped::new(&expr.span, &p.a, ExprX::Var(p.name.clone()));
                let arg = match &*p.a {
                    TypX::TypParam(_) | TypX::Boxed(_) => arg,
                    _ => {
                        let argx = ExprX::UnaryOpr(UnaryOpr::Box(p.a.clone()), arg);
                        let typ = Arc::new(TypX::Boxed(p.a.clone()));
                        SpannedTyped::new(&expr.span, &typ, argx)
                    }
                };
                args.push(arg);
            }
            let target = CallTarget::Path(apply, Arc::new(targs));
            let appx = ExprX::Call(target, Arc::new(args));
            let appx = match &*body.typ {
                TypX::TypParam(_) | TypX::Boxed(_) => appx,
                _ => {
                    let typ = Arc::new(TypX::Boxed(body.typ.clone()));
                    let app = SpannedTyped::new(&expr.span, &typ, appx);
                    ExprX::UnaryOpr(UnaryOpr::Unbox(body.typ.clone()), app)
                }
            };
            let app = SpannedTyped::new(&expr.span, &body.typ, appx);
            let eqx = ExprX::Binary(BinaryOp::Eq(Mode::Spec), app, body.clone());
            let eq = SpannedTyped::new(&expr.span, &tbool, eqx);
            let axiomx = ExprX::Quant(Quant::Forall, Arc::new(binders), eq);
            let axiom = Some(SpannedTyped::new(&expr.span, &tbool, axiomx));

            state.closures.push((path, Arc::new(captures)));
            let call = Some(call);
            let exprx = ExprX::Closure { params: params.clone(), body: body.clone(), call, axiom };
            Ok(SpannedTyped::new(&expr.span, &expr.typ, exprx))
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
                let if_expr = if let Some(decl) = temp_decl {
                    let block = ExprX::Block(Arc::new(vec![decl]), Some(if_expr));
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
        StmtX::Decl { pattern, mode: _, init: Some(init) } => {
            let mut decls: Vec<Stmt> = Vec::new();
            let (temp_decl, init) = small_or_temp(state, init);
            if let Some(temp_decl) = temp_decl {
                decls.push(temp_decl);
            }
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
            let typs = vec_map(typs, |(t, _)| t.clone());
            Ok(Arc::new(TypX::Datatype(path, Arc::new(typs))))
        }
        TypX::TypParam(x) => {
            if !local.bounds.contains_key(x) {
                return err_string(
                    &local.span,
                    format!("type paramater {} used before being declared", x),
                );
            }
            match &*local.bounds[x] {
                GenericBoundX::None => Ok(typ.clone()),
                GenericBoundX::FnSpec(ts, _) => {
                    state.fnspec_apply_name(ts.len());
                    Ok(fnspec_type())
                }
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
    let mut local = LocalCtxt { span: function.span.clone(), bounds: HashMap::new() };
    for (x, bound) in functionx.typ_bounds.iter() {
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
            .filter(|(_, bound)| is_removed(bound))
            .map(|x| x.clone())
            .collect(),
    );

    let function = Spanned::new(function.span.clone(), functionx);
    crate::ast_visitor::map_function_visitor_env(
        &function,
        state,
        &|state, expr| simplify_one_expr(ctx, &local, state, expr),
        &|state, stmt| simplify_one_stmt(ctx, state, stmt),
        &|state, typ| simplify_one_typ(&local, state, typ),
    )
}

fn simplify_datatype(state: &mut State, datatype: &Datatype) -> Result<Datatype, VirErr> {
    let mut local = LocalCtxt { span: datatype.span.clone(), bounds: HashMap::new() };
    for x in datatype.x.typ_params.iter() {
        local.bounds.insert(x.clone(), Arc::new(GenericBoundX::None));
    }
    crate::ast_visitor::map_datatype_visitor_env(datatype, state, &|state, typ| {
        simplify_one_typ(&local, state, typ)
    })
}

fn mk_fun_decl(
    span: &Span,
    path: &Path,
    typ_params: &Idents,
    params: &Params,
    ret: &Param,
) -> Function {
    Spanned::new(
        span.clone(),
        FunctionX {
            path: path.clone(),
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
            custom_req_err: None,
            hidden: Arc::new(vec![]),
            is_abstract: false,
            body: None,
        },
    )
}

pub fn simplify_krate(ctx: &mut GlobalCtx, krate: &Krate) -> Result<Krate, VirErr> {
    let KrateX { functions, datatypes, module_ids } = &**krate;
    let mut state = State::new();
    let mut functions = vec_map_result(functions, |f| simplify_function(ctx, &mut state, f))?;
    let mut datatypes = vec_map_result(&datatypes, |d| simplify_datatype(&mut state, d))?;

    // Add a generic datatype to represent each tuple arity
    for (arity, path) in state.tuple_typs {
        let visibility = Visibility { owning_module: None, is_private: false };
        let transparency = DatatypeTransparency::Always;
        let typ_params = Arc::new((0..arity).map(|i| prefix_tuple_param(i)).collect());
        let mut fields: Vec<Field> = Vec::new();
        for i in 0..arity {
            let typ = Arc::new(TypX::TypParam(prefix_tuple_param(i)));
            // Note: the mode is irrelevant at this stage, so we arbitrarily use Mode::Exec
            fields.push(ident_binder(&prefix_tuple_field(i), &(typ, Mode::Exec)));
        }
        let variant = ident_binder(&prefix_tuple_variant(arity), &Arc::new(fields));
        let variants = Arc::new(vec![variant]);
        let datatypex = DatatypeX { path, visibility, transparency, typ_params, variants };
        datatypes.push(Spanned::new(ctx.no_span.clone(), datatypex));
    }

    // Add a single nongeneric, abstract datatype for all FnSpec types
    let path = crate::def::prefix_fnspec_type();
    let visibility = Visibility { owning_module: None, is_private: false };
    let transparency = DatatypeTransparency::Never;
    let typ_params = Arc::new(vec![]);
    let variants = Arc::new(vec![]);
    let datatypex = DatatypeX { path, visibility, transparency, typ_params, variants };
    datatypes.push(Spanned::new(ctx.no_span.clone(), datatypex));

    // Add a generic apply function for each function arity
    for (arity, path) in state.fnspec_applies {
        let mut param_typs: Vec<Typ> = Vec::new();
        for i in 0..arity + 1 {
            param_typs.push(Arc::new(TypX::TypParam(prefix_fnspec_tparam(i))));
        }
        param_typs.push(fnspec_type());
        let mut params: Vec<Param> = param_typs
            .iter()
            .enumerate()
            .map(|(i, typ)| {
                let param =
                    ParamX { name: prefix_fnspec_param(i), mode: Mode::Spec, typ: typ.clone() };
                Spanned::new(ctx.no_span.clone(), param)
            })
            .collect();
        let ret = params.remove(0);
        let f_param = params.remove(arity);
        params.insert(0, f_param);
        let typ_params = Arc::new((0..arity + 1).map(|i| prefix_fnspec_tparam(i)).collect());
        functions.push(mk_fun_decl(&ctx.no_span, &path, &typ_params, &Arc::new(params), &ret));
    }

    // Add a closure function declaration for each closure
    for (path, captures) in state.closures {
        let params: Vec<Param> = captures
            .iter()
            .map(|b| {
                let param = ParamX { name: b.name.clone(), mode: Mode::Spec, typ: b.a.clone() };
                Spanned::new(ctx.no_span.clone(), param)
            })
            .collect();
        let typ_params = Arc::new(vec![]);
        let retx = ParamX { name: prefix_fnspec_param(0), mode: Mode::Spec, typ: fnspec_type() };
        let ret = Spanned::new(ctx.no_span.clone(), retx);
        functions.push(mk_fun_decl(&ctx.no_span, &path, &typ_params, &Arc::new(params), &ret));
    }

    let module_ids = module_ids.clone();
    let krate = Arc::new(KrateX { functions, datatypes, module_ids });
    *ctx = crate::context::GlobalCtx::new(&krate, ctx.no_span.clone());
    Ok(krate)
}
