//! VIR-AST -> VIR-AST transformation to simplify away some complicated features

use crate::air_ast::BinderX;
use crate::air_ast::Binders;
use crate::ast::Quant;
use crate::ast::Typs;
use crate::ast::{
    AssocTypeImpl, AutospecUsage, BinaryOp, Binder, BuiltinSpecFun, CallTarget, ChainedOp,
    Constant, Datatype, DatatypeTransparency, DatatypeX, Expr, ExprX, Exprs, Field, FieldOpr,
    Function, FunctionKind, Ident, IntRange, Krate, KrateX, Mode, MultiOp, Path, Pattern, PatternX,
    SpannedTyped, Stmt, StmtX, TraitImpl, Typ, TypX, UnaryOp, UnaryOpr, VirErr, Visibility,
};
use crate::ast_util::int_range_from_type;
use crate::ast_util::is_integer_type;
use crate::ast_util::{conjoin, disjoin, if_then_else, wrap_in_trigger};
use crate::context::GlobalCtx;
use crate::def::{prefix_tuple_field, prefix_tuple_param, prefix_tuple_variant, Spanned};
use crate::messages::error;
use crate::messages::Span;
use crate::util::vec_map_result;
use air::ast_util::ident_binder;
use air::scope_map::ScopeMap;
use std::collections::HashMap;
use std::sync::Arc;

struct State {
    // Counter to generate temporary variables
    next_var: u64,
    // Name of a datatype to represent each tuple arity
    tuple_typs: HashMap<usize, Path>,
    // Name of a datatype to represent each tuple arity
    closure_typs: HashMap<usize, Path>,
}

impl State {
    fn new() -> Self {
        State { next_var: 0, tuple_typs: HashMap::new(), closure_typs: HashMap::new() }
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

    fn closure_type_name(&mut self, id: usize) -> Path {
        if !self.closure_typs.contains_key(&id) {
            self.closure_typs.insert(id, crate::def::prefix_closure_type(id));
        }
        self.closure_typs[&id].clone()
    }
}

struct LocalCtxt {
    span: Span,
    typ_params: Vec<Ident>,
}

fn is_small_expr(expr: &Expr) -> bool {
    match &expr.x {
        ExprX::Const(_) | ExprX::Var(_) | ExprX::VarAt(..) => true,
        ExprX::Unary(UnaryOp::Not | UnaryOp::Clip { .. }, e) => is_small_expr(e),
        ExprX::UnaryOpr(UnaryOpr::Box(_) | UnaryOpr::Unbox(_), e) => is_small_expr(e),
        ExprX::Loc(_) => panic!("expr is a location"),
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

fn small_or_temp(state: &mut State, expr: &Expr) -> (Vec<Stmt>, Expr) {
    if is_small_expr(&expr) {
        (vec![], expr.clone())
    } else {
        let (ts, te) = temp_expr(state, expr);
        (vec![ts], te)
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
    let mut pattern_bound_decls = vec![];
    let e = pattern_to_exprs_rec(ctx, state, expr, pattern, &mut pattern_bound_decls)?;

    for pbd in pattern_bound_decls {
        let PatternBoundDecl { name, mutable, expr } = pbd;
        let patternx = PatternX::Var { name, mutable };
        let pattern = SpannedTyped::new(&expr.span, &expr.typ, patternx);
        // Mode doesn't matter at this stage; arbitrarily set it to 'exec'
        let decl = StmtX::Decl { pattern, mode: Mode::Exec, init: Some(expr.clone()) };
        decls.push(Spanned::new(expr.span.clone(), decl));
    }

    Ok(e)
}

struct PatternBoundDecl {
    name: Ident,
    mutable: bool,
    expr: Expr,
}

fn pattern_to_exprs_rec(
    ctx: &GlobalCtx,
    state: &mut State,
    expr: &Expr,
    pattern: &Pattern,
    decls: &mut Vec<PatternBoundDecl>,
) -> Result<Expr, VirErr> {
    let t_bool = Arc::new(TypX::Bool);
    match &pattern.x {
        PatternX::Wildcard(_) => {
            Ok(SpannedTyped::new(&pattern.span, &t_bool, ExprX::Const(Constant::Bool(true))))
        }
        PatternX::Var { name: x, mutable } => {
            decls.push(PatternBoundDecl { name: x.clone(), mutable: *mutable, expr: expr.clone() });
            Ok(SpannedTyped::new(&expr.span, &t_bool, ExprX::Const(Constant::Bool(true))))
        }
        PatternX::Tuple(patterns) => {
            let arity = patterns.len();
            let path = state.tuple_type_name(arity);
            let variant = prefix_tuple_variant(arity);
            let mut test =
                SpannedTyped::new(&pattern.span, &t_bool, ExprX::Const(Constant::Bool(true)));
            for (i, pat) in patterns.iter().enumerate() {
                let field_op = UnaryOpr::Field(FieldOpr {
                    datatype: path.clone(),
                    variant: variant.clone(),
                    field: prefix_tuple_field(i),
                    get_variant: false,
                });
                let field_exp = pattern_field_expr(&pattern.span, expr, &pat.typ, field_op);
                let pattern_test = pattern_to_exprs_rec(ctx, state, &field_exp, pat, decls)?;
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
                let field_op = UnaryOpr::Field(FieldOpr {
                    datatype: path.clone(),
                    variant: variant.clone(),
                    field: binder.name.clone(),
                    get_variant: false,
                });
                let field_exp = pattern_field_expr(&pattern.span, expr, &binder.a.typ, field_op);
                let pattern_test = pattern_to_exprs_rec(ctx, state, &field_exp, &binder.a, decls)?;
                let and = ExprX::Binary(BinaryOp::And, test, pattern_test);
                test = SpannedTyped::new(&pattern.span, &t_bool, and);
            }
            Ok(test)
        }
        PatternX::Or(pat1, pat2) => {
            let mut decls1 = vec![];
            let mut decls2 = vec![];

            let pat1_matches = pattern_to_exprs_rec(ctx, state, expr, pat1, &mut decls1)?;
            let pat2_matches = pattern_to_exprs_rec(ctx, state, expr, pat2, &mut decls2)?;

            let matches = disjoin(&pattern.span, &vec![pat1_matches.clone(), pat2_matches]);

            assert!(decls1.len() == decls2.len());
            for d1 in decls1 {
                let d2 = decls2
                    .iter()
                    .find(|d| d.name == d1.name)
                    .expect("both sides of 'or' pattern should bind the same variables");
                assert!(d1.mutable == d2.mutable);
                let combined_decl = PatternBoundDecl {
                    name: d1.name,
                    mutable: d1.mutable,
                    expr: if_then_else(&pattern.span, &pat1_matches, &d1.expr, &d2.expr),
                };
                decls.push(combined_decl);
            }

            Ok(matches)
        }
    }
}

// note that this gets called *bottom up*
// that is, if node A is the parent of children B and C,
// then simplify_one_expr is called first on B and C, and then on A

fn simplify_one_expr(ctx: &GlobalCtx, state: &mut State, expr: &Expr) -> Result<Expr, VirErr> {
    use crate::ast::CallTargetKind;
    match &expr.x {
        ExprX::ConstVar(x) => {
            let call = ExprX::Call(
                CallTarget::Fun(
                    CallTargetKind::Static,
                    x.clone(),
                    Arc::new(vec![]),
                    Arc::new(vec![]),
                    AutospecUsage::Final,
                ),
                Arc::new(vec![]),
            );
            Ok(SpannedTyped::new(&expr.span, &expr.typ, call))
        }
        ExprX::Call(CallTarget::Fun(kind, tgt, typs, impl_paths, autospec_usage), args) => {
            assert!(*autospec_usage == AutospecUsage::Final);

            let is_trait_impl = matches!(kind, CallTargetKind::Method(..));
            let args = if typs.len() == 0 && args.len() == 0 && !is_trait_impl {
                // To simplify the AIR/SMT encoding, add a dummy argument to any function with 0 arguments
                let typ = Arc::new(TypX::Int(IntRange::Int));
                use num_traits::Zero;
                let argx = ExprX::Const(Constant::Int(num_bigint::BigInt::zero()));
                let arg = SpannedTyped::new(&expr.span, &typ, argx);
                Arc::new(vec![arg])
            } else {
                args.clone()
            };
            let call = ExprX::Call(
                CallTarget::Fun(
                    kind.clone(),
                    tgt.clone(),
                    typs.clone(),
                    impl_paths.clone(),
                    *autospec_usage,
                ),
                args,
            );
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
                    let op = UnaryOpr::Field(FieldOpr {
                        datatype: path.clone(),
                        variant: variant.clone(),
                        field: field.name.clone(),
                        get_variant: false,
                    });
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
        ExprX::Unary(UnaryOp::CoerceMode { .. }, expr0) => Ok(expr0.clone()),
        ExprX::UnaryOpr(UnaryOpr::TupleField { tuple_arity, field }, expr0) => {
            Ok(tuple_get_field_expr(state, &expr.span, &expr.typ, expr0, *tuple_arity, *field))
        }
        ExprX::Multi(MultiOp::Chained(ops), args) => {
            assert!(args.len() == ops.len() + 1);
            let mut stmts: Vec<Stmt> = Vec::new();
            let mut es: Vec<Expr> = Vec::new();
            for i in 0..args.len() {
                if i == 0 || i == args.len() - 1 {
                    es.push(args[i].clone());
                } else {
                    let (decls, e) = small_or_temp(state, &args[i]);
                    stmts.extend(decls);
                    es.push(e);
                }
            }
            let mut conjunction: Expr = es[0].clone();
            for i in 0..ops.len() {
                let op = match ops[i] {
                    ChainedOp::Inequality(a) => BinaryOp::Inequality(a),
                    ChainedOp::MultiEq => BinaryOp::Eq(Mode::Spec),
                };
                let left = es[i].clone();
                let right = es[i + 1].clone();
                let span = left.span.clone();
                let binary = SpannedTyped::new(&span, &expr.typ, ExprX::Binary(op, left, right));
                if i == 0 {
                    conjunction = binary;
                } else {
                    let exprx = ExprX::Binary(BinaryOp::And, conjunction, binary);
                    conjunction = SpannedTyped::new(&span, &expr.typ, exprx);
                }
            }
            if stmts.len() == 0 {
                Ok(conjunction)
            } else {
                let block = ExprX::Block(Arc::new(stmts), Some(conjunction));
                Ok(SpannedTyped::new(&expr.span, &expr.typ, block))
            }
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
                let body = SpannedTyped::new(&arm.x.pattern.span, &expr.typ, block);
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
                Err(error(&expr.span, "not yet implemented: zero-arm match expressions"))
            }
        }
        ExprX::Ghost { alloc_wrapper: _, tracked: _, expr: expr1 } => Ok(expr1.clone()),
        ExprX::ExecClosure { params, body, requires, ensures, ret, external_spec } => {
            assert!(external_spec.is_none());

            let closure_var_ident = state.next_temp();
            let closure_var = SpannedTyped::new(
                &expr.span,
                &expr.typ.clone(),
                ExprX::Var(closure_var_ident.clone()),
            );

            let external_spec_expr =
                exec_closure_spec(state, &expr.span, &closure_var, params, ret, requires, ensures)?;
            let external_spec = Some((closure_var_ident, external_spec_expr));

            Ok(SpannedTyped::new(
                &expr.span,
                &expr.typ,
                ExprX::ExecClosure {
                    params: params.clone(),
                    body: body.clone(),
                    requires: requires.clone(),
                    ensures: ensures.clone(),
                    ret: ret.clone(),
                    external_spec,
                },
            ))
        }
        ExprX::Assign { init_not_mut, lhs, rhs, op: Some(op) } => {
            match &lhs.x {
                ExprX::VarLoc(id) => {
                    // convert VarLoc to Var to be used on the RHS
                    let var = SpannedTyped::new(&lhs.span, &lhs.typ, ExprX::Var(id.clone()));
                    // insert clipping if the lhs is an integer
                    let new_rhs = if is_integer_type(&lhs.typ) {
                        let range = int_range_from_type(&lhs.typ)
                            .expect("integer types are expected to have a range");
                        SpannedTyped::new(
                            &expr.span,
                            &lhs.typ,
                            ExprX::Unary(
                                // REVIEW:
                                // right now, we are not taking into accound any "verifier(truncate)" annotations
                                // that may be present in this expression; instead, we always truncate. In the future,
                                // we may want to revisit this and make it consistent with what happens in regular
                                // binary expressions.
                                UnaryOp::Clip { range: range, truncate: true },
                                SpannedTyped::new(
                                    &expr.span,
                                    &lhs.typ,
                                    ExprX::Binary(op.clone(), var, rhs.clone()),
                                ),
                            ),
                        )
                    } else {
                        SpannedTyped::new(
                            &expr.span,
                            &lhs.typ,
                            ExprX::Binary(op.clone(), var, rhs.clone()),
                        )
                    };
                    Ok(SpannedTyped::new(
                        &expr.span,
                        &expr.typ,
                        ExprX::Assign {
                            init_not_mut: *init_not_mut,
                            lhs: lhs.clone(),
                            rhs: new_rhs,
                            op: None,
                        },
                    ))
                }
                _ => Err(error(&lhs.span, "not yet implemented: lhs of compound assignment")),
            }
        }
        _ => Ok(expr.clone()),
    }
}

fn tuple_get_field_expr(
    state: &mut State,
    span: &Span,
    typ: &Typ,
    tuple_expr: &Expr,
    tuple_arity: usize,
    field: usize,
) -> Expr {
    let datatype = state.tuple_type_name(tuple_arity);
    let variant = prefix_tuple_variant(tuple_arity);
    let field = prefix_tuple_field(field);
    let op = UnaryOpr::Field(FieldOpr { datatype, variant, field, get_variant: false });
    let field_expr = SpannedTyped::new(span, typ, ExprX::UnaryOpr(op, tuple_expr.clone()));
    field_expr
}

fn simplify_one_stmt(ctx: &GlobalCtx, state: &mut State, stmt: &Stmt) -> Result<Vec<Stmt>, VirErr> {
    match &stmt.x {
        StmtX::Decl { pattern, mode: _, init: None } => match &pattern.x {
            PatternX::Var { .. } => Ok(vec![stmt.clone()]),
            _ => Err(error(&stmt.span, "let-pattern declaration must have an initializer")),
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
            Ok(Arc::new(TypX::Datatype(path, typs.clone(), Arc::new(vec![]))))
        }
        TypX::AnonymousClosure(_typs, _typ, id) => {
            let path = state.closure_type_name(*id);
            Ok(Arc::new(TypX::Datatype(path, Arc::new(vec![]), Arc::new(vec![]))))
        }
        TypX::TypParam(x) => {
            if !local.typ_params.contains(x) {
                return Err(error(
                    &local.span,
                    format!("type parameter {} used before being declared", x),
                ));
            }
            Ok(typ.clone())
        }
        _ => Ok(typ.clone()),
    }
}

fn closure_trait_call_typ_args(state: &mut State, fn_val: &Expr, params: &Binders<Typ>) -> Typs {
    let path = state.tuple_type_name(params.len());

    let param_typs: Vec<Typ> = params.iter().map(|p| p.a.clone()).collect();
    let tup_typ = Arc::new(TypX::Datatype(path, Arc::new(param_typs), Arc::new(vec![])));

    Arc::new(vec![fn_val.typ.clone(), tup_typ])
}

fn mk_closure_req_call(
    state: &mut State,
    span: &Span,
    params: &Binders<Typ>,
    fn_val: &Expr,
    arg_tuple: &Expr,
) -> Expr {
    let bool_typ = Arc::new(TypX::Bool);
    SpannedTyped::new(
        span,
        &bool_typ,
        ExprX::Call(
            CallTarget::BuiltinSpecFun(
                BuiltinSpecFun::ClosureReq,
                closure_trait_call_typ_args(state, fn_val, params),
            ),
            Arc::new(vec![fn_val.clone(), arg_tuple.clone()]),
        ),
    )
}

fn mk_closure_ens_call(
    state: &mut State,
    span: &Span,
    params: &Binders<Typ>,
    fn_val: &Expr,
    arg_tuple: &Expr,
    ret_arg: &Expr,
) -> Expr {
    let bool_typ = Arc::new(TypX::Bool);
    SpannedTyped::new(
        span,
        &bool_typ,
        ExprX::Call(
            CallTarget::BuiltinSpecFun(
                BuiltinSpecFun::ClosureEns,
                closure_trait_call_typ_args(state, fn_val, params),
            ),
            Arc::new(vec![fn_val.clone(), arg_tuple.clone(), ret_arg.clone()]),
        ),
    )
}

fn exec_closure_spec_requires(
    state: &mut State,
    span: &Span,
    closure_var: &Expr,
    params: &Binders<Typ>,
    requires: &Exprs,
) -> Result<Expr, VirErr> {
    // For requires:

    // If the closure has `|a0, a1, a2| requires f(a0, a1, a2)`
    // then we emit a spec of the form
    //
    //      forall x :: f(x.0, x.1, x.2) ==> closure.requires(x)
    //
    // with `closure.requires(x)` as the trigger

    // (Since the user doesn't have the option to specify a trigger here,
    // we need to use the most general one, and that means we need to
    // quantify over a tuple.)

    let param_typs: Vec<Typ> = params.iter().map(|p| p.a.clone()).collect();
    let tuple_path = state.tuple_type_name(params.len());
    let tuple_typ = Arc::new(TypX::Datatype(tuple_path, Arc::new(param_typs), Arc::new(vec![])));
    let tuple_ident = state.next_temp();
    let tuple_var = SpannedTyped::new(span, &tuple_typ, ExprX::Var(tuple_ident.clone()));

    let reqs = conjoin(span, requires);

    // Supply 'let' statements of the form 'let a0 = x.0; let a1 = x.1; ...' etc.

    let mut decls: Vec<Stmt> = Vec::new();
    for (i, p) in params.iter().enumerate() {
        let patternx = PatternX::Var { name: p.name.clone(), mutable: false };
        let pattern = SpannedTyped::new(span, &p.a, patternx);
        let tuple_field = tuple_get_field_expr(state, span, &p.a, &tuple_var, params.len(), i);
        let decl = StmtX::Decl { pattern, mode: Mode::Spec, init: Some(tuple_field) };
        decls.push(Spanned::new(span.clone(), decl));
    }

    let reqs_body =
        SpannedTyped::new(&reqs.span, &reqs.typ, ExprX::Block(Arc::new(decls), Some(reqs.clone())));

    let closure_req_call =
        wrap_in_trigger(&mk_closure_req_call(state, span, params, closure_var, &tuple_var));

    let bool_typ = Arc::new(TypX::Bool);
    let req_quant_body = SpannedTyped::new(
        span,
        &bool_typ,
        ExprX::Binary(BinaryOp::Implies, reqs_body, closure_req_call.clone()),
    );

    let forall = Quant { quant: air::ast::Quant::Forall, boxed_params: true };
    let binders = Arc::new(vec![Arc::new(BinderX { name: tuple_ident, a: tuple_typ })]);
    let req_forall =
        SpannedTyped::new(span, &bool_typ, ExprX::Quant(forall, binders, req_quant_body));

    Ok(req_forall)
}

fn exec_closure_spec_ensures(
    state: &mut State,
    span: &Span,
    closure_var: &Expr,
    params: &Binders<Typ>,
    ret: &Binder<Typ>,
    ensures: &Exprs,
) -> Result<Expr, VirErr> {
    // For ensures:

    // If the closure has `|a0, a1, a2| ensures |b| f(a0, a1, a2, b)`
    // then we emit a spec of the form
    //
    //      forall x, y :: closure.ensures(x, y) ==> f(x.0, x.1, x.2, y)
    //
    // with `closure.ensures(x)` as the trigger

    let param_typs: Vec<Typ> = params.iter().map(|p| p.a.clone()).collect();
    let tuple_path = state.tuple_type_name(params.len());
    let tuple_typ = Arc::new(TypX::Datatype(tuple_path, Arc::new(param_typs), Arc::new(vec![])));
    let tuple_ident = state.next_temp();
    let tuple_var = SpannedTyped::new(span, &tuple_typ, ExprX::Var(tuple_ident.clone()));

    let ret_ident = &ret.name;
    let ret_var = SpannedTyped::new(span, &ret.a, ExprX::Var(ret_ident.clone()));

    let enss = conjoin(span, ensures);

    // Supply 'let' statements of the form 'let a0 = x.0; let a1 = x.1; ...' etc.

    let mut decls: Vec<Stmt> = Vec::new();
    for (i, p) in params.iter().enumerate() {
        let patternx = PatternX::Var { name: p.name.clone(), mutable: false };
        let pattern = SpannedTyped::new(span, &p.a, patternx);
        let tuple_field = tuple_get_field_expr(state, span, &p.a, &tuple_var, params.len(), i);
        let decl = StmtX::Decl { pattern, mode: Mode::Spec, init: Some(tuple_field) };
        decls.push(Spanned::new(span.clone(), decl));
    }

    let enss_body =
        SpannedTyped::new(&enss.span, &enss.typ, ExprX::Block(Arc::new(decls), Some(enss.clone())));

    let closure_ens_call = wrap_in_trigger(&mk_closure_ens_call(
        state,
        span,
        params,
        closure_var,
        &tuple_var,
        &ret_var,
    ));

    let bool_typ = Arc::new(TypX::Bool);
    let ens_quant_body = SpannedTyped::new(
        span,
        &bool_typ,
        ExprX::Binary(BinaryOp::Implies, closure_ens_call.clone(), enss_body),
    );

    let forall = Quant { quant: air::ast::Quant::Forall, boxed_params: true };
    let binders =
        Arc::new(vec![Arc::new(BinderX { name: tuple_ident, a: tuple_typ }), ret.clone()]);
    let ens_forall =
        SpannedTyped::new(span, &bool_typ, ExprX::Quant(forall, binders, ens_quant_body));

    Ok(ens_forall)
}

fn exec_closure_spec(
    state: &mut State,
    span: &Span,
    closure_var: &Expr,
    params: &Binders<Typ>,
    ret: &Binder<Typ>,
    requires: &Exprs,
    ensures: &Exprs,
) -> Result<Expr, VirErr> {
    let req_forall = exec_closure_spec_requires(state, span, closure_var, params, requires)?;

    if ensures.len() > 0 {
        let ens_forall = exec_closure_spec_ensures(state, span, closure_var, params, ret, ensures)?;
        Ok(conjoin(span, &vec![req_forall, ens_forall]))
    } else {
        Ok(req_forall)
    }
}

fn simplify_function(
    ctx: &GlobalCtx,
    state: &mut State,
    function: &Function,
) -> Result<Function, VirErr> {
    state.reset_for_function();
    let mut functionx = function.x.clone();
    let local =
        LocalCtxt { span: function.span.clone(), typ_params: (*functionx.typ_params).clone() };

    let is_trait_impl = matches!(functionx.kind, FunctionKind::TraitMethodImpl { .. });

    // To simplify the AIR/SMT encoding, add a dummy argument to any function with 0 arguments
    if functionx.typ_params.len() == 0
        && functionx.params.len() == 0
        && !functionx.is_const
        && !functionx.attrs.broadcast_forall
        && !is_trait_impl
    {
        let paramx = crate::ast::ParamX {
            name: Arc::new(crate::def::DUMMY_PARAM.to_string()),
            typ: Arc::new(TypX::Int(IntRange::Int)),
            mode: Mode::Spec,
            is_mut: false,
            unwrapped_info: None,
        };
        let param = Spanned::new(function.span.clone(), paramx);
        functionx.params = Arc::new(vec![param]);
    }

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
    let mut local = LocalCtxt { span: datatype.span.clone(), typ_params: Vec::new() };
    for (x, _strict_pos) in datatype.x.typ_params.iter() {
        local.typ_params.push(x.clone());
    }
    crate::ast_visitor::map_datatype_visitor_env(datatype, state, &|state, typ| {
        simplify_one_typ(&local, state, typ)
    })
}

fn simplify_trait_impl(state: &mut State, imp: &TraitImpl) -> Result<TraitImpl, VirErr> {
    let mut local = LocalCtxt { span: imp.span.clone(), typ_params: Vec::new() };
    for x in imp.x.typ_params.iter() {
        local.typ_params.push(x.clone());
    }
    crate::ast_visitor::map_trait_impl_visitor_env(imp, state, &|state, typ| {
        simplify_one_typ(&local, state, typ)
    })
}

fn simplify_assoc_type_impl(
    state: &mut State,
    assoc: &AssocTypeImpl,
) -> Result<AssocTypeImpl, VirErr> {
    let mut local = LocalCtxt { span: assoc.span.clone(), typ_params: Vec::new() };
    for x in assoc.x.typ_params.iter() {
        local.typ_params.push(x.clone());
    }
    crate::ast_visitor::map_assoc_type_impl_visitor_env(assoc, state, &|state, typ| {
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
            name: Arc::new(FunX { path: path.clone() }),
            visibility: Visibility { owning_module: None, restricted_to: None },
            mode: Mode::Spec,
            fuel: 0,
            typ_params: typ_params.clone(),
            typ_bounds: Arc::new(vec![]),
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
    let KrateX {
        functions,
        datatypes,
        traits,
        trait_impls,
        assoc_type_impls,
        module_ids,
        external_fns,
        external_types,
        path_as_rust_names,
    } = &**krate;
    let mut state = State::new();

    // Pre-emptively add this because unit values might be added later.
    state.tuple_type_name(0);

    let functions = vec_map_result(functions, |f| simplify_function(ctx, &mut state, f))?;
    let mut datatypes = vec_map_result(&datatypes, |d| simplify_datatype(&mut state, d))?;
    let trait_impls = vec_map_result(&trait_impls, |t| simplify_trait_impl(&mut state, t))?;
    let assoc_type_impls =
        vec_map_result(&assoc_type_impls, |a| simplify_assoc_type_impl(&mut state, a))?;

    // Add a generic datatype to represent each tuple arity
    // Iterate in sorted order to get consistent output
    let mut tuples: Vec<_> = state.tuple_typs.into_iter().collect();
    tuples.sort_by_key(|kv| kv.0);
    for (arity, path) in tuples {
        let visibility = Visibility { restricted_to: None };
        let transparency = DatatypeTransparency::WhenVisible(visibility.clone());
        let acc = crate::ast::AcceptRecursiveType::RejectInGround;
        let typ_params = Arc::new((0..arity).map(|i| (prefix_tuple_param(i), acc)).collect());
        let mut fields: Vec<Field> = Vec::new();
        for i in 0..arity {
            let typ = Arc::new(TypX::TypParam(prefix_tuple_param(i)));
            let vis = Visibility { restricted_to: None };
            // Note: the mode is irrelevant at this stage, so we arbitrarily use Mode::Exec
            fields.push(ident_binder(&prefix_tuple_field(i), &(typ, Mode::Exec, vis)));
        }
        let variant = ident_binder(&prefix_tuple_variant(arity), &Arc::new(fields));
        let variants = Arc::new(vec![variant]);
        let datatypex = DatatypeX {
            path,
            proxy: None,
            visibility,
            owning_module: None,
            transparency,
            typ_params,
            typ_bounds: Arc::new(vec![]),
            variants,
            mode: Mode::Exec,
            ext_equal: arity > 0,
        };
        datatypes.push(Spanned::new(ctx.no_span.clone(), datatypex));
    }

    let mut closures: Vec<_> = state.closure_typs.into_iter().collect();
    closures.sort_by_key(|kv| kv.0);
    for (_id, path) in closures {
        // Right now, we translate the closure type into an a global datatype.
        //
        // However, I'm pretty sure an anonymous closure can't actually be referenced
        // from outside the item that defines it (Rust seems to represent it as an
        // "opaque type" if it escapes through an existential type, which Verus currently
        // doesn't support anyway.)
        // So in principle, we could make the type private to the item and not emit any
        // global declarations for it.
        //
        // Also, note that the closure type doesn't take any type params, although
        // theoretically it depends on any type params of the enclosing item.
        // e.g., if we have
        //      fn foo<T>(...) {
        //          let x = |t: T| { ... };
        //      }
        // Then the closure type is dependent on T.
        // But since the closure type is only referenced from the item, we can consider
        // T to be fixed, so we don't need to define the closure type polymorphically.

        // Also, note that Rust already prohibits a closure type from depending on itself
        // (not even via reference types, which would be allowed for other types).
        // As such, we don't have to worry about any kind of recursion-checking:
        // a closure type cannot possibly be involved in any type cycle.
        // (In principle, the closure should depend negatively on its param and return types,
        // since they are arguments to the 'requires' and 'ensures' predicates, but thanks
        // to Rust's restrictions, we don't have to do any additional checks.)

        let visibility = Visibility { restricted_to: None };
        let transparency = DatatypeTransparency::Never;

        let typ_params = Arc::new(vec![]);
        let variants = Arc::new(vec![]);

        let datatypex = DatatypeX {
            path,
            proxy: None,
            visibility,
            owning_module: None,
            transparency,
            typ_params,
            typ_bounds: Arc::new(vec![]),
            variants,
            mode: Mode::Exec,
            ext_equal: false,
        };
        datatypes.push(Spanned::new(ctx.no_span.clone(), datatypex));
    }

    let traits = traits.clone();
    let module_ids = module_ids.clone();
    let external_fns = external_fns.clone();
    let external_types = external_types.clone();
    let krate = Arc::new(KrateX {
        functions,
        datatypes,
        traits,
        trait_impls,
        assoc_type_impls,
        module_ids,
        external_fns,
        external_types,
        path_as_rust_names: path_as_rust_names.clone(),
    });
    *ctx = crate::context::GlobalCtx::new(
        &krate,
        ctx.no_span.clone(),
        ctx.inferred_modes.as_ref().clone(),
        ctx.rlimit,
        ctx.interpreter_log.clone(),
        ctx.vstd_crate_name.clone(),
        ctx.arch,
    )?;
    Ok(krate)
}

pub fn merge_krates(krates: Vec<Krate>) -> Result<Krate, VirErr> {
    let mut kratex = KrateX {
        functions: Vec::new(),
        datatypes: Vec::new(),
        traits: Vec::new(),
        trait_impls: Vec::new(),
        assoc_type_impls: Vec::new(),
        module_ids: Vec::new(),
        external_fns: Vec::new(),
        external_types: Vec::new(),
        path_as_rust_names: Vec::new(),
    };
    for k in krates.into_iter() {
        kratex.functions.extend(k.functions.clone());
        kratex.datatypes.extend(k.datatypes.clone());
        kratex.traits.extend(k.traits.clone());
        kratex.trait_impls.extend(k.trait_impls.clone());
        kratex.assoc_type_impls.extend(k.assoc_type_impls.clone());
        kratex.module_ids.extend(k.module_ids.clone());
        kratex.external_fns.extend(k.external_fns.clone());
        kratex.external_types.extend(k.external_types.clone());
        kratex.path_as_rust_names.extend(k.path_as_rust_names.clone());
    }
    Ok(Arc::new(kratex))
}
