use crate::ast::{
    BinaryOp, BindX, Binder, Binders, Constant, Decl, DeclX, Expr, ExprX, Ident, MultiOp, Quant,
    Stmt, StmtX, Stmts, Trigger, Triggers, Typ, TypX, Typs, UnaryOp,
};
use crate::ast_util::{ident_binder, mk_forall};
use crate::context::Context;
use crate::typecheck::DeclaredX;
use crate::util::vec_map;
use std::sync::Arc;

// This module replaces lambda and choose with lower-level, first-order representations.

#[derive(Debug, PartialEq, Eq, Hash)]
pub(crate) enum App {
    Apply(Ident),
    ApplyLambda,
    Unary(UnaryOp),
    Binary(BinaryOp),
    Multi(MultiOp),
    IfElse,
    Let,
    Quant(Quant, Typs, Arc<Vec<usize>>),
    LabeledAssertion,
}

// Represent the shape of an expression with holes that can be filled in various ways.
// The goal is to share expressions that differ only in the way that holes are filled.
// This allows us to prove equality on higher-order expressions.
// For example:
//   - in (lambda ((x Int)) (+ x 4)), we replace 4 with a hole.
//   - in (lambda ((x Int)) (+ x (+ 2 2))), we replace (+ 2 2) with a hole.
// We merge these into a single, shared lambda with a hole:
//   - (lambda ((x Int)) (+ x HOLE))
// based on this shared lambda representation,
// the SMT solver can prove that the two lambdas are equal as long as 4 is equal to (+ 2 2).
pub(crate) type Term = Arc<TermX>;
pub(crate) type Terms = Arc<Vec<Term>>;
#[derive(Debug, PartialEq, Eq, Hash)]
pub(crate) enum TermX {
    Hole(usize),
    Var { depth: usize, index: usize },
    App(App, Terms),
}

#[derive(Debug)]
struct ClosureState {
    typing_depth: usize,
    holes: Vec<(Ident, Typ, Expr)>,
}

#[derive(Debug)]
struct State {
    // function and axiom declarations generated to represent closures
    generated_decls: Vec<Decl>,
    // stack of active ClosureStates
    closure_states: Vec<ClosureState>,
}

impl State {
    fn new() -> Self {
        State { generated_decls: Vec::new(), closure_states: Vec::new() }
    }
}

pub(crate) type ClosureTerm = Arc<ClosureTermX>;
#[derive(Debug, PartialEq, Eq, Hash)]
pub(crate) struct ClosureTermX {
    terms: Vec<Term>,
    params: Typs,
    holes: Typs,
}

// We generate new function declarations for closures while processing the expressions
// that contain the closures.
// The function declarations live in scope outside the expression scope, so
// we need to insert them into the typing's outer scope:
fn insert_fun_typing(ctxt: &mut Context, x: &Ident, typs: &Typs, typ: &Typ) {
    let fun = DeclaredX::Fun(typs.clone(), typ.clone());

    // the maps that aren't ctxt.typing.decls (e.g. apply_map) are still in the outer scope,
    // so use one of them as the outer scope index:
    let scope_index = ctxt.apply_map.num_scopes() - 1;

    ctxt.typing.decls.insert_at(scope_index, x.clone(), Arc::new(fun)).expect("insert_fun_typing");
}

fn mk_apply(ctxt: &mut Context, state: &mut State, param_typs: Typs, ret_typ: Typ) -> Ident {
    if let Some(name) = ctxt.apply_map.get(&(param_typs.clone(), ret_typ.clone())) {
        name.clone()
    } else {
        let name = Arc::new(format!("{}{}", crate::def::APPLY, ctxt.apply_count));
        ctxt.apply_count += 1;
        ctxt.apply_map
            .insert((param_typs.clone(), ret_typ.clone()), name.clone())
            .expect("mk_apply insert");
        let mut typs: Vec<Typ> =
            vec![Arc::new(TypX::Named(Arc::new(crate::def::FUNCTION.to_string())))];
        typs.extend((*param_typs).clone());
        let decl = Arc::new(DeclX::Fun(name.clone(), Arc::new(typs), ret_typ.clone()));
        state.generated_decls.push(decl);
        insert_fun_typing(ctxt, &name, &param_typs, &ret_typ);
        name
    }
}

fn enclose_force_hole(
    state: &mut ClosureState,
    typ: Typ,
    expr: Expr,
    term: Option<Term>,
) -> (Expr, Term) {
    match term {
        None => {
            // allocate hole
            let n = state.holes.len();
            let x = Arc::new(format!("{}{}", crate::def::HOLE, n));
            state.holes.push((x.clone(), typ, expr));
            (Arc::new(ExprX::Var(x)), Arc::new(TermX::Hole(n)))
        }
        Some(t) => (expr, t),
    }
}

fn enclose(
    state: &mut State,
    app: App,
    exprs: Vec<Expr>,
    terms: Vec<(Typ, Option<Term>)>,
) -> (Vec<Expr>, Option<Term>) {
    if let Some(state) = state.closure_states.last_mut() {
        if terms.iter().any(|(_, t)| t.is_some()) {
            // At least one of the exprs is not a hole, so we will return a non-hole (Some).
            // For any of the exprs that are holes (None), we need to allocate an actual hole.
            let mut es: Vec<Expr> = Vec::new();
            let mut ts: Vec<Term> = Vec::new();
            for (e, (typ, t)) in exprs.into_iter().zip(terms.into_iter()) {
                let (e, t) = enclose_force_hole(state, typ, e, t);
                es.push(e);
                ts.push(t);
            }
            let t = Arc::new(TermX::App(app, Arc::new(ts)));
            (es, Some(t))
        } else {
            // All of the exprs are holes, so merge them into a bigger hole (None)
            (exprs, None)
        }
    } else {
        (exprs, None)
    }
}

fn simplify_var(ctxt: &mut Context, state: &mut State, x: &Ident) -> (Typ, Option<Term>) {
    let typ = match ctxt.typing.get(x) {
        Some(DeclaredX::Var { typ, .. }) => typ.clone(),
        _ => panic!("internal error: missing variable {}", x),
    };
    let term = if let Some(state) = state.closure_states.last() {
        let (depth, index) =
            ctxt.typing.decls.scope_and_index_of_key(x).expect("simplify_expr depth");
        if state.typing_depth <= depth {
            // x is one of our closure's variables (parameter or declared in body)
            Some(Arc::new(TermX::Var { depth: depth - state.typing_depth, index }))
        } else {
            // variable from outside the closure (becomes a hole)
            None
        }
    } else {
        None
    };
    (typ, term)
}

fn simplify_lambda(
    ctxt: &mut Context,
    state: &mut State,
    binders: &Binders<Typ>,
    e1: &Expr,
) -> (Typ, Expr, Option<Term>) {
    let closure_state =
        ClosureState { typing_depth: ctxt.typing.decls.num_scopes(), holes: Vec::new() };
    ctxt.typing.decls.push_scope(true);
    for binder in binders.iter() {
        let var = DeclaredX::Var { typ: binder.a.clone(), mutable: false };
        let _ = ctxt.typing.insert(&binder.name, Arc::new(var));
    }
    state.closure_states.push(closure_state);
    let (typ1, e1, t1) = simplify_expr(ctxt, state, e1);
    let mut closure_state = state.closure_states.pop().unwrap();
    ctxt.typing.decls.pop_scope();
    let (e1, t1) = enclose_force_hole(&mut closure_state, typ1.clone(), e1, t1);
    let param_typs = Arc::new(vec_map(&**binders, |b| b.a.clone()));
    let typ = Arc::new(TypX::Lambda);
    let holes = Arc::new(vec_map(&closure_state.holes, |(_, typ, _)| typ.clone()));
    let closure =
        ClosureTermX { terms: vec![t1], params: param_typs.clone(), holes: holes.clone() };
    let closure = Arc::new(closure);
    let closure_fun = match ctxt.lambda_map.get(&closure) {
        None => {
            let name = format!("{}{}", crate::def::LAMBDA, ctxt.lambda_count);
            let closure_fun = Arc::new(name);
            ctxt.lambda_count += 1;
            let _ = ctxt.lambda_map.insert(closure, closure_fun.clone());

            // f(holes): (Fun (t_params) t_body)
            let decl = Arc::new(DeclX::Fun(closure_fun.clone(), holes.clone(), typ.clone()));
            state.generated_decls.push(decl);
            insert_fun_typing(ctxt, &closure_fun, &holes, &typ);

            // forall holes params. #[trigger] apply_param_typs(f(captures), params) == body
            let mut xholes: Vec<Expr> = Vec::new();
            let mut bs: Vec<Binder<Typ>> = Vec::new();
            for (x, typ, _) in closure_state.holes.iter() {
                xholes.push(Arc::new(ExprX::Var(x.clone())));
                bs.push(ident_binder(x, typ));
            }
            let call = Arc::new(ExprX::Apply(closure_fun.clone(), Arc::new(xholes)));
            let mut eparams: Vec<Expr> = vec![call];
            for binder in binders.iter() {
                bs.push(binder.clone());
                eparams.push(Arc::new(ExprX::Var(binder.name.clone())));
            }
            let apply_fun = mk_apply(ctxt, state, param_typs, typ1);
            let apply = Arc::new(ExprX::Apply(apply_fun, Arc::new(eparams)));
            let eq = Arc::new(ExprX::Binary(BinaryOp::Eq, apply.clone(), e1));
            let trig = Arc::new(vec![apply]);
            let trigs = Arc::new(vec![trig]);
            let forall = mk_forall(&bs, &trigs, &eq);
            let decl = Arc::new(DeclX::Axiom(forall));
            state.generated_decls.push(decl);

            closure_fun
        }
        Some(closure_fun) => closure_fun.clone(),
    };
    let exprs = vec_map(&closure_state.holes, |(_, _, e)| e.clone());
    let app = Arc::new(ExprX::Apply(closure_fun, Arc::new(exprs)));
    if state.closure_states.len() == 0 {
        (typ, app, None)
    } else {
        // REVIEW: when we're nested in a closure, it's easiest to just rerun
        // the simplifier on the simplified inner closure, so we can generate the
        // correct holes in the outer closure.  This is inefficient, though,
        // on unusually deeply nested, treelike closures.
        simplify_expr(ctxt, state, &app)
    }
}

fn simplify_choose(
    ctxt: &mut Context,
    state: &mut State,
    binder: &Binder<Typ>,
    triggers: &Triggers,
    e1: &Expr,
) -> (Typ, Expr, Option<Term>) {
    let closure_state =
        ClosureState { typing_depth: ctxt.typing.decls.num_scopes(), holes: Vec::new() };
    let mut terms: Vec<Term> = Vec::new();
    let mut new_triggers: Vec<Trigger> = Vec::new();

    ctxt.typing.decls.push_scope(true);
    let var = DeclaredX::Var { typ: binder.a.clone(), mutable: false };
    let _ = ctxt.typing.insert(&binder.name, Arc::new(var));
    state.closure_states.push(closure_state);
    let (typ1, e1, t1) = simplify_expr(ctxt, state, e1);
    let (e1, t1) =
        enclose_force_hole(state.closure_states.last_mut().unwrap(), typ1.clone(), e1, t1);
    terms.push(t1);
    for trigger in triggers.iter() {
        let mut new_trigger: Vec<Expr> = Vec::new();
        for e in trigger.iter() {
            let (_, e, t) = simplify_expr(ctxt, state, e);
            let (e, t) =
                enclose_force_hole(state.closure_states.last_mut().unwrap(), typ1.clone(), e, t);
            terms.push(t);
            new_trigger.push(e);
        }
        new_triggers.push(Arc::new(new_trigger));
    }
    let closure_state = state.closure_states.pop().unwrap();
    ctxt.typing.decls.pop_scope();

    let param_typs = Arc::new(vec![binder.a.clone()]);
    let holes = Arc::new(vec_map(&closure_state.holes, |(_, typ, _)| typ.clone()));
    let closure = ClosureTermX { terms, params: param_typs.clone(), holes: holes.clone() };
    let closure = Arc::new(closure);

    // Declare closure function or find existing closure function
    let closure_fun = match ctxt.choose_map.get(&closure) {
        None => {
            let name = format!("{}{}", crate::def::CHOOSE, ctxt.choose_count);
            let closure_fun = Arc::new(name);
            ctxt.choose_count += 1;
            let _ = ctxt.choose_map.insert(closure, closure_fun.clone());

            // f(holes): typ_x
            let decl = Arc::new(DeclX::Fun(closure_fun.clone(), holes.clone(), binder.a.clone()));
            state.generated_decls.push(decl);
            insert_fun_typing(ctxt, &closure_fun, &holes, &binder.a);

            // forall captures. (exists {triggers} x. body) ==> let x = #[trigger] f(captures) in body
            let mut xholes: Vec<Expr> = Vec::new();
            let mut bs: Vec<Binder<Typ>> = Vec::new();
            for (x, typ, _) in closure_state.holes.iter() {
                xholes.push(Arc::new(ExprX::Var(x.clone())));
                bs.push(ident_binder(x, typ));
            }
            let call = Arc::new(ExprX::Apply(closure_fun.clone(), Arc::new(xholes)));
            let existsbs = Arc::new(vec![binder.clone()]);
            let existsbind =
                Arc::new(BindX::Quant(Quant::Exists, existsbs, Arc::new(new_triggers)));
            let exists = Arc::new(ExprX::Bind(existsbind, e1.clone()));
            let bindlet = Arc::new(BindX::Let(Arc::new(vec![binder.new_a(call.clone())])));
            let elet = Arc::new(ExprX::Bind(bindlet, e1));
            let imply = Arc::new(ExprX::Binary(BinaryOp::Implies, exists.clone(), elet));
            let trig = Arc::new(vec![call]);
            let trigs = Arc::new(vec![trig]);
            let forall = mk_forall(&bs, &trigs, &imply);
            let decl = Arc::new(DeclX::Axiom(forall));
            state.generated_decls.push(decl);

            closure_fun
        }
        Some(closure_fun) => closure_fun.clone(),
    };

    let exprs = vec_map(&closure_state.holes, |(_, _, e)| e.clone());
    let app = Arc::new(ExprX::Apply(closure_fun, Arc::new(exprs)));
    if state.closure_states.len() == 0 {
        (binder.a.clone(), app, None)
    } else {
        // REVIEW: when we're nested in a closure, it's easiest to just rerun
        // the simplifier on the simplified inner closure, so we can generate the
        // correct holes in the outer closure.  This is inefficient, though,
        // on unusually deeply nested, treelike closures.
        simplify_expr(ctxt, state, &app)
    }
}

fn simplify_exprs(
    ctxt: &mut Context,
    state: &mut State,
    exprs: &Vec<Expr>,
) -> (Vec<Expr>, Vec<(Typ, Option<Term>)>) {
    let mut es: Vec<Expr> = Vec::new();
    let mut ts: Vec<(Typ, Option<Term>)> = Vec::new();
    for expr in exprs.iter() {
        let (typ, e, t) = simplify_expr(ctxt, state, expr);
        es.push(e);
        ts.push((typ, t));
    }
    (es, ts)
}

fn simplify_exprs_ref(
    ctxt: &mut Context,
    state: &mut State,
    exprs: &Vec<&Expr>,
) -> (Vec<Expr>, Vec<(Typ, Option<Term>)>) {
    let mut es: Vec<Expr> = Vec::new();
    let mut ts: Vec<(Typ, Option<Term>)> = Vec::new();
    for expr in exprs.iter() {
        let (typ, e, t) = simplify_expr(ctxt, state, expr);
        es.push(e);
        ts.push((typ, t));
    }
    (es, ts)
}

fn simplify_expr(ctxt: &mut Context, state: &mut State, expr: &Expr) -> (Typ, Expr, Option<Term>) {
    match &**expr {
        ExprX::Const(c) => {
            let typ = match c {
                Constant::Bool(_) => Arc::new(TypX::Bool),
                Constant::Nat(_) => Arc::new(TypX::Int),
                Constant::BitVec(_, width) => Arc::new(TypX::BitVec(*width)),
            };
            (typ, expr.clone(), None)
        }
        ExprX::Var(x) => {
            let (typ, term) = simplify_var(ctxt, state, x);
            (typ, expr.clone(), term)
        }
        ExprX::Old(_, x) => {
            // Note: Old(_, x), where x is one of the closure's variables, is equivalent to Var(x)
            let (typ, term) = simplify_var(ctxt, state, x);
            (typ, expr.clone(), term)
        }
        ExprX::Apply(x, args) => {
            let typ = match ctxt.typing.get(x) {
                Some(DeclaredX::Fun(_, typ)) => typ.clone(),
                _ => panic!("internal error: missing function {}", x),
            };
            let (es, ts) = simplify_exprs(ctxt, state, &**args);
            let (es, t) = enclose(state, App::Apply(x.clone()), es, ts);
            (typ, Arc::new(ExprX::Apply(x.clone(), Arc::new(es))), t)
        }
        ExprX::ApplyLambda(typ, e0, args) => {
            let mut es: Vec<&Expr> = vec![e0];
            for e in args.iter() {
                es.push(e);
            }
            let (es, ts) = simplify_exprs_ref(ctxt, state, &es);
            let mut typs = vec_map(&ts, |(typ, _)| typ.clone());
            typs.remove(0);
            let (es, t) = enclose(state, App::ApplyLambda, es, ts);
            let apply_fun = mk_apply(ctxt, state, Arc::new(typs), typ.clone());
            (typ.clone(), Arc::new(ExprX::Apply(apply_fun, Arc::new(es))), t)
        }
        ExprX::Unary(op, e1) => {
            let typ = match op {
                UnaryOp::Not => Arc::new(TypX::Bool),
            };
            let (es, ts) = simplify_exprs_ref(ctxt, state, &vec![e1]);
            let (es, t) = enclose(state, App::Unary(*op), es, ts);
            (typ, Arc::new(ExprX::Unary(*op, es[0].clone())), t)
        }
        ExprX::Binary(op, e1, e2) => {
            let typ = match op {
                BinaryOp::Implies | BinaryOp::Eq => Arc::new(TypX::Bool),
                BinaryOp::Le | BinaryOp::Ge | BinaryOp::Lt | BinaryOp::Gt => Arc::new(TypX::Bool),
                BinaryOp::EuclideanDiv | BinaryOp::EuclideanMod => Arc::new(TypX::Int),
                // TODO: is this actually reasonable for bit vector operations?
                BinaryOp::UintXor
                | BinaryOp::BitXor
                | BinaryOp::BitAnd
                | BinaryOp::BitOr
                | BinaryOp::BitAdd
                | BinaryOp::Shr
                | BinaryOp::Shl => Arc::new(TypX::Int),
            };
            let (es, ts) = simplify_exprs_ref(ctxt, state, &vec![e1, e2]);
            let (es, t) = enclose(state, App::Binary(*op), es, ts);
            (typ, Arc::new(ExprX::Binary(*op, es[0].clone(), es[1].clone())), t)
        }
        ExprX::Multi(op, es) => {
            let typ = match op {
                MultiOp::And | MultiOp::Or => Arc::new(TypX::Bool),
                MultiOp::Add | MultiOp::Sub | MultiOp::Mul => Arc::new(TypX::Int),
                MultiOp::Distinct => Arc::new(TypX::Bool),
            };
            let (es, ts) = simplify_exprs(ctxt, state, &es);
            let (es, t) = enclose(state, App::Multi(*op), es, ts);
            (typ, Arc::new(ExprX::Multi(*op, Arc::new(es))), t)
        }
        ExprX::IfElse(e0, e1, e2) => {
            let (es, ts) = simplify_exprs_ref(ctxt, state, &vec![e0, e1, e2]);
            let (typ, _) = ts[1].clone();
            let (es, t) = enclose(state, App::IfElse, es, ts);
            (typ, Arc::new(ExprX::IfElse(es[0].clone(), es[1].clone(), es[2].clone())), t)
        }
        ExprX::Bind(bind, e1) => match &**bind {
            BindX::Let(binders) => {
                let mut es: Vec<Expr> = Vec::new();
                let mut ts: Vec<(Typ, Option<Term>)> = Vec::new();
                for binder in binders.iter() {
                    let (typ, e, t) = simplify_expr(ctxt, state, &binder.a);
                    es.push(e);
                    ts.push((typ, t));
                }
                ctxt.typing.decls.push_scope(true);
                for (binder, (typ, _)) in binders.iter().zip(ts.iter()) {
                    let var = DeclaredX::Var { typ: typ.clone(), mutable: false };
                    let _ = ctxt.typing.insert(&binder.name, Arc::new(var));
                }
                let (typ1, e1, t1) = simplify_expr(ctxt, state, e1);
                ts.push((typ1.clone(), t1));
                es.push(e1);
                ctxt.typing.decls.pop_scope();

                let (es, t) = enclose(state, App::Let, es, ts);
                let mut bs: Vec<Binder<Expr>> = Vec::new();
                for (binder, e) in binders.iter().zip(es.iter()) {
                    bs.push(binder.new_a(e.clone()));
                }
                let e1 = es.last().unwrap();
                let bind = Arc::new(BindX::Let(Arc::new(bs)));
                let expr = Arc::new(ExprX::Bind(bind, e1.clone()));
                (typ1, expr, t)
            }
            BindX::Quant(quant, binders, triggers) => {
                ctxt.typing.decls.push_scope(true);
                let mut typs: Vec<Typ> = Vec::new();
                for binder in binders.iter() {
                    let var = DeclaredX::Var { typ: binder.a.clone(), mutable: false };
                    let _ = ctxt.typing.insert(&binder.name, Arc::new(var));
                    typs.push(binder.a.clone());
                }
                let mut es: Vec<&Expr> = Vec::new();
                let mut trigger_shape: Vec<usize> = Vec::new();
                for trigger in triggers.iter() {
                    trigger_shape.push(trigger.len());
                    for e in trigger.iter() {
                        es.push(&e);
                    }
                }
                es.push(&e1);
                let (es, ts) = simplify_exprs_ref(ctxt, state, &es);
                let app = App::Quant(*quant, Arc::new(typs), Arc::new(trigger_shape));
                let (es, t) = enclose(state, app, es, ts);
                ctxt.typing.decls.pop_scope();

                let mut new_triggers: Vec<Trigger> = Vec::new();
                let mut i: usize = 0;
                for trigger in triggers.iter() {
                    let mut new_trigger: Vec<Expr> = Vec::new();
                    for _ in trigger.iter() {
                        new_trigger.push(es[i].clone());
                        i += 1;
                    }
                    new_triggers.push(Arc::new(new_trigger));
                }
                let e1 = es[i].clone();
                let typ = Arc::new(TypX::Bool);
                let bind = BindX::Quant(*quant, binders.clone(), Arc::new(new_triggers));
                (typ, Arc::new(ExprX::Bind(Arc::new(bind), e1)), t)
            }
            BindX::Lambda(binders) => simplify_lambda(ctxt, state, binders, e1),
            BindX::Choose(binder, triggers) => simplify_choose(ctxt, state, binder, triggers, e1),
        },
        ExprX::LabeledAssertion(span, e1) => {
            let (es, ts) = simplify_exprs_ref(ctxt, state, &vec![e1]);
            let (typ, _) = ts[0].clone();
            let (es, t) = enclose(state, App::LabeledAssertion, es, ts);
            (typ, Arc::new(ExprX::LabeledAssertion(span.clone(), es[0].clone())), t)
        }
    }
}

fn simplify_stmt_rec(ctxt: &mut Context, state: &mut State, stmt: &Stmt) -> Stmt {
    match &**stmt {
        StmtX::Assume(expr) => {
            let (_, expr, _) = simplify_expr(ctxt, state, expr);
            Arc::new(StmtX::Assume(expr))
        }
        StmtX::Assert(span, expr) => {
            let (_, expr, _) = simplify_expr(ctxt, state, expr);
            Arc::new(StmtX::Assert(span.clone(), expr))
        }
        StmtX::Havoc(_) => stmt.clone(),
        StmtX::Assign(x, expr) => {
            let (_, expr, _) = simplify_expr(ctxt, state, expr);
            Arc::new(StmtX::Assign(x.clone(), expr))
        }
        StmtX::Snapshot(_) => stmt.clone(),
        StmtX::DeadEnd(stmt) => Arc::new(StmtX::DeadEnd(simplify_stmt_rec(ctxt, state, stmt))),
        StmtX::Block(stmts) => Arc::new(StmtX::Block(simplify_stmts(ctxt, state, stmts))),
        StmtX::Switch(stmts) => Arc::new(StmtX::Switch(simplify_stmts(ctxt, state, stmts))),
    }
}

fn simplify_stmts(ctxt: &mut Context, state: &mut State, stmts: &Stmts) -> Stmts {
    let mut ss: Vec<Stmt> = Vec::new();
    for s in stmts.iter() {
        ss.push(simplify_stmt_rec(ctxt, state, s));
    }
    Arc::new(ss)
}

pub(crate) fn simplify_stmt(ctxt: &mut Context, stmt: &Stmt) -> (Vec<Decl>, Stmt) {
    let mut state = State::new();
    let stmt = simplify_stmt_rec(ctxt, &mut state, stmt);
    (state.generated_decls, stmt)
}

pub(crate) fn simplify_decl(ctxt: &mut Context, decl: &Decl) -> (Vec<Decl>, Decl) {
    assert_eq!(ctxt.apply_map.num_scopes(), ctxt.typing.decls.num_scopes());
    let mut state = State::new();
    let decl = match &**decl {
        DeclX::Sort(..) => decl.clone(),
        DeclX::Datatypes(..) => decl.clone(),
        DeclX::Const(..) => decl.clone(),
        DeclX::Fun(..) => decl.clone(),
        DeclX::Var(..) => decl.clone(),
        DeclX::Axiom(expr) => {
            let (_, expr, _) = simplify_expr(ctxt, &mut state, expr);
            Arc::new(DeclX::Axiom(expr))
        }
    };
    (state.generated_decls, decl)
}
