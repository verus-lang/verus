use crate::ast::{BinaryOp, Expr, Function, Ident, Params, SpannedTyped, Typ, TypX, UnaryOp};
use crate::ast_to_sst::{get_function, State};
use crate::context::Ctx;
use crate::def::Spanned;
use crate::sst::{Bnd, BndX, Exp, ExpX, Exps, Stm, StmX, UniqueIdent};
use air::ast::{Binder, BinderX, Span};
use air::errors::Error;
use std::collections::HashMap;
use std::sync::Arc;

fn subsitute_argument(
    exp: &Exp,
    arg_map: &HashMap<Arc<String>, Exp>,
) -> Result<Exp, (Span, String)> {
    let result = match &exp.x {
        ExpX::Var(UniqueIdent { name: id, local: _ }) => match arg_map.get(id) {
            Some(e) => e.clone(),
            None => exp.clone(),
        },
        ExpX::Call(x, typs, es) => {
            let mut es_replaced = vec![];
            for e in es.iter() {
                let e_replaced = subsitute_argument(e, arg_map)?;
                es_replaced.push(e_replaced);
            }
            let new_exp = ExpX::Call(x.clone(), typs.clone(), Arc::new(es_replaced));
            SpannedTyped::new(&exp.span, &exp.typ, new_exp)
        }
        ExpX::Unary(op, e1) => {
            let e1_replaced = subsitute_argument(e1, arg_map)?;
            let new_exp = ExpX::Unary(*op, e1_replaced);
            SpannedTyped::new(&exp.span, &exp.typ, new_exp)
        }
        ExpX::UnaryOpr(uop, e1) => {
            let e1_replaced = subsitute_argument(e1, arg_map)?;
            let new_exp = ExpX::UnaryOpr(uop.clone(), e1_replaced);
            SpannedTyped::new(&exp.span, &exp.typ, new_exp)
        }
        ExpX::Binary(bop, e1, e2) => {
            let e1_replaced = subsitute_argument(e1, arg_map)?;
            let e2_replaced = subsitute_argument(e2, arg_map)?;
            let new_exp = ExpX::Binary(*bop, e1_replaced, e2_replaced);
            SpannedTyped::new(&exp.span, &exp.typ, new_exp)
        }
        ExpX::If(e1, e2, e3) => {
            let e1_replaced = subsitute_argument(e1, arg_map)?;
            let e2_replaced = subsitute_argument(e2, arg_map)?;
            let e3_replaced = subsitute_argument(e3, arg_map)?;
            let new_exp = ExpX::If(e1_replaced, e2_replaced, e3_replaced);
            SpannedTyped::new(&exp.span, &exp.typ, new_exp)
        }
        ExpX::Bind(bnd, e1) => {
            // In the arg_map, remove names that will be binded locally
            let mut arg_map = arg_map.clone();
            arg_map.retain(|name, _| {
                let binded_names: Vec<Ident> = match &bnd.x {
                    BndX::Let(binders) => binders.iter().map(|b| b.name.clone()).collect(),
                    BndX::Quant(_, binders, _) => binders.iter().map(|b| b.name.clone()).collect(),
                    BndX::Choose(binders, _, _) => binders.iter().map(|b| b.name.clone()).collect(),
                    BndX::Lambda(binders) => binders.iter().map(|b| b.name.clone()).collect(),
                };
                !binded_names.iter().any(|bname| **bname == **name)
            });
            let arg_map = arg_map;
            let e1_replaced = subsitute_argument(e1, &arg_map)?;
            let bnd_replaced: Bnd = match &bnd.x {
                BndX::Let(binders) => {
                    let mut new_binders: Vec<Binder<Exp>> = vec![];
                    for old_b in &**binders {
                        let new_b = BinderX {
                            name: old_b.name.clone(),
                            a: subsitute_argument(&old_b.a, &arg_map)?,
                        };
                        new_binders.push(Arc::new(new_b));
                    }
                    Spanned::new(bnd.span.clone(), BndX::Let(Arc::new(new_binders)))
                }
                BndX::Quant(quant, bndrs, _trigs) => Spanned::new(
                    bnd.span.clone(),
                    BndX::Quant(quant.clone(), bndrs.clone(), Arc::new(vec![])),
                ),
                _ => {
                    return Err((
                        exp.span.clone(),
                        format!("Unsupported binder during subsitution"),
                    ));
                }
            };
            let new_exp = ExpX::Bind(bnd_replaced, e1_replaced);
            SpannedTyped::new(&exp.span, &exp.typ, new_exp)
        }
        ExpX::Const(_) => exp.clone(),
        _ => {
            return Err((exp.span.clone(), format!("Unsupported expression during subsitution")));
        }
    };
    Ok(result)
}

fn is_bool_type(t: &Typ) -> bool {
    match &**t {
        TypX::Bool => true,
        TypX::Boxed(b) => is_bool_type(b),
        _ => false,
    }
}

fn is_same_type(t1: &Typ, t2: &Typ) -> bool {
    match (&**t1, &**t2) {
        (TypX::Bool, TypX::Bool)
        | (TypX::Int(_), TypX::Int(_))
        | (TypX::Tuple(_), TypX::Tuple(_))
        | (TypX::Lambda(_, _), TypX::Lambda(_, _))
        | (TypX::Datatype(_, _), TypX::Datatype(_, _))
        | (TypX::TypParam(_), TypX::TypParam(_))
        | (TypX::TypeId, TypX::TypeId)
        | (TypX::Air(_), TypX::Air(_)) => true,
        (TypX::Boxed(b1), TypX::Boxed(b2)) => is_same_type(b1, b2),
        _ => false,
    }
}

pub(crate) fn tr_inline_expression(
    body_exp: &Exp,
    params: &Params,
    exps: &Exps,
) -> Result<Exp, (Span, String)> {
    match *body_exp.typ {
        TypX::Bool => (),
        _ => {
            return Err((
                body_exp.span.clone(),
                "Skip inlining for non-boolean expreesion".to_string(),
            ));
        }
    };
    let mut arg_map: HashMap<Arc<String>, Exp> = HashMap::new();
    let mut count = 0;
    for param in &**params {
        let exp_to_insert = &exps[count];
        if !is_same_type(&param.x.typ, &exp_to_insert.typ) {
            return Err((
                exp_to_insert.span.clone(),
                "Error: arg type mismatch during expression inlining".to_string(),
            ));
        }
        arg_map.insert(param.x.name.clone(), exp_to_insert.clone());
        count = count + 1;
    }
    return subsitute_argument(body_exp, &arg_map);
}

pub(crate) fn pure_ast_expression_to_sst(ctx: &Ctx, body: &Expr, params: &Params) -> Exp {
    crate::ast_to_sst::expr_to_exp_as_spec(
        &ctx,
        &HashMap::new(),
        &crate::func_to_air::params_to_pars(params, true), // REVIEW: is `true` here desirable?
        &body,
    )
    .expect("pure_ast_expression_to_sst")
}

fn tr_inline_function(
    ctx: &Ctx,
    state: &State,
    fun_to_inline: Function,
    exps: &Exps,
    span: &Span,
) -> Result<Exp, (Span, String)> {
    let opaque_err = Err((fun_to_inline.span.clone(), "Note: this function is opaque".to_string()));
    let closed_err = Err((
        fun_to_inline.span.clone(),
        "Note: this function is closed at the module boundary".to_string(),
    ));
    let foriegn_module_err = Err((
        fun_to_inline.span.clone(),
        "Note: this function is inside a foriegn module".to_string(),
    ));
    let type_err = Err((
        fun_to_inline.span.clone(),
        "Note: this function body is not inlined since it is not bool type".to_string(),
    ));

    let mut found_local_fuel = false;
    let fuel = match state.find_fuel(&fun_to_inline.x.name) {
        Some(local_fuel) => {
            found_local_fuel = true;
            local_fuel
        } // prefer local_fuel on fun.x.fuel. local_fuel tracks `reveal` statements
        None => fun_to_inline.x.fuel,
    };

    let mut hidden = false; // track `hide` statement
    match &state.fun {
        Some(f) => {
            let fun_owner = get_function(ctx, span, f).unwrap();
            let fs_to_hide = &fun_owner.x.attrs.hidden;
            for f_to_hide in &**fs_to_hide {
                if **f_to_hide == *fun_to_inline.x.name {
                    hidden = true;
                };
            }
        }
        None => {
            return Err((
                span.clone(),
                "Internal error: cannot find the owning function of this function call".to_string(),
            ));
        }
    };

    if fuel == 0 || (!found_local_fuel && hidden) {
        return opaque_err;
    } else {
        if fun_to_inline.x.visibility.owning_module.is_none() {
            return foriegn_module_err;
        } else {
            if *ctx.module != **fun_to_inline.x.visibility.owning_module.as_ref().unwrap() {
                // if the target inline function is outside this module, track `open` `closed` at module boundaries
                match fun_to_inline.x.publish {
                    Some(b) => {
                        if !b {
                            return opaque_err;
                        }
                    }
                    None => {
                        return closed_err;
                    }
                };
            }
        }

        let body = match fun_to_inline.x.body.as_ref() {
            Some(body) => body,
            None => {
                return closed_err;
            }
        };

        if !is_bool_type(&body.typ) {
            return type_err;
        }

        let params = &fun_to_inline.x.params;
        let body_exp = pure_ast_expression_to_sst(ctx, body, params);

        if crate::recursion::is_recursive_exp(ctx, &fun_to_inline.x.name, &body_exp) {
            return Err((
                fun_to_inline.span.clone(),
                format!("Note: this function is recursive with fuel {fuel}"),
            ));
        } else {
            return tr_inline_expression(&body_exp, params, exps);
        }
    }
}

//  Note that `e` is not the same with the highlighted expression. It is the expression that will be handed to Z3 for verification condition.
//  For example,  A => (B && C) is splitted into A => B and A => B => C. When A => B => C fails, only C will be highlighted.
//  For details, See BinaryOp::And/OR, `implies`, `If`, `Bind`.
pub type TracedExp = Arc<TracedExpX>;
pub type TracedExps = Arc<Vec<TracedExp>>;
pub struct TracedExpX {
    pub e: Exp,                    // Exp to be discharged to Z3
    pub trace: air::errors::Error, //  when inlining function, log call stack into `trace`
}
impl TracedExpX {
    pub fn new(e: Exp, trace: air::errors::Error) -> TracedExp {
        Arc::new(TracedExpX { e, trace })
    }
}

fn negate_atom(exp: TracedExp) -> TracedExp {
    let negated_expx = ExpX::Unary(UnaryOp::Not, exp.e.clone());
    let negated_exp = SpannedTyped::new(&exp.e.span, &exp.e.typ, negated_expx);
    TracedExpX::new(negated_exp.clone(), exp.trace.clone())
}

fn mk_atom(e: TracedExp, negated: bool) -> TracedExps {
    if negated { Arc::new(vec![negate_atom(e)]) } else { Arc::new(vec![e]) }
}

fn merge_two_es(es1: TracedExps, es2: TracedExps) -> TracedExps {
    let mut merged_vec = vec![];
    for e in &*es1 {
        merged_vec.push(e.clone());
    }
    for e in &*es2 {
        merged_vec.push(e.clone());
    }
    return Arc::new(merged_vec);
}

// Assuming e1, try to prove e2. Hence we use the span of e2 here.
fn mk_imply_traced(e1: &Exp, e2: &TracedExp) -> TracedExp {
    let imply = ExpX::Binary(BinaryOp::Implies, e1.clone(), e2.e.clone());
    let imply_exp = SpannedTyped::new(&e2.e.span, &Arc::new(TypX::Bool), imply);
    TracedExpX::new(imply_exp, e2.trace.clone())
}

fn mk_chained_implies(es: TracedExps) -> TracedExps {
    let mut chained_vec = vec![];
    let mut chained_e = es.first().unwrap().clone();
    // REVIEW: change encoding order ---- (A => B) => C to A => (B => C )
    for (idx, e) in es.iter().enumerate() {
        if idx == 0 {
            chained_vec.push(chained_e.clone());
        } else {
            chained_e = mk_imply_traced(&chained_e.e, e);
            chained_vec.push(chained_e.clone());
        }
    }
    Arc::new(chained_vec)
}

// Note: this splitting referenced Dafny - https://github.com/dafny-lang/dafny/blob/cf285b9282499c46eb24f05c7ecc7c72423cd878/Source/Dafny/Verifier/Translator.cs#L11100
pub(crate) fn split_expr(ctx: &Ctx, state: &State, exp: &TracedExp, negated: bool) -> TracedExps {
    match *exp.e.typ {
        TypX::Bool => (),
        _ => {
            panic!("internal error: attempt to split non-boolean expression");
        }
    }
    match &exp.e.x {
        ExpX::Unary(UnaryOp::Not, e1) => {
            let tr_exp = TracedExpX::new(e1.clone(), exp.trace.clone());
            return split_expr(ctx, state, &tr_exp, !negated);
        }
        ExpX::Binary(bop, e1, e2) => {
            match bop {
                BinaryOp::And if !negated => {
                    let es1 = split_expr(
                        ctx,
                        state,
                        &TracedExpX::new(e1.clone(), exp.trace.clone()),
                        false,
                    );
                    let es2 = split_expr(
                        ctx,
                        state,
                        &TracedExpX::new(e2.clone(), exp.trace.clone()),
                        false,
                    );
                    // instead of `A && B` to [A,B], use [A, A=>B]
                    let es1 = mk_chained_implies(es1);
                    let es2 = mk_chained_implies(es2);
                    let es2 = Arc::new(es2.iter().map(|e| mk_imply_traced(e1, e)).collect());
                    return merge_two_es(es1, es2);
                }
                BinaryOp::Or if negated => {
                    // apply DeMorgan's Law
                    let es1 = split_expr(
                        ctx,
                        state,
                        &TracedExpX::new(e1.clone(), exp.trace.clone()),
                        true,
                    );
                    let es2 = split_expr(
                        ctx,
                        state,
                        &TracedExpX::new(e2.clone(), exp.trace.clone()),
                        true,
                    );
                    // now `Or` is changed to `And`
                    // instead of `A && B` to [A,B], use [A, A=>B]
                    let es1 = mk_chained_implies(es1);
                    let es2 = mk_chained_implies(es2);
                    let e1 = SpannedTyped::new(
                        &e1.span,
                        &Arc::new(TypX::Bool),
                        ExpX::Unary(UnaryOp::Not, e1.clone()),
                    ); // negate e1
                    let es2 = Arc::new(es2.iter().map(|e| mk_imply_traced(&e1, e)).collect());
                    return merge_two_es(es1, es2);
                }
                // split rhs (e.g.  A => (B && C)  to  (A => B) && (A => C) )
                BinaryOp::Implies if !negated => {
                    let es2 = split_expr(
                        ctx,
                        state,
                        &TracedExpX::new(e2.clone(), exp.trace.clone()),
                        false,
                    );
                    let mut splitted: Vec<TracedExp> = vec![];
                    for e in &*es2 {
                        let new_e = ExpX::Binary(BinaryOp::Implies, e1.clone(), e.e.clone());
                        let new_exp = SpannedTyped::new(&e.e.span, &exp.e.typ, new_e);
                        let new_tr_exp = TracedExpX::new(new_exp, e.trace.clone());
                        splitted.push(new_tr_exp);
                    }
                    return Arc::new(splitted);
                }
                // split lhs (e.g. !((A && B) => C) to !(A=>C) && !(B=>C) )
                // REVIEW: is this actually useful?
                BinaryOp::Implies if negated => {
                    let es1 = split_expr(
                        ctx,
                        state,
                        &TracedExpX::new(e1.clone(), exp.trace.clone()),
                        false, // instead of pushing negation, wrap negation outside
                    );
                    let mut splitted: Vec<TracedExp> = vec![];
                    for e in &*es1 {
                        let new_e = ExpX::Binary(BinaryOp::Implies, e.e.clone(), e2.clone());
                        let new_exp = SpannedTyped::new(&e.e.span, &exp.e.typ, new_e);
                        let new_tr_exp = TracedExpX::new(new_exp, e.trace.clone());
                        splitted.push(negate_atom(new_tr_exp)); // negate here
                    }
                    return Arc::new(splitted);
                }
                _ => return mk_atom(exp.clone(), negated),
            }
        }
        ExpX::Call(fun_name, _typs, exps) => {
            let fun = get_function(ctx, &exp.e.span, fun_name).unwrap();
            let res_inlined_exp = tr_inline_function(ctx, state, fun, exps, &exp.e.span);
            match res_inlined_exp {
                Ok(inlined_exp) => {
                    let inlined_tr_exp = TracedExpX::new(
                        inlined_exp,
                        exp.trace.secondary_label(&exp.e.span, "from this function call"),
                    );
                    return split_expr(ctx, state, &inlined_tr_exp, negated);
                }
                Err((sp, msg)) => {
                    // if the function inlining failed, treat as atom
                    let not_inlined_exp =
                        TracedExpX::new(exp.e.clone(), exp.trace.secondary_label(&sp, msg));
                    return mk_atom(not_inlined_exp, negated);
                }
            }
        }
        ExpX::If(e1, e2, e3) if !negated => {
            let then_e = ExpX::Binary(BinaryOp::Implies, e1.clone(), e2.clone());
            let then_exp = SpannedTyped::new(&e2.span, &exp.e.typ, then_e);

            let not_e1 =
                SpannedTyped::new(&e1.span, &exp.e.typ, ExpX::Unary(UnaryOp::Not, e1.clone()));
            let else_e = ExpX::Binary(BinaryOp::Implies, not_e1, e3.clone());
            let else_exp = SpannedTyped::new(&e3.span, &exp.e.typ, else_e);

            let es1 = split_expr(
                ctx,
                state,
                &TracedExpX::new(then_exp.clone(), exp.trace.clone()),
                negated,
            );
            let es2 = split_expr(
                ctx,
                state,
                &TracedExpX::new(else_exp.clone(), exp.trace.clone()),
                negated,
            );
            return merge_two_es(es1, es2);
        }
        ExpX::UnaryOpr(uop, e1) => {
            match uop {
                crate::ast::UnaryOpr::Box(_) | crate::ast::UnaryOpr::Unbox(_) => (),
                crate::ast::UnaryOpr::HasType(_)
                | crate::ast::UnaryOpr::IsVariant { .. }
                | crate::ast::UnaryOpr::TupleField { .. }
                | crate::ast::UnaryOpr::Field(_) => return mk_atom(exp.clone(), negated),
            }
            let es1 =
                split_expr(ctx, state, &TracedExpX::new(e1.clone(), exp.trace.clone()), negated);
            let mut splitted: Vec<TracedExp> = vec![];
            for e in &*es1 {
                let new_e = ExpX::UnaryOpr(uop.clone(), e.e.clone());
                let new_exp = SpannedTyped::new(&e.e.span, &exp.e.typ, new_e);
                let new_tr_exp = TracedExpX::new(new_exp.clone(), e.trace.clone());
                splitted.push(new_tr_exp);
            }
            return Arc::new(splitted);
        }
        ExpX::Bind(bnd, e1) => {
            let new_bnd = match &bnd.x {
                BndX::Let(..) if !negated => bnd.clone(),
                // TODO(channy1413): split quantifiers
                _ => return mk_atom(exp.clone(), negated),
            };
            let es1 =
                split_expr(ctx, state, &TracedExpX::new(e1.clone(), exp.trace.clone()), negated);
            let mut splitted: Vec<TracedExp> = vec![];
            for e in &*es1 {
                let new_expx = ExpX::Bind(new_bnd.clone(), e.e.clone());
                let new_exp = SpannedTyped::new(&e.e.span, &exp.e.typ, new_expx);
                let new_tr_exp = TracedExpX::new(new_exp, e.trace.clone());
                splitted.push(new_tr_exp);
            }
            return Arc::new(splitted);
        }
        // cases that cannot be splitted. "atom" boolean expressions
        _ => return mk_atom(exp.clone(), negated),
    }
}

pub(crate) fn register_splitted_assertions(traced_exprs: TracedExps) -> Vec<Stm> {
    let mut stms: Vec<Stm> = Vec::new();
    if traced_exprs.len() == 1 && traced_exprs[0].trace.labels.len() == 0 {
        // if the length of the vector is 1, this indicate split failure
        // however, if this includes message like "this function is opaque",
        // if is worth reporting to the user
        return vec![];
    }
    for small_exp in &*traced_exprs {
        let new_error = small_exp.trace.primary_span(&small_exp.e.span);
        let additional_assert = StmX::Assert(Some(new_error), small_exp.e.clone());
        stms.push(Spanned::new(small_exp.e.span.clone(), additional_assert));
    }
    stms
}

pub(crate) fn need_split_expression(ctx: &Ctx, span: &Span) -> bool {
    for err in &*ctx.debug_expand_targets {
        if err.msg == crate::def::POSTCONDITION_FAILURE.to_string() {
            for label in &err.labels {
                if label.msg == crate::def::THIS_POST_FAILED.to_string() {
                    if label.span.as_string == span.as_string {
                        return true;
                    }
                }
            }
        } else {
            for sp in &err.spans {
                // REVIEW: is this string matching desirable?
                if sp.as_string == span.as_string {
                    return true;
                }
            }
        }
    }
    false
}

// check if this error is generated from splitting
pub fn is_split_error(error: &Error) -> bool {
    if error.msg == crate::def::SPLIT_ASSERT_FAILURE {
        true
    } else if error.msg == crate::def::SPLIT_PRE_FAILURE {
        true
    } else if error.msg == crate::def::SPLIT_POST_FAILURE {
        true
    } else {
        false
    }
}
