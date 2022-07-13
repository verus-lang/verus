use crate::ast::{BinaryOp, Expr, Function, Params, Quant, SpannedTyped, Typ, TypX, UnaryOp};
use crate::ast_to_sst::{get_function, State};
use crate::context::Ctx;
use crate::def::Spanned;
use crate::sst::{Bnd, BndX, Exp, ExpX, Exps, Stm, StmX};
use air::ast::{Binder, BinderX, Span};
use core::panic;
use std::collections::HashMap;
use std::sync::Arc;

fn subsitute_argument(
    exp: &Exp,
    arg_map: &HashMap<Arc<String>, Exp>,
) -> Result<Exp, (Span, String)> {
    let result = match &exp.x {
        ExpX::Var((id, _num)) => {
            // println!("id: {:?}", id);
            match arg_map.get(id) {
                Some(e) => e.clone(),
                None => exp.clone(),
            }
        }
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
            // TODO: check if binded name and  `var to replace` is same
            let e1_replaced = subsitute_argument(e1, arg_map)?;
            let bnd_replaced: Bnd = match &bnd.x {
                BndX::Let(binders) => {
                    let mut new_binders: Vec<Binder<Exp>> = vec![];
                    for old_b in &**binders {
                        let new_b = BinderX {
                            name: old_b.name.clone(),
                            a: subsitute_argument(&old_b.a, arg_map)?,
                        };
                        new_binders.push(Arc::new(new_b));
                    }
                    Spanned::new(bnd.span.clone(), BndX::Let(Arc::new(new_binders)))
                }
                BndX::Quant(quant, bndrs, trigs) => {
                    // replace vars in trigger
                    let mut replaced_trigs: Vec<crate::sst::Trig> = vec![];
                    for ts in &***trigs {
                        let mut replaced_ts: Vec<Exp> = vec![];
                        for t in &**ts {
                            replaced_ts.push(subsitute_argument(t, arg_map)?);
                        }
                        replaced_trigs.push(Arc::new(replaced_ts));
                    }
                    Spanned::new(
                        bnd.span.clone(),
                        BndX::Quant(quant.clone(), bndrs.clone(), Arc::new(replaced_trigs)),
                    )
                }
                _ => return Err((exp.span.clone(), format!("TODO: binders, subsitute_argument"))),
            };
            let new_exp = ExpX::Bind(bnd_replaced, e1_replaced);
            SpannedTyped::new(&exp.span, &exp.typ, new_exp)
        }
        ExpX::Const(_) => exp.clone(),
        _ => {
            // | ExpX::WithTriggers(_, _) => exp.clone()
            // VarLoc(UniqueIdent),
            // VarAt(UniqueIdent, VarAt),
            // Loc(Exp),
            // Old(Ident, UniqueIdent),
            // CallLambda(Typ, Exp, Exps),
            // Ctor(Path, Ident, Binders<Exp>),
            // WithTriggers(Trigs, Exp),
            return Err((exp.span.clone(), format!("TODO: unsubsituted exp, subsitute_argument ")));
        }
    };
    Ok(result)
}

// e1: param, e2: exp_to_replace
fn assert_same_type(param_typ: &Typ, e2: &Exp) -> Result<(), (Span, String)> {
    match (&**param_typ, &*e2.typ) {
        (TypX::Bool, TypX::Bool) |
        (TypX::Int(_),TypX::Int(_)) |
        (TypX::Tuple(_), TypX::Tuple(_)) |
        (TypX::Lambda(_, _), TypX::Lambda(_,_)) |
        (TypX::Datatype(_, _), TypX::Datatype(_,_)) |
        // TODO: recursive check instead
        (TypX::Boxed(_), TypX::Boxed(_)) |
        (TypX::TypParam(_), TypX::TypParam(_)) |
        (TypX::TypeId, TypX::TypeId) |
        (TypX::Air(_), TypX::Air(_)) => Ok(()),
        _ => return Err((e2.span.clone(), "TODO or interal error: arg type mismatch during function inlining".to_string())),
    }
}
pub(crate) fn tr_inline_expression(
    body_exp: &Exp,
    params: &Params,
    exps: &Exps,
) -> Result<Exp, (Span, String)> {
    let mut arg_map: HashMap<Arc<String>, Exp> = HashMap::new();
    let mut count = 0;
    for param in &**params {
        let exp_to_insert = &exps[count];
        assert_same_type(&param.x.typ, exp_to_insert)?;
        arg_map.insert(param.x.name.clone(), exp_to_insert.clone());
        count = count + 1;
    }
    return subsitute_argument(body_exp, &arg_map);
}

// TODO: see if I can use `expr_to_exp_as_spec` instead of below one
pub(crate) fn pure_ast_expression_to_sst(ctx: &Ctx, body: &Expr, params: &Params) -> Exp {
    // let pars = crate::func_to_air::params_to_pars(params, false);
    // let mut state = crate::ast_to_sst::State::new();
    // state.declare_params(&pars);
    // state.view_as_spec = true;
    // let body_exp = expr_to_pure_exp(&ctx, &mut state, &body).expect("pure_ast_expression_to_sst");
    // state.finalize_exp(&body_exp)
    crate::ast_to_sst::expr_to_exp_as_spec(
        &ctx,
        &crate::func_to_air::params_to_pars(params, false),
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
    // TODO: recursive function inline. don't inline
    let opaque_err = Err((fun_to_inline.span.clone(), "Note: this function is opaque".to_string()));
    let closed_err = Err((
        fun_to_inline.span.clone(),
        "Note: this function is closed at the module boundary".to_string(),
    ));
    let foriegn_module_err = Err((
        fun_to_inline.span.clone(),
        "Note: this function is inside a foriegn module".to_string(),
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
        None => (), // should I panic instead?
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
        let params = &fun_to_inline.x.params;
        let body_exp = pure_ast_expression_to_sst(ctx, body, params);
        return tr_inline_expression(&body_exp, params, exps);
    }
}

// trace
// 1) when inlining function, log call stack into `trace`
// 2) boolean negation
pub type TracedExp = Arc<TracedExpX>;
pub type TracedExps = Arc<Vec<TracedExp>>;
pub struct TracedExpX {
    pub e: Exp,
    pub trace: air::errors::Error,
}
impl TracedExpX {
    pub fn new(e: Exp, trace: air::errors::Error) -> TracedExp {
        Arc::new(TracedExpX { e, trace })
    }
}

fn negate_atom(exp: TracedExp) -> TracedExp {
    let negated_expx = ExpX::Unary(UnaryOp::Not, exp.e.clone());
    let negated_exp = SpannedTyped::new(&exp.e.span, &exp.e.typ, negated_expx);
    TracedExpX::new(negated_exp, exp.trace.clone())
}

macro_rules! return_atom {
    ($e:expr, $negated:expr) => {
        if $negated {
            return Arc::new(vec![negate_atom($e)]);
        } else {
            return Arc::new(vec![$e]);
        }
    };
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

// Note: this splitting referenced Dafny
// https://github.com/dafny-lang/dafny/blob/cf285b9282499c46eb24f05c7ecc7c72423cd878/Source/Dafny/Verifier/Translator.cs#L11100
pub(crate) fn split_expr(ctx: &Ctx, state: &State, exp: &TracedExp, negated: bool) -> TracedExps {
    match *exp.e.typ {
        TypX::Bool => (),
        _ => panic!("cannot split non boolean expression"),
    }
    match &exp.e.x {
        ExpX::Unary(UnaryOp::Not, e1) => {
            let tr_exp = TracedExpX::new(
                e1.clone(),
                exp.trace.secondary_label(
                    &exp.e.span,
                    "This leftmost boolean-not negated the highlighted expression",
                ),
            );
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
                    return merge_two_es(es1, es2);
                }
                // apply DeMorgan's Law
                BinaryOp::Or if negated => {
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
                    return merge_two_es(es1, es2);
                }
                // in case of implies, split rhs. (e.g.  A => (B && C)  to  [ (A => B) , (A => C) ] )
                BinaryOp::Implies if !negated => {
                    let es2 = split_expr(
                        ctx,
                        state,
                        &TracedExpX::new(e2.clone(), exp.trace.clone()),
                        negated,
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
                // TODO
                // BinaryOp::Implies if negated
                _ => return_atom!(exp.clone(), negated),
            }
        }
        ExpX::Call(fun_name, _typs, exps) => {
            let fun = get_function(ctx, &exp.e.span, fun_name).unwrap();
            // println!("{:?}", &fun.span.as_string);
            // println!("{:?}", exps[0].span.as_string);
            let res_inlined_exp = tr_inline_function(ctx, state, fun, exps, &exp.e.span);
            match res_inlined_exp {
                Ok(inlined_exp) => {
                    // println!("inlined exp: {:?}", inlined_exp);
                    let inlined_tr_exp = TracedExpX::new(
                        inlined_exp,
                        exp.trace.secondary_label(&exp.e.span, "inlining this function call"), // TODO: pretty print inlined expr
                    );
                    return split_expr(ctx, state, &inlined_tr_exp, negated);
                }
                Err((sp, msg)) => {
                    println!("inline failed for {:?}", fun_name);
                    let not_inlined_exp =
                        TracedExpX::new(exp.e.clone(), exp.trace.secondary_label(&sp, msg));
                    // stop inlining. treat as atom
                    return_atom!(not_inlined_exp, negated);
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
            let es1 =
                split_expr(ctx, state, &TracedExpX::new(e1.clone(), exp.trace.clone()), negated);
            let mut splitted: Vec<TracedExp> = vec![];
            for e in &*es1 {
                let new_e = ExpX::UnaryOpr(uop.clone(), e.e.clone());
                let new_exp = SpannedTyped::new(&e.e.span, &exp.e.typ, new_e);
                let new_tr_exp = TracedExpX::new(new_exp, e.trace.clone());
                splitted.push(new_tr_exp);
            }
            return Arc::new(splitted);
        }
        ExpX::Bind(bnd, e1) => {
            // TODO: split on `exists` when negated
            // TODO: Lambda, Choose
            // split on `forall` when !neagted,
            match bnd.x {
                BndX::Quant(Quant { quant: air::ast::Quant::Forall, boxed_params: _ }, _, _)
                    if !negated =>
                {
                    ()
                }
                BndX::Let(..) => (),
                _ => return_atom!(exp.clone(), negated),
            };
            let es1 =
                split_expr(ctx, state, &TracedExpX::new(e1.clone(), exp.trace.clone()), negated);
            let mut splitted: Vec<TracedExp> = vec![];
            for e in &*es1 {
                // REVIEW: should I split expression in `let sth = exp`?
                let new_expx = ExpX::Bind(bnd.clone(), e.e.clone());
                let new_exp = SpannedTyped::new(&e.e.span, &exp.e.typ, new_expx);
                let new_tr_exp = TracedExpX::new(new_exp, e.trace.clone());
                splitted.push(new_tr_exp);
            }
            return Arc::new(splitted);
        }

        // TODO: more cases

        // cases that cannot be splitted. "atom" boolean expressions
        _ => return_atom!(exp.clone(), negated),
    }
}

pub(crate) fn register_splitted_assertions(traced_exprs: TracedExps) -> Vec<Stm> {
    // maybe check some condition here before registering every small exps
    let mut stms: Vec<Stm> = Vec::new();
    for small_exp in &*traced_exprs {
        let new_error = small_exp.trace.primary_span(&small_exp.e.span);
        let additional_assert = StmX::Assert(Some(new_error), small_exp.e.clone());
        stms.push(Spanned::new(small_exp.e.span.clone(), additional_assert));
    }
    stms
}

pub(crate) fn need_split_expression(ctx: &Ctx, span: &Span) -> bool {
    for err in &*ctx.debug_expand_targets {
        // println!("target error msg: {:?}", err.msg);
        // TODO: make this message in a def.rs somewhere
        if err.msg == "postcondition not satisfied".to_string() {
            for label in &err.labels {
                // println!("label msg {:?}", label.msg);
                // println!("label span {:?}", label.span);
                if label.msg == "failed this postcondition".to_string() {
                    if label.span.as_string == span.as_string {
                        return true;
                    }
                }
            }
        } else {
            for sp in &err.spans {
                // println!("error span: {:?}", sp);
                // TODO: is this string matching desirable??
                if sp.as_string == span.as_string {
                    return true;
                }
            }
        }
    }
    // println!("chose not to split. query span: {:?}", span);
    false
}
