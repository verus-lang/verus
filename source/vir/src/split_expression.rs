use crate::ast::{
    BinaryOp, Fun, Function, Params, Quant, SpannedTyped, Typ, TypX, Typs, UnaryOp, UnaryOpr,
    VarIdent, VirErr,
};
use crate::ast_to_sst::get_function;
use crate::context::Ctx;
use crate::def::unique_local;
use crate::def::Spanned;
use crate::func_to_air::{SstInfo, SstMap};
use crate::messages::Message;
use crate::messages::{error, Span};
use crate::sst::{BndX, CallFun, Exp, ExpX, Exps, Pars, Stm, StmX, UniqueVarIdent};
use crate::sst_visitor::map_shallow_stm;
use air::messages::Diagnostics;
use std::collections::HashMap;
use std::sync::Arc;

struct State<'a> {
    fun_ssts: &'a SstMap,
    // Track the status of fuel for each function,
    // since `reveal`, `reveal_with_fuel` can change the fuel locally.
    reveal_map: Vec<HashMap<Fun, u32>>, //  HashMap<Fun, fuel>

    // stuff for postconditions when we encounter an AssertPostCondition
    // note: this is a slightly different form of data than sst_to_air uses
    // for the same purpose
    ensures: &'a Exps,
    ens_pars: &'a Pars,
    dest: Option<UniqueVarIdent>,
}

impl<'a> State<'a> {
    pub fn new(
        fun_ssts: &'a SstMap,
        ensures: &'a Exps,
        ens_pars: &'a Pars,
        dest: Option<UniqueVarIdent>,
    ) -> Self {
        let mut reveal_map = Vec::new();
        reveal_map.push(HashMap::new());
        State { fun_ssts, reveal_map, ensures, ens_pars, dest }
    }

    fn record_fuel(&mut self, x: &Fun, fuel: u32) {
        self.reveal_map.last_mut().expect("reveal_map").insert(x.clone(), fuel);
    }

    pub(crate) fn find_fuel(&self, x: &Fun) -> Option<u32> {
        for rmap in self.reveal_map.iter().rev() {
            if let Some(local_fuel) = rmap.get(x) {
                return Some(*local_fuel);
            }
        }
        None
    }

    // if some expr can contain `proof` block, push and pop around that proof block's translation
    pub(crate) fn push_fuel_scope(&mut self) {
        self.reveal_map.push(HashMap::new());
    }

    pub(crate) fn pop_fuel_scope(&mut self) {
        self.reveal_map.pop();
    }
}

fn is_bool_type(t: &Typ) -> bool {
    match &**t {
        TypX::Bool => true,
        TypX::Boxed(b) => is_bool_type(b),
        _ => false,
    }
}

// This function is to
// 1) inline a function body at a call site
// 2) inline a function's requires expression at a call site
fn inline_expression(
    ctx: &Ctx,
    args: &Exps,
    typs: &Typs,
    params: &Params,
    typ_params: &crate::ast::VarIdents,
    body: &Exp,
) -> Result<Exp, (Span, String)> {
    // code copied from crate::ast_to_sst::finalized_exp
    let mut typ_substs: HashMap<VarIdent, Typ> = HashMap::new();
    let mut substs: HashMap<UniqueVarIdent, Exp> = HashMap::new();
    assert!(typ_params.len() == typs.len());
    for (name, typ) in typ_params.iter().zip(typs.iter()) {
        assert!(!typ_substs.contains_key(name));
        let typ = crate::poly::coerce_typ_to_poly(ctx, typ);
        typ_substs.insert(name.clone(), typ.clone());
    }
    assert!(params.len() == args.len());
    for (param, arg) in params.iter().zip(args.iter()) {
        let unique = unique_local(&param.x.name);
        assert!(!substs.contains_key(&unique));
        substs.insert(unique, arg.clone());
    }
    let e = crate::sst_util::subst_exp(&typ_substs, &substs, body);
    let e = SpannedTyped::new(&body.span, &e.typ, e.x.clone());
    return Ok(e);
}

// Note that errors from `tr_inline_function` will be used by `split_expr`.
// It will be reported to users specifying the reason why the function inlining failed.
fn tr_inline_function(
    ctx: &Ctx,
    state: &State,
    fun_to_inline: Function,
    args: &Exps,
    span: &Span,
    typs: &Typs,
) -> Result<Exp, (Span, String)> {
    let opaque_err = Err((fun_to_inline.span.clone(), "Note: this function is opaque".to_string()));
    let closed_err = Err((
        fun_to_inline.span.clone(),
        "Note: this function is closed at the module boundary".to_string(),
    ));
    let foreign_module_err = Err((
        fun_to_inline.span.clone(),
        "Note: this function is inside a foreign module".to_string(),
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
    match &ctx.fun {
        Some(f) => {
            let fun_owner = get_function(ctx, span, &f.current_fun).unwrap();
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
        if fun_to_inline.x.owning_module.is_none() {
            return foreign_module_err;
        }

        // REVIEW: support trait fn impls?
        let body = match fun_to_inline.x.body.as_ref() {
            Some(body) => body,
            None => {
                return Err((
                    fun_to_inline.span.clone(),
                    format!(
                        "Note: this function is uninterpreted, or is a trait function declaration"
                    ),
                ));
            }
        };
        if !crate::ast_util::is_visible_to_of_owner(&fun_to_inline.x.owning_module, &ctx.module) {
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

        if !is_bool_type(&body.typ) {
            return type_err;
        }

        if fun_to_inline.x.decrease.len() != 0 {
            return Err((
                fun_to_inline.span.clone(),
                format!("Note: this function is recursive with fuel {fuel}"),
            ));
        }
        let fun = &fun_to_inline.x.name;
        let fun_ssts = &state.fun_ssts;
        if let Some(SstInfo { inline, params, body, .. }) = fun_ssts.borrow().get(fun) {
            return inline_expression(ctx, args, typs, params, &inline.typ_params, body);
        } else {
            return Err((fun_to_inline.span.clone(), format!("Note: not found on SstMap")));
        }
    }
}

//  Note that `e` is not the same with the highlighted expression. It is the expression that will be handed to Z3 for verification condition.
//  For example,  A => (B && C) is split into A => B and A => B => C. When A => B => C fails, only C will be highlighted.
//  For details, See BinaryOp::And/OR, `implies`, `If`, `Bind`.
pub type TracedExp = Arc<TracedExpX>;
pub type TracedExps = Arc<Vec<TracedExp>>;
#[derive(Debug)]
pub struct TracedExpX {
    pub e: Exp,                          //  Exp to be discharged to Z3
    pub trace: crate::messages::Message, //  when inlining function, record call stack into `trace`
}
impl TracedExpX {
    pub fn new(e: Exp, trace: crate::messages::Message) -> TracedExp {
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

// Note: this splitting referenced Dafny - https://github.com/dafny-lang/dafny/blob/cf285b9282499c46eb24f05c7ecc7c72423cd878/Source/Dafny/Verifier/Translator.cs#L11100
fn split_expr(
    ctx: &Ctx,
    state: &State,
    exp: &TracedExp,
    negated: bool,
    depth: usize,
) -> TracedExps {
    if !is_bool_type(&exp.e.typ) {
        panic!("internal error: attempt to split non-boolean expression");
    }

    match &exp.e.x {
        ExpX::Unary(UnaryOp::Not, e1) => {
            let tr_exp = TracedExpX::new(e1.clone(), exp.trace.clone());
            return split_expr(ctx, state, &tr_exp, !negated, depth);
        }
        ExpX::Binary(bop, e1, e2) => {
            match bop {
                BinaryOp::And if !negated => {
                    let es1 = split_expr(
                        ctx,
                        state,
                        &TracedExpX::new(e1.clone(), exp.trace.clone()),
                        false,
                        depth,
                    );
                    let es2 = split_expr(
                        ctx,
                        state,
                        &TracedExpX::new(e2.clone(), exp.trace.clone()),
                        false,
                        depth,
                    );
                    // instead of `A && B` to [A,B], use [A, A=>B]
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
                        depth,
                    );
                    let es2 = split_expr(
                        ctx,
                        state,
                        &TracedExpX::new(e2.clone(), exp.trace.clone()),
                        true,
                        depth,
                    );
                    // now `Or` is changed to `And`
                    // instead of `A && B` to [A,B], use [A, A=>B]
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
                        depth,
                    );
                    let mut split_traced: Vec<TracedExp> = vec![];
                    for e in &*es2 {
                        let new_e = ExpX::Binary(BinaryOp::Implies, e1.clone(), e.e.clone());
                        let new_exp = SpannedTyped::new(&e.e.span, &exp.e.typ, new_e);
                        let new_tr_exp = TracedExpX::new(new_exp, e.trace.clone());
                        split_traced.push(new_tr_exp);
                    }
                    return Arc::new(split_traced);
                }
                // split lhs (e.g. !((A && B) => C) to !(A=>C) && !(B=>C) )
                // REVIEW: is this actually useful?
                BinaryOp::Implies if negated => {
                    let es1 = split_expr(
                        ctx,
                        state,
                        &TracedExpX::new(e1.clone(), exp.trace.clone()),
                        false, // instead of pushing negation, wrap negation outside
                        depth,
                    );
                    let mut split_traced: Vec<TracedExp> = vec![];
                    for e in &*es1 {
                        let new_e = ExpX::Binary(BinaryOp::Implies, e.e.clone(), e2.clone());
                        let new_exp = SpannedTyped::new(&e.e.span, &exp.e.typ, new_e);
                        let new_tr_exp = TracedExpX::new(new_exp, e.trace.clone());
                        split_traced.push(negate_atom(new_tr_exp)); // negate here
                    }
                    return Arc::new(split_traced);
                }
                _ => return mk_atom(exp.clone(), negated),
            }
        }
        ExpX::Call(CallFun::Fun(fun_name, _), typs, args) => {
            if depth == 1 {
                return mk_atom(exp.clone(), negated);
            }

            let fun = get_function(ctx, &exp.e.span, fun_name).unwrap();
            let res_inlined_exp = tr_inline_function(ctx, state, fun, args, &exp.e.span, typs);
            match res_inlined_exp {
                Ok(inlined_exp) => {
                    let inlined_tr_exp = TracedExpX::new(
                        inlined_exp,
                        exp.trace.secondary_label(&exp.e.span, "from this function call"),
                    );
                    return split_expr(ctx, state, &inlined_tr_exp, negated, depth + 1);
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
                depth,
            );
            let es2 = split_expr(
                ctx,
                state,
                &TracedExpX::new(else_exp.clone(), exp.trace.clone()),
                negated,
                depth,
            );
            return merge_two_es(es1, es2);
        }
        ExpX::UnaryOpr(uop, e1) => match uop {
            UnaryOpr::Box(_) | UnaryOpr::Unbox(_) => {
                let es1 = split_expr(
                    ctx,
                    state,
                    &TracedExpX::new(e1.clone(), exp.trace.clone()),
                    negated,
                    depth,
                );
                let mut split_traced: Vec<TracedExp> = vec![];
                for e in &*es1 {
                    let new_e = ExpX::UnaryOpr(uop.clone(), e.e.clone());
                    let new_exp = SpannedTyped::new(&e.e.span, &exp.e.typ, new_e);
                    let new_tr_exp = TracedExpX::new(new_exp.clone(), e.trace.clone());
                    split_traced.push(new_tr_exp);
                }
                return Arc::new(split_traced);
            }
            UnaryOpr::CustomErr(msg) => {
                let traced_exp =
                    TracedExpX::new(e1.clone(), exp.trace.secondary_label(&exp.e.span, &**msg));
                return split_expr(ctx, state, &traced_exp, negated, depth);
            }
            UnaryOpr::HasType(_)
            | UnaryOpr::IntegerTypeBound(..)
            | UnaryOpr::IsVariant { .. }
            | UnaryOpr::TupleField { .. }
            | UnaryOpr::Field(_) => {
                return mk_atom(exp.clone(), negated);
            }
        },
        ExpX::Bind(bnd, e1) => {
            if matches!(&bnd.x, BndX::Quant(..)) && depth == 1 {
                return mk_atom(exp.clone(), negated);
            }
            let new_bnd = match &bnd.x {
                BndX::Let(..) if !negated => bnd.clone(), // REVIEW: Can we support `Let` in negated position?
                BndX::Quant(Quant { quant: air::ast::Quant::Forall }, _, _trigs) if !negated => {
                    bnd.clone()
                }
                // REVIEW: is this actually useful?
                BndX::Quant(Quant { quant: air::ast::Quant::Exists }, bndrs, expr_in)
                    if negated =>
                {
                    let new_bndx = BndX::Quant(
                        Quant { quant: air::ast::Quant::Forall },
                        bndrs.clone(),
                        expr_in.clone(),
                    );
                    Spanned::new(bnd.span.clone(), new_bndx)
                }
                _ => return mk_atom(exp.clone(), negated),
            };

            let es1 = split_expr(
                ctx,
                state,
                &TracedExpX::new(e1.clone(), exp.trace.clone()),
                negated,
                if matches!(&bnd.x, BndX::Quant(..)) { depth + 1 } else { depth },
            );
            let mut split_traced: Vec<TracedExp> = vec![];
            for e in &*es1 {
                let new_expx = ExpX::Bind(new_bnd.clone(), e.e.clone());
                let new_exp = SpannedTyped::new(&e.e.span, &exp.e.typ, new_expx);
                let new_tr_exp = TracedExpX::new(new_exp, e.trace.clone());
                split_traced.push(new_tr_exp);
            }
            return Arc::new(split_traced);
        }
        // cases that cannot be split. "atom" boolean expressions
        _ => return mk_atom(exp.clone(), negated),
    }
}

fn register_split_assertions(traced_exprs: TracedExps) -> Vec<Stm> {
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
        if err.note == crate::def::POSTCONDITION_FAILURE.to_string() {
            for label in &err.labels {
                if label.note == crate::def::THIS_POST_FAILED.to_string() {
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
pub fn is_split_error(error: &Message) -> bool {
    if error.note == crate::def::SPLIT_ASSERT_FAILURE {
        true
    } else if error.note == crate::def::SPLIT_PRE_FAILURE {
        true
    } else if error.note == crate::def::SPLIT_POST_FAILURE {
        true
    } else {
        false
    }
}

fn split_call(
    ctx: &Ctx,
    state: &State,
    diagnostics: &impl Diagnostics,
    span: &Span,
    name: &Fun,
    typs: &Typs,
    args: &Exps,
    error: &Message,
) -> Result<Vec<Stm>, VirErr> {
    let fun = get_function(ctx, span, name)?;
    let mut stms: Vec<Stm> = Vec::new();

    // We split the `requires` expression on the call site.
    // (If we were to split the `requires` expression on the function itself,
    // this split encoding would take effect on every call site, which is not desirable.)
    //
    // Also, note that pervasive::assert consists of `requires` and `ensures`,
    // so we are also splitting pervasive::assert here.
    let params = &fun.x.params;
    let typ_params = &fun.x.typ_params;
    for e in &**fun.x.require {
        // skip checks on require, since this is checked when the function is checked
        let exp = crate::ast_to_sst::expr_to_exp_as_spec_skip_checks(
            &ctx,
            diagnostics,
            &state.fun_ssts,
            &crate::func_to_air::params_to_pars(params, true), // REVIEW: is `true` here desirable?
            &e,
        )
        .expect("expr_to_exp_as_spec_skip_checks");

        // In requires, old(x) is really just x:
        let mut f_var_at = |e: &Exp| match &e.x {
            ExpX::VarAt(x, crate::ast::VarAt::Pre) => e.new_x(ExpX::Var(x.clone())),
            _ => e.clone(),
        };
        let exp = crate::sst_visitor::map_exp_visitor(&exp, &mut f_var_at);
        let exp_subsituted = inline_expression(ctx, args, typs, params, typ_params, &exp);
        if exp_subsituted.is_err() {
            continue;
        }
        let exp_subsituted = exp_subsituted.unwrap();
        // REVIEW: should we simply use SPLIT_ASSERT_FAILURE?
        let exprs = split_expr(
            ctx,
            &state,
            &TracedExpX::new(exp_subsituted.clone(), error.clone()),
            false,
            0,
        );
        stms.extend(register_split_assertions(exprs).into_iter());
    }
    Ok(stms)
}

fn visit_split_stm(
    ctx: &Ctx,
    state: &mut State,
    diagnostics: &impl Diagnostics,
    stm: &Stm,
) -> Result<Stm, VirErr> {
    match &stm.x {
        StmX::Assert(_err, e1) => {
            if need_split_expression(ctx, &stm.span) {
                let error = error(&stm.span, crate::def::SPLIT_ASSERT_FAILURE);
                let split_exprs = split_expr(
                    ctx,
                    &state, // use the state after `body` translation to get the fuel info
                    &TracedExpX::new(e1.clone(), error),
                    false,
                    0,
                );
                let stms = register_split_assertions(split_exprs);
                Ok(Spanned::new(stm.span.clone(), StmX::Block(Arc::new(stms))))
            } else {
                Ok(stm.clone())
            }
        }
        StmX::Return { base_error: _, ret_exp, inside_body: _ } => {
            let split_stms = if state.ensures.len() == 0 {
                vec![]
            } else {
                let mut stms = if let Some(dest_id) = state.dest.clone() {
                    let ret_exp =
                        ret_exp.as_ref().expect("if dest is provided, expr must be provided");
                    vec![crate::sst_to_air::assume_var(&stm.span, &dest_id, ret_exp)]
                } else {
                    vec![]
                };

                for e in state.ensures.iter() {
                    if need_split_expression(ctx, &e.span) {
                        let error = error(&e.span, crate::def::SPLIT_POST_FAILURE);
                        let split_exprs = split_expr(
                            ctx,
                            &state, // use the state after `body` translation to get the fuel info
                            &TracedExpX::new(e.clone(), error.clone()),
                            false,
                            0,
                        );
                        stms.extend(register_split_assertions(split_exprs));
                    }
                }
                stms
            };
            Ok(crate::ast_to_sst::stms_to_one_stm(&stm.span, split_stms))
        }
        StmX::Call { fun, typ_args, args, split: Some(error), dest: None, .. } => {
            let stms = split_call(ctx, state, diagnostics, &stm.span, fun, typ_args, args, error)?;
            Ok(Spanned::new(stm.span.clone(), StmX::Block(Arc::new(stms))))
        }
        StmX::Fuel(x, fuel) => {
            state.record_fuel(x, *fuel);
            Ok(stm.clone())
        }
        StmX::DeadEnd(s) => {
            state.push_fuel_scope();
            let s = visit_split_stm(ctx, state, diagnostics, s)?;
            state.pop_fuel_scope();
            Ok(Spanned::new(stm.span.clone(), StmX::DeadEnd(s)))
        }
        StmX::If(cond, lhs, rhs) => {
            state.push_fuel_scope();
            let lhs = visit_split_stm(ctx, state, diagnostics, lhs)?;
            state.pop_fuel_scope();
            state.push_fuel_scope();
            let rhs = rhs
                .as_ref()
                .map(|rhs| visit_split_stm(ctx, state, diagnostics, rhs))
                .transpose()?;
            state.pop_fuel_scope();
            Ok(Spanned::new(stm.span.clone(), StmX::If(cond.clone(), lhs, rhs)))
        }
        StmX::Loop { is_for_loop, label, cond, body, invs, typ_inv_vars, modified_vars } => {
            let cond = if let Some((cond_stm, cond_exp)) = cond {
                let cond_stm = visit_split_stm(ctx, state, diagnostics, cond_stm)?;
                Some((cond_stm, cond_exp.clone()))
            } else {
                None
            };
            let mut body_state =
                State::new(&state.fun_ssts, &state.ensures, &state.ens_pars, state.dest.clone());
            let body = visit_split_stm(ctx, &mut body_state, diagnostics, body)?;
            Ok(Spanned::new(
                stm.span.clone(),
                StmX::Loop {
                    is_for_loop: *is_for_loop,
                    label: label.clone(),
                    cond,
                    body,
                    invs: invs.clone(),
                    typ_inv_vars: typ_inv_vars.clone(),
                    modified_vars: modified_vars.clone(),
                },
            ))
        }
        _ => map_shallow_stm(stm, &mut |s| visit_split_stm(ctx, state, diagnostics, s)),
    }
}

pub(crate) fn all_split_exp(
    ctx: &Ctx,
    diagnostics: &impl Diagnostics,
    fun_ssts: &SstMap,
    stm: &Stm,
    ensures: &Exps,
    ens_pars: &Pars,
    dest: Option<UniqueVarIdent>,
) -> Result<Stm, VirErr> {
    let mut state = State::new(fun_ssts, ensures, ens_pars, dest);
    map_shallow_stm(stm, &mut |s| visit_split_stm(ctx, &mut state, diagnostics, s))
}
