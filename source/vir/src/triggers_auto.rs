use crate::ast::{
    BinaryOp, BitwiseOp, Constant, FieldOpr, Fun, Ident, Path, Typ, TypX, UnaryOp, UnaryOpr, VarAt,
    VirErr,
};
use crate::ast_util::{err_str, path_as_rust_name};
use crate::context::{ChosenTriggers, Ctx, FunctionCtx};
use crate::sst::{Exp, ExpX, Trig, Trigs, UniqueIdent};
use crate::util::vec_map;
use air::ast::Span;
use std::collections::{HashMap, HashSet};
use std::sync::Arc;

/*
This trigger selection algorithm is experimental and somewhat different from the usual
selection algorithms, such as the algorithm used by Z3 internally.
The goal is to be cautious and avoid triggers that lead to excessive quantifier
instantiations, which could lead to SMT timeouts.

To that end, the algorithm tries to choose only one trigger for any given quantifier,
because multiple triggers lead to more unintended instantiations.
The one "best" trigger is chosen using a rather arbitrary heuristic score.
The algorithm selects multiple triggers only if there is a tie for the first-place score
between multiple candidates.

If the chosen triggers are too conservative,
programmers can always override the decision with manual trigger annotations.
In fact, the hope is that the default triggers will err on the side of avoiding timeouts,
and then programmers can use manual triggers to make the quantifiers more liberal,
rather than the defaults causing timeouts,
and programmers having to use manual triggers to eliminate the timeouts.
*/

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum App {
    Const(Constant),
    Field(Path, Ident, Ident),
    Call(Fun),
    // datatype constructor: (Path, Variant)
    Ctor(Path, Ident),
    // u64 is an id, assigned via a simple counter
    Other(u64),
    VarAt(UniqueIdent, VarAt),
    BitOp(BitOpName),
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum BitOpName {
    BitXor,
    BitAnd,
    BitOr,
    Shr,
    Shl,
    BitNot,
}

type Term = Arc<TermX>;
type Terms = Arc<Vec<Term>>;
#[derive(PartialEq, Eq, Hash)]
enum TermX {
    Var(UniqueIdent),
    App(App, Terms),
}

impl std::fmt::Debug for TermX {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        match self {
            TermX::Var(x) => write!(f, "{}", &x.name),
            TermX::App(App::Const(c), _) => write!(f, "{:?}", c),
            TermX::App(App::Field(_, x, y), es) => write!(f, "{:?}.{}/{}", es[0], x, y),
            TermX::App(c @ (App::Call(_) | App::Ctor(_, _)), es) => {
                match c {
                    App::Call(x) => write!(f, "{}(", path_as_rust_name(&x.path))?,
                    App::Ctor(path, variant) => {
                        write!(f, "{}::{}(", path_as_rust_name(path), variant)?
                    }
                    _ => unreachable!(),
                }
                for i in 0..es.len() {
                    write!(f, "{:?}", es[i])?;
                    if i < es.len() - 1 {
                        write!(f, ", ")?;
                    }
                }
                write!(f, ")")
            }
            TermX::App(App::Other(_), _) => {
                write!(f, "_")
            }
            TermX::App(App::VarAt(x, VarAt::Pre), _) => {
                write!(f, "old({})", &x.name)
            }
            TermX::App(App::BitOp(bop), _) => {
                write!(f, "BitOp: {:?}", bop)
            }
        }
    }
}

/*
First, we prefer triggers containing the fewest number of terms:
- {f(x, y)} (1 term) is better (safer) than {g(x), h(y)} (2 terms)
We choose this because a smaller number of terms leads to fewer quantifier instantiations,
meaning less chance of an SMT timeout.

Second, for triggers that are tied for number of terms, we compute a heuristic score:
- the depth measures how deeply buried the term is inside other terms
  - lower depth is better
  - prefer terms next to logical operators or == rather than arithmetic
  - we actually measure the max depth to the trigger variables in the term
    rather than to the term itself -- otherwise, in f(g(x)),
    the term g(x) would be considered higher depth than f(g(x)),
    and this would bias the decision towards large terms,
    while we actually prefer small terms
- the size measures how large a term is
  - smaller size is better
- terms that contain a function call are better than terms with just constructors and fields
  - (avoid choosing something like Option::Some(x) as the trigger)
We choose these because they are likely to identify relevant terms
such as function definitions f(x, y) == ... or implication f(x, y) ==> ...
rather than terms used incidentally inside other terms.

Obviously, these are fairly arbitrary criteria, but the goal is to make *some* choice,
rather than just selecting all the candidate triggers.

REVIEW: these heuristics are experimental -- are they useful in practice?  Can they be improved?
*/

// Score for a single term in a trigger.
// Can be summed to compute a total score for all terms in a trigger
// (lower scores are better)
struct Score {
    // number of bitwise operators
    num_operators: u64,
    // 0 means term has function calls
    // 1 means term has no function calls (only constructors, fields, operators)
    no_calls: u64,
    // 1 or more, or 0 for next to ==
    depth: u64,
    // total size of term
    size: u64,
}

impl Score {
    // lower score is better (lexicographically ordered)
    fn lex(&self) -> (u64, u64, u64, u64) {
        (self.num_operators, self.no_calls, self.depth, self.size)
    }
}

struct Ctxt {
    // variables the triggers must cover
    trigger_vars: HashSet<Ident>,
    // terms with App
    all_terms: HashMap<Term, Span>,
    // terms with App and without Other
    // The usize is used to sort the terms in the triggers for better stability
    pure_terms: HashMap<Term, (Exp, usize)>,
    // all_terms, indexed by head App
    all_terms_by_app: HashMap<App, HashMap<Term, Span>>,
    // pure_terms, indexed by trigger_vars
    pure_terms_by_var: HashMap<Ident, HashMap<Term, Span>>,
    // best score for this term
    pure_best_scores: HashMap<Term, Score>,
    // used for Other
    next_id: u64,
}

impl Ctxt {
    fn other(&mut self) -> App {
        self.next_id += 1;
        App::Other(self.next_id)
    }
}

struct Timer {
    // span of entire quantifier
    span: Span,
    // algorithms are exponential, so give up rather than taking too long
    timeout_countdown: u64,
}

fn check_timeout(timer: &mut Timer) -> Result<(), VirErr> {
    if timer.timeout_countdown == 0 {
        err_str(
            &timer.span,
            "could not infer triggers, because quantifier is too large (use manual #[trigger] instead)",
        )
    } else {
        timer.timeout_countdown -= 1;
        Ok(())
    }
}

fn trigger_vars_in_term(ctxt: &Ctxt, vars: &mut HashSet<Ident>, term: &Term) {
    match &**term {
        TermX::Var(UniqueIdent { name: x, local: None }) if ctxt.trigger_vars.contains(x) => {
            vars.insert(x.clone());
        }
        TermX::Var(..) => {}
        TermX::App(_, args) => {
            for arg in args.iter() {
                trigger_vars_in_term(ctxt, vars, arg);
            }
        }
    }
}

fn term_size(term: &Term) -> u64 {
    match &**term {
        TermX::Var(..) => 1,
        TermX::App(_, args) => 1 + args.iter().map(term_size).sum::<u64>(),
    }
}

fn trigger_var_depth(ctxt: &Ctxt, term: &Term, depth: u64) -> Option<u64> {
    match &**term {
        TermX::Var(UniqueIdent { name: x, local: None }) if ctxt.trigger_vars.contains(x) => {
            Some(depth)
        }
        TermX::Var(..) => None,
        TermX::App(_, args) => {
            args.iter().filter_map(|t| trigger_var_depth(ctxt, t, depth + 1)).max()
        }
    }
}

fn count_bit_operators(term: &Term) -> u64 {
    match &**term {
        TermX::App(App::BitOp(_), args) => 1 + args.iter().map(count_bit_operators).sum::<u64>(),
        TermX::App(_, args) => args.iter().map(count_bit_operators).sum::<u64>(),
        TermX::Var(..) => 0,
    }
}

fn count_calls(term: &Term) -> u64 {
    match &**term {
        TermX::App(App::Call(_), args) => 1 + args.iter().map(count_calls).sum::<u64>(),
        TermX::App(_, args) => args.iter().map(count_calls).sum::<u64>(),
        TermX::Var(..) => 0,
    }
}

fn make_score(term: &Term, depth: u64) -> Score {
    let no_calls = if count_calls(term) == 0 { 1 } else { 0 };
    Score { num_operators: count_bit_operators(term), no_calls, depth, size: term_size(term) }
}

fn gather_terms(ctxt: &mut Ctxt, ctx: &Ctx, exp: &Exp, depth: u64) -> (bool, Term) {
    let (is_pure, term) = match &exp.x {
        ExpX::Const(c) => (true, Arc::new(TermX::App(App::Const(c.clone()), Arc::new(vec![])))),
        ExpX::Var(x) => (true, Arc::new(TermX::Var(x.clone()))),
        ExpX::VarLoc(..) | ExpX::Loc(..) => panic!("unexpected Loc/VarLoc in quantifier"),
        ExpX::VarAt(x, _) => {
            (true, Arc::new(TermX::App(App::VarAt(x.clone(), VarAt::Pre), Arc::new(vec![]))))
        }
        ExpX::Old(_, _) => panic!("internal error: Old"),
        ExpX::Call(x, typs, args) => {
            let (is_pures, terms): (Vec<bool>, Vec<Term>) =
                args.iter().map(|e| gather_terms(ctxt, ctx, e, depth + 1)).unzip();
            let is_pure = is_pures.into_iter().all(|b| b);
            let mut all_terms: Vec<Term> = Vec::new();
            for typ in typs.iter() {
                let ft = |all_terms: &mut Vec<Term>, t: &Typ| match &**t {
                    TypX::TypParam(x) => {
                        let x = crate::def::unique_bound(&crate::def::suffix_typ_param_id(x));
                        all_terms.push(Arc::new(TermX::Var(x)));
                        Ok(t.clone())
                    }
                    _ => Ok(t.clone()),
                };
                crate::ast_visitor::map_typ_visitor_env(typ, &mut all_terms, &ft).unwrap();
            }
            all_terms.extend(terms);
            match ctx.func_map.get(x) {
                Some(f) if f.x.attrs.no_auto_trigger => {
                    (false, Arc::new(TermX::App(ctxt.other(), Arc::new(all_terms))))
                }
                _ => (is_pure, Arc::new(TermX::App(App::Call(x.clone()), Arc::new(all_terms)))),
            }
        }
        ExpX::CallLambda(_, e0, es) => {
            // REVIEW: maybe we should include CallLambdas in the auto-triggers
            let depth = 1;
            let (_, term0) = gather_terms(ctxt, ctx, e0, depth);
            let mut terms: Vec<Term> =
                es.iter().map(|e| gather_terms(ctxt, ctx, e, depth).1).collect();
            terms.insert(0, term0);
            (false, Arc::new(TermX::App(ctxt.other(), Arc::new(terms))))
        }
        ExpX::Ctor(path, variant, fields) => {
            let (variant, args) = crate::sst_to_air::ctor_to_apply(ctx, path, variant, fields);
            let (is_pures, terms): (Vec<bool>, Vec<Term>) =
                args.map(|e| gather_terms(ctxt, ctx, &e.a, depth + 1)).unzip();
            let is_pure = is_pures.into_iter().all(|b| b);
            (is_pure, Arc::new(TermX::App(App::Ctor(path.clone(), variant), Arc::new(terms))))
        }
        ExpX::Unary(UnaryOp::Trigger(_), e1) => gather_terms(ctxt, ctx, e1, depth),
        ExpX::Unary(UnaryOp::CoerceMode { .. }, e1) => gather_terms(ctxt, ctx, e1, depth),
        ExpX::Unary(UnaryOp::MustBeFinalized, e1) => gather_terms(ctxt, ctx, e1, depth),
        ExpX::Unary(op, e1) => {
            let depth = match op {
                UnaryOp::Not | UnaryOp::CoerceMode { .. } | UnaryOp::MustBeFinalized => 0,
                UnaryOp::Trigger(_) | UnaryOp::Clip(_) | UnaryOp::BitNot => 1,
            };
            let (_, term1) = gather_terms(ctxt, ctx, e1, depth);
            match op {
                UnaryOp::BitNot => (
                    true,
                    Arc::new(TermX::App(App::BitOp(BitOpName::BitNot), Arc::new(vec![term1]))),
                ),
                _ => (false, Arc::new(TermX::App(ctxt.other(), Arc::new(vec![term1])))),
            }
        }
        ExpX::UnaryOpr(UnaryOpr::Box(_), e1) => gather_terms(ctxt, ctx, e1, depth),
        ExpX::UnaryOpr(UnaryOpr::Unbox(_), e1) => gather_terms(ctxt, ctx, e1, depth),
        ExpX::UnaryOpr(UnaryOpr::HasType(_), _) => {
            (false, Arc::new(TermX::App(ctxt.other(), Arc::new(vec![]))))
        }
        ExpX::UnaryOpr(UnaryOpr::IsVariant { .. }, e1) => {
            // We currently don't auto-trigger on IsVariant
            // Even if we did, it might be best not to trigger on IsVariants generated from Match
            let (_, term1) = gather_terms(ctxt, ctx, e1, 1);
            (false, Arc::new(TermX::App(ctxt.other(), Arc::new(vec![term1]))))
        }
        ExpX::UnaryOpr(UnaryOpr::TupleField { .. }, _) => {
            panic!("internal error: TupleField should have been removed before here")
        }
        ExpX::UnaryOpr(UnaryOpr::Field(FieldOpr { datatype, variant, field }), lhs) => {
            let (is_pure, arg) = gather_terms(ctxt, ctx, lhs, depth + 1);
            (
                is_pure,
                Arc::new(TermX::App(
                    App::Field(datatype.clone(), variant.clone(), field.clone()),
                    Arc::new(vec![arg]),
                )),
            )
        }
        ExpX::Binary(op, e1, e2) => {
            use BinaryOp::*;
            let depth = match op {
                And | Or | Xor | Implies | Eq(_) => 0,
                Ne | Inequality(_) | Arith(..) => 1,
                Bitwise(..) => 1,
            };
            let (_, term1) = gather_terms(ctxt, ctx, e1, depth);
            let (_, term2) = gather_terms(ctxt, ctx, e2, depth);
            match op {
                Bitwise(bp) => {
                    let bop = match bp {
                        BitwiseOp::BitXor => BitOpName::BitXor,
                        BitwiseOp::BitAnd => BitOpName::BitAnd,
                        BitwiseOp::Shr => BitOpName::Shr,
                        BitwiseOp::Shl => BitOpName::Shl,
                        BitwiseOp::BitOr => BitOpName::BitOr,
                    };
                    (true, Arc::new(TermX::App(App::BitOp(bop), Arc::new(vec![term1, term2]))))
                }
                _ => (false, Arc::new(TermX::App(ctxt.other(), Arc::new(vec![term1, term2])))),
            }
        }
        ExpX::If(e1, e2, e3) => {
            let depth = 1;
            let (_, term1) = gather_terms(ctxt, ctx, e1, depth);
            let (_, term2) = gather_terms(ctxt, ctx, e2, depth);
            let (_, term3) = gather_terms(ctxt, ctx, e3, depth);
            (false, Arc::new(TermX::App(ctxt.other(), Arc::new(vec![term1, term2, term3]))))
        }
        ExpX::WithTriggers(..) => {
            panic!("shouldn't be inferring triggers for WithTriggers expression")
        }
        ExpX::Bind(_, _) => {
            // REVIEW: we could at least look for matching loops here
            (false, Arc::new(TermX::App(ctxt.other(), Arc::new(vec![]))))
        }
    };
    if let TermX::Var(..) = *term {
        return (is_pure, term);
    }
    if !ctxt.all_terms.contains_key(&term) {
        ctxt.all_terms.insert(term.clone(), exp.span.clone());
        if let TermX::App(app, _) = &*term {
            if !ctxt.all_terms_by_app.contains_key(app) {
                ctxt.all_terms_by_app.insert(app.clone(), HashMap::new());
            }
            ctxt.all_terms_by_app.get_mut(app).unwrap().insert(term.clone(), exp.span.clone());
        }
    }
    if is_pure {
        if let Some(var_depth) = trigger_var_depth(ctxt, &term, depth) {
            if !ctxt.pure_terms.contains_key(&term) {
                ctxt.pure_terms.insert(term.clone(), (exp.clone(), ctxt.pure_terms.len()));
            }
            let score = make_score(&term, var_depth);
            if !ctxt.pure_best_scores.contains_key(&term)
                || score.lex() < ctxt.pure_best_scores[&term].lex()
            {
                ctxt.pure_best_scores.insert(term.clone(), score);
            }
        }
    }
    (is_pure, term)
}

// First bool: is term equal to template for some instantiation of trigger_vars?
// Second bool: is the instantiation potentially bigger than the original template?
fn structure_matches(ctxt: &Ctxt, template: &Term, term: &Term) -> (bool, bool) {
    match (&**template, &**term) {
        (TermX::Var(UniqueIdent { name: x1, local: None }), TermX::App(_, _))
            if ctxt.trigger_vars.contains(x1) =>
        {
            (true, true)
        }
        (TermX::Var(UniqueIdent { name: x1, local: None }), _)
            if ctxt.trigger_vars.contains(x1) =>
        {
            (true, false)
        }
        (TermX::Var(x1), TermX::Var(x2)) => (x1 == x2, false),
        (TermX::App(a1, args1), TermX::App(a2, args2))
            if a1 == a2 && args1.len() == args2.len() =>
        {
            let (eq, bigger): (Vec<bool>, Vec<bool>) = args1
                .iter()
                .zip(args2.iter())
                .map(|(a1, a2)| structure_matches(ctxt, a1, a2))
                .unzip();
            (eq.into_iter().all(|b| b), bigger.into_iter().any(|b| b))
        }
        _ => (false, false),
    }
}

fn remove_obvious_potential_loops(ctxt: &mut Ctxt, timer: &mut Timer) -> Result<(), VirErr> {
    // Very basic filtering of potential matching loops:
    //   eliminate f(...x...) if there's a different term f(...e...)
    //   that matches f(...x...) in structure
    // REVIEW: we could attempt more sophisticated cycle detection
    let mut remove: Vec<Term> = Vec::new();
    for pure in ctxt.pure_terms.keys() {
        if let TermX::App(app, _) = &**pure {
            if ctxt.all_terms_by_app.contains_key(app) {
                for term in ctxt.all_terms_by_app[app].keys() {
                    check_timeout(timer)?;
                    let (eq, bigger) = structure_matches(ctxt, pure, term);
                    if eq && bigger {
                        remove.push(pure.clone());
                        break;
                    }
                }
            }
        }
    }
    for pure in remove {
        ctxt.pure_terms.remove(&pure);
    }
    Ok(())
}

type Trigger = Vec<(Term, Span)>;

struct State {
    remaining_vars: HashSet<Ident>,
    accumulated_terms: HashMap<Term, Span>,
    best_so_far: Vec<Trigger>,
    // If we relied on Score to break a tie, we consider this a low-confidence trigger
    // and we emit a report to the user.
    low_confidence: bool,
}

fn trigger_score(ctxt: &Ctxt, trigger: &Trigger) -> Score {
    let mut total = Score { num_operators: 0, no_calls: 0, depth: 0, size: 0 };
    for (t, _) in trigger.iter() {
        let score = &ctxt.pure_best_scores[t];
        total.num_operators += score.num_operators;
        total.no_calls += score.no_calls;
        total.depth += score.depth;
        total.size += score.size;
    }
    total
}

// Find the best trigger that covers all the trigger variables.
// This is a variant of minimum-set-cover, which is NP-complete.
fn compute_triggers(ctxt: &Ctxt, state: &mut State, timer: &mut Timer) -> Result<(), VirErr> {
    if state.remaining_vars.len() == 0 {
        let trigger: Vec<(Term, Span)> =
            state.accumulated_terms.iter().map(|(t, s)| (t.clone(), s.clone())).collect();
        // println!("found: {:?} {}", trigger, trigger_score(ctxt, &trigger));
        if state.best_so_far.len() > 0 {
            // If we're better than what came before, drop what came before
            if state.best_so_far[0].len() > trigger.len() {
                state.best_so_far.clear();
                state.low_confidence = false;
            } else {
                let prev_score = trigger_score(ctxt, &state.best_so_far[0]).lex();
                let new_score = trigger_score(ctxt, &trigger).lex();
                if prev_score > new_score {
                    state.low_confidence = true;
                    state.best_so_far.clear();
                } else if prev_score < new_score {
                    state.low_confidence = true;
                    // If we're worse, return
                    return Ok(());
                }
            }
        }
        state.best_so_far.push(trigger);
        return Ok(());
    }
    if state.best_so_far.len() > 0 && state.best_so_far[0].len() <= state.accumulated_terms.len() {
        // We've already found something better
        return Ok(());
    }
    check_timeout(timer)?;
    // pick one variable x from remaining_vars
    let x = state.remaining_vars.iter().next().unwrap().clone();
    for (term, span) in &ctxt.pure_terms_by_var[&x] {
        if !state.accumulated_terms.contains_key(term) {
            state.accumulated_terms.insert(term.clone(), span.clone());
            let mut vars: HashSet<Ident> = HashSet::new();
            let mut removed: Vec<Ident> = Vec::new();
            trigger_vars_in_term(ctxt, &mut vars, &term);
            // remove term's vars
            for y in vars {
                if state.remaining_vars.contains(&y) {
                    state.remaining_vars.remove(&y);
                    removed.push(y.clone());
                }
            }
            compute_triggers(ctxt, state, timer)?;
            // restore vars
            for y in removed {
                state.remaining_vars.insert(y);
            }
            state.accumulated_terms.remove(term);
        }
    }
    Ok(())
}

pub(crate) fn build_triggers(
    ctx: &Ctx,
    span: &Span,
    vars: &Vec<Ident>,
    exp: &Exp,
    auto_trigger: bool,
) -> Result<Trigs, VirErr> {
    let mut ctxt = Ctxt {
        trigger_vars: vars.iter().cloned().collect(),
        all_terms: HashMap::new(),
        pure_terms: HashMap::new(),
        all_terms_by_app: HashMap::new(),
        pure_terms_by_var: HashMap::new(),
        pure_best_scores: HashMap::new(),
        next_id: 0,
    };
    for x in vars {
        ctxt.pure_terms_by_var.insert(x.clone(), HashMap::new());
    }
    let mut timer = Timer { span: span.clone(), timeout_countdown: 10000 };
    gather_terms(&mut ctxt, ctx, exp, 0);
    /*
    println!();
    println!("all:");
    for t in ctxt.all_terms.keys() {
        println!("  {:?}", t);
    }
    println!("pure:");
    for t in ctxt.pure_terms.keys() {
        println!("  {:?} {}", t, ctxt.pure_best_scores[t].lex());
    }
    */
    remove_obvious_potential_loops(&mut ctxt, &mut timer)?;
    // println!("pure after loop removal:");
    for (term, (e, _)) in ctxt.pure_terms.iter() {
        let mut vars: HashSet<Ident> = HashSet::new();
        trigger_vars_in_term(&ctxt, &mut vars, &term);
        for x in &vars {
            ctxt.pure_terms_by_var.get_mut(x).unwrap().insert(term.clone(), e.span.clone());
        }
        // println!("  {:?}", term);
    }
    /*
    println!("by var:");
    for (x, map) in &ctxt.pure_terms_by_var {
        println!("  {:?} {:?}", x, map.keys());
    }
    */
    let mut state = State {
        remaining_vars: ctxt.trigger_vars.iter().cloned().collect(),
        accumulated_terms: HashMap::new(),
        best_so_far: Vec::new(),
        low_confidence: false,
    };
    compute_triggers(&ctxt, &mut state, &mut timer)?;

    // To stabilize the order of the chosen triggers,
    // sort the triggers by the position of their terms in exp
    for trigger in &mut state.best_so_far {
        trigger.sort_by_key(|(term, _)| ctxt.pure_terms[term].1);
    }
    state.best_so_far.sort_by_key(|trig| vec_map(trig, |(term, _)| ctxt.pure_terms[term].1));

    /*
    for found in &state.best_so_far {
        let score: u64 = trigger_score(&ctxt, &found);
        println!("FOUND: {} {:?}", score, found.iter().map(|(t, _)| t).collect::<Vec<_>>());
    }
    */
    let mut chosen_triggers_vec = ctx.global.chosen_triggers.borrow_mut();
    let found_triggers: Vec<Vec<(Span, String)>> = vec_map(&state.best_so_far, |trig| {
        vec_map(&trig, |(term, span)| (span.clone(), format!("{:?}", term)))
    });
    let module = match &ctx.fun {
        Some(FunctionCtx { module_for_chosen_triggers: Some(m), .. }) => m.clone(),
        _ => ctx.module.clone(),
    };
    let chosen_triggers = ChosenTriggers {
        module,
        span: span.clone(),
        triggers: found_triggers,
        low_confidence: state.low_confidence && !auto_trigger,
    };
    chosen_triggers_vec.push(chosen_triggers);
    if state.best_so_far.len() >= 1 {
        let trigs: Vec<Trig> = vec_map(&state.best_so_far, |trig| {
            Arc::new(vec_map(&trig, |(term, _)| ctxt.pure_terms[term].0.clone()))
        });
        Ok(Arc::new(trigs))
    } else {
        err_str(
            span,
            "Could not automatically infer triggers for this quantifer.  Use #[trigger] annotations to manually mark trigger terms instead.",
        )
    }
}
