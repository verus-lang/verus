use crate::ast::{BinaryOp, Ident, Path, UnaryOp, UnaryOpr, VirErr};
use crate::ast_util::err_str;
use crate::context::Ctx;
use crate::def::prefix_recursive;
use crate::sst::{Exp, ExpX, Trig, Trigs};
use crate::sst_to_air::path_to_air_ident;
use crate::util::vec_map;
use air::ast::{Constant, Span};
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
    Field(Path, Ident),
    Call(Ident),
    Ctor(Ident, Ident), // datatype constructor: (Path, Variant)
    Other(u64),         // u64 is an id, assigned via a simple counter
}

type Term = Arc<TermX>;
type Terms = Arc<Vec<Term>>;
#[derive(PartialEq, Eq, Hash)]
enum TermX {
    Var(Ident),
    App(App, Terms),
}

impl std::fmt::Debug for TermX {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        match self {
            TermX::Var(x) => write!(f, "{}", x),
            TermX::App(App::Const(c), _) => write!(f, "{:?}", c),
            TermX::App(App::Field(_, x), es) => write!(f, "{:?}.{}", es[0], x),
            TermX::App(c @ (App::Call(_) | App::Ctor(_, _)), es) => {
                match c {
                    App::Call(x) => write!(f, "{}(", x)?,
                    App::Ctor(path, variant) => {
                        write!(f, "{}{}{}(", path, crate::def::VARIANT_SEPARATOR, variant)?
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
We choose these because they are likely to identify relevant terms
such as function definitions f(x, y) == ... or implication f(x, y) ==> ...
rather than terms used incidentally inside other terms.

Obviously, these are fairly arbitrary criteria, but the goal is to make *some* choice,
rather than just selecting all the candidate triggers.

REVIEW: these heuristics are experimental -- are they useful in practice?  Can they be improved?
*/
struct Score {
    // prefer
    depth: u64, // 1 or more, or 0 for next to ==
    size: u64,
}

impl Score {
    // lower total score is better
    fn total(&self) -> u64 {
        self.depth * 1000 + self.size
    }
}

struct Ctxt {
    trigger_vars: HashSet<Ident>,   // variables the triggers must cover
    all_terms: HashMap<Term, Span>, // terms with App
    pure_terms: HashMap<Term, Exp>, // terms with App and without Other
    all_terms_by_app: HashMap<App, HashMap<Term, Span>>, // all_terms, indexed by head App
    pure_terms_by_var: HashMap<Ident, HashMap<Term, Span>>, // pure_terms, indexed by trigger_vars
    pure_best_scores: HashMap<Term, Score>, // best score for this term
    next_id: u64,                   // used for Other
}

struct Timer {
    span: Span,             // span of entire quantifier
    timeout_countdown: u64, // algorithms are exponential, so give up rather than taking too long
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
        TermX::Var(x) if ctxt.trigger_vars.contains(x) => {
            vars.insert(x.clone());
        }
        TermX::Var(_) => {}
        TermX::App(_, args) => {
            for arg in args.iter() {
                trigger_vars_in_term(ctxt, vars, arg);
            }
        }
    }
}

fn term_size(term: &Term) -> u64 {
    match &**term {
        TermX::Var(_) => 1,
        TermX::App(_, args) => 1 + args.iter().map(term_size).sum::<u64>(),
    }
}

fn trigger_var_depth(ctxt: &Ctxt, term: &Term, depth: u64) -> Option<u64> {
    match &**term {
        TermX::Var(x) if ctxt.trigger_vars.contains(x) => Some(depth),
        TermX::Var(_) => None,
        TermX::App(_, args) => {
            args.iter().filter_map(|t| trigger_var_depth(ctxt, t, depth + 1)).max()
        }
    }
}

fn make_score(term: &Term, depth: u64) -> Score {
    Score { depth, size: term_size(term) }
}

fn gather_terms(ctxt: &mut Ctxt, ctx: &Ctx, exp: &Exp, depth: u64) -> (bool, Term) {
    let (is_pure, term) = match &exp.x {
        ExpX::Const(c) => {
            return match c {
                crate::ast::Constant::Bool(b) => {
                    (true, Arc::new(TermX::App(App::Const(Constant::Bool(*b)), Arc::new(vec![]))))
                }
                crate::ast::Constant::Nat(n) => (
                    true,
                    Arc::new(TermX::App(App::Const(Constant::Nat(n.clone())), Arc::new(vec![]))),
                ),
            };
        }
        ExpX::Var(x) => {
            return (true, Arc::new(TermX::Var(x.clone())));
        }
        ExpX::Old(_, _) => panic!("internal error: Old"),
        ExpX::Call(recursive, x, _, args) => {
            let (is_pures, terms): (Vec<bool>, Vec<Term>) =
                args.iter().map(|e| gather_terms(ctxt, ctx, e, depth + 1)).unzip();
            let is_pure = is_pures.into_iter().all(|b| b);
            let air_ident = path_to_air_ident(&x);
            (
                is_pure,
                Arc::new(TermX::App(
                    App::Call(if *recursive { prefix_recursive(&air_ident) } else { air_ident }),
                    Arc::new(terms),
                )),
            )
        }
        ExpX::Ctor(path, variant, fields) => {
            let (variant, args) = crate::sst_to_air::ctor_to_apply(ctx, path, variant, fields);
            let (is_pures, terms): (Vec<bool>, Vec<Term>) =
                args.map(|e| gather_terms(ctxt, ctx, &e.a, depth + 1)).unzip();
            let is_pure = is_pures.into_iter().all(|b| b);
            (
                is_pure,
                Arc::new(TermX::App(App::Ctor(path_to_air_ident(path), variant), Arc::new(terms))),
            )
        }
        ExpX::Field { lhs, datatype, field_name } => {
            let (is_pure, arg) = gather_terms(ctxt, ctx, lhs, depth + 1);
            (
                is_pure,
                Arc::new(TermX::App(
                    App::Field(datatype.clone(), field_name.clone()),
                    Arc::new(vec![arg]),
                )),
            )
        }
        ExpX::Unary(UnaryOp::Trigger(_), e1) => gather_terms(ctxt, ctx, e1, depth),
        ExpX::Unary(op, e1) => {
            let depth = match op {
                UnaryOp::Not => 0,
                UnaryOp::Trigger(_) | UnaryOp::Clip(_) => 1,
            };
            let (_, term1) = gather_terms(ctxt, ctx, e1, depth);
            ctxt.next_id += 1;
            (false, Arc::new(TermX::App(App::Other(ctxt.next_id), Arc::new(vec![term1]))))
        }
        ExpX::UnaryOpr(UnaryOpr::Box(_), e1) => gather_terms(ctxt, ctx, e1, depth),
        ExpX::UnaryOpr(UnaryOpr::Unbox(_), e1) => gather_terms(ctxt, ctx, e1, depth),
        ExpX::Binary(op, e1, e2) => {
            use BinaryOp::*;
            let depth = match op {
                And | Or | Implies | Eq => 0,
                Ne | Le | Ge | Lt | Gt | Add | Sub | Mul | EuclideanDiv | EuclideanMod => 1,
            };
            let (_, term1) = gather_terms(ctxt, ctx, e1, depth);
            let (_, term2) = gather_terms(ctxt, ctx, e2, depth);
            ctxt.next_id += 1;
            (false, Arc::new(TermX::App(App::Other(ctxt.next_id), Arc::new(vec![term1, term2]))))
        }
        ExpX::If(e1, e2, e3) => {
            let depth = 1;
            let (_, term1) = gather_terms(ctxt, ctx, e1, depth);
            let (_, term2) = gather_terms(ctxt, ctx, e2, depth);
            let (_, term3) = gather_terms(ctxt, ctx, e3, depth);
            ctxt.next_id += 1;
            (
                false,
                Arc::new(TermX::App(App::Other(ctxt.next_id), Arc::new(vec![term1, term2, term3]))),
            )
        }
        ExpX::Bind(_, _) => {
            // REVIEW: we could at least look for matching loops here
            ctxt.next_id += 1;
            (false, Arc::new(TermX::App(App::Other(ctxt.next_id), Arc::new(vec![]))))
        }
    };
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
                ctxt.pure_terms.insert(term.clone(), exp.clone());
            }
            let score = make_score(&term, var_depth);
            if !ctxt.pure_best_scores.contains_key(&term)
                || score.total() < ctxt.pure_best_scores[&term].total()
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
        (TermX::Var(x1), TermX::App(_, _)) if ctxt.trigger_vars.contains(x1) => (true, true),
        (TermX::Var(x1), _) if ctxt.trigger_vars.contains(x1) => (true, false),
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
}

fn trigger_score(ctxt: &Ctxt, trigger: &Trigger) -> u64 {
    trigger.iter().map(|(t, _)| ctxt.pure_best_scores[t].total()).sum()
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
            } else {
                let prev_score = trigger_score(ctxt, &state.best_so_far[0]);
                let new_score = trigger_score(ctxt, &trigger);
                if prev_score > new_score {
                    state.best_so_far.clear();
                } else if prev_score < new_score {
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
        println!("  {:?} {}", t, ctxt.pure_best_scores[t].total());
    }
    */
    remove_obvious_potential_loops(&mut ctxt, &mut timer)?;
    // println!("pure after loop removal:");
    for term in ctxt.pure_terms.keys() {
        let mut vars: HashSet<Ident> = HashSet::new();
        trigger_vars_in_term(&ctxt, &mut vars, &term);
        for x in &vars {
            ctxt.pure_terms_by_var.get_mut(x).unwrap().insert(term.clone(), exp.span.clone());
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
    };
    compute_triggers(&ctxt, &mut state, &mut timer)?;
    /*
    for found in &state.best_so_far {
        let score: u64 = trigger_score(&ctxt, &found);
        println!("FOUND: {} {:?}", score, found.iter().map(|(t, _)| t).collect::<Vec<_>>());
    }
    */
    let mut chosen_triggers = ctx.chosen_triggers.borrow_mut();
    let found_strings: Vec<Vec<String>> =
        vec_map(&state.best_so_far, |trig| vec_map(&trig, |(term, _)| format!("{:?}", term)));
    chosen_triggers.push((span.clone(), found_strings));
    //println!();
    if state.best_so_far.len() >= 1 {
        let trigs: Vec<Trig> = vec_map(&state.best_so_far, |trig| {
            Arc::new(vec_map(&trig, |(term, _)| ctxt.pure_terms[term].clone()))
        });
        Ok(Arc::new(trigs))
    } else {
        err_str(
            span,
            "Could not automatically infer triggers for this quantifer.  Use #[trigger] annotations to manually mark trigger terms instead.",
        )
    }
}
