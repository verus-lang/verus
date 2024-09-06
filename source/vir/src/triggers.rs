use crate::ast::{
    BinaryOp, SpannedTyped, TriggerAnnotation, Typ, TypX, UnaryOp, UnaryOpr, VarAt, VarBinders,
    VarIdent, VirErr,
};
use crate::context::Ctx;
use crate::messages::{error, Span};
use crate::sst::{BndX, Exp, ExpX, Exps, Trig, Trigs};
use crate::triggers_auto::AutoType;
use air::scope_map::ScopeMap;
use std::collections::{BTreeMap, HashMap, HashSet};
use std::sync::Arc;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum TriggerBoxing {
    Poly,
    Native,
    TypeId,
}

// Manual triggers
struct State {
    // use results from triggers_auto, no questions asked
    auto_trigger: AutoType,
    // variables the triggers must cover
    trigger_vars: HashMap<VarIdent, TriggerBoxing>,
    // user-specified triggers (for sortedness stability, use BTreeMap rather than HashMap)
    triggers: BTreeMap<Option<u64>, Vec<Exp>>,
    // trigger_vars covered by each trigger
    coverage: HashMap<Option<u64>, HashSet<VarIdent>>,
}

pub(crate) fn typ_boxing(ctx: &Ctx, typ: &Typ) -> TriggerBoxing {
    match &**typ {
        TypX::TypeId => TriggerBoxing::TypeId,
        _ if crate::poly::typ_is_poly(ctx, typ) => TriggerBoxing::Poly,
        _ => TriggerBoxing::Native,
    }
}

fn preprocess_exp(exp: &Exp) -> Exp {
    match &exp.x {
        ExpX::UnaryOpr(UnaryOpr::Box(_), e) | ExpX::UnaryOpr(UnaryOpr::Unbox(_), e) => {
            preprocess_exp(e)
        }
        ExpX::Binary(BinaryOp::HeightCompare { .. }, e1, _) => {
            // We don't let users use the "height" function or Height type directly.
            // However, when using HeightCompare, it's useful to trigger on "height",
            // and it's not useful to trigger on HeightCompare,
            // which is essentially a "<" operator on heights.
            // Therefore, we replace HeightCompare triggers with height triggers.
            // (Or rather, HeightCompare is the interface by which users write height triggers.)
            let typ = Arc::new(TypX::Bool); // arbitrary type for trigger
            SpannedTyped::new(&exp.span, &typ, ExpX::Unary(UnaryOp::HeightTrigger, e1.clone()))
        }
        _ => exp.clone(),
    }
}

// REVIEW: it's awkward that poly.rs has to decide ahead of time
// in AST which quantifier variables are Poly and which are native,
// and only later in SST do we have all the information (e.g. inlining results)
// to tell whether this decision was correct.
// See test test_arith_with_inline in triggers.rs for an example of a case
// in which this prediction is incorrect.
pub(crate) fn predict_native_quant_vars(
    bs: &VarBinders<Typ>,
    bodies: &Vec<&crate::ast::Expr>,
) -> HashSet<VarIdent> {
    use crate::ast::ExprX;
    let mut natives: HashSet<VarIdent> = HashSet::new();
    let mut scope_map = crate::ast_visitor::VisitorScopeMap::new();
    let mut fbody = |map: &mut crate::ast_visitor::VisitorScopeMap, expr: &crate::ast::Expr| {
        let mut ftrig = |map: &mut crate::ast_visitor::VisitorScopeMap, expr: &crate::ast::Expr| {
            let mut check_arg = |expr: &crate::ast::Expr| match &expr.x {
                ExprX::Var(x) => {
                    if bs.iter().any(|b| &b.name == x) && !map.contains_key(x) {
                        natives.insert(x.clone());
                    }
                }
                _ => {}
            };
            match &expr.x {
                ExprX::Unary(op, arg) => match op {
                    UnaryOp::Clip { .. } => check_arg(arg),
                    _ => {}
                },
                ExprX::UnaryOpr(UnaryOpr::IntegerTypeBound(..), arg) => check_arg(arg),
                ExprX::Binary(op, arg1, arg2) => {
                    use BinaryOp::*;
                    match op {
                        Inequality(_) | Arith(..) => {
                            check_arg(arg1);
                            check_arg(arg2);
                        }
                        _ => {}
                    }
                }
                _ => {}
            }
        };
        match &expr.x {
            ExprX::Unary(UnaryOp::Trigger(TriggerAnnotation::Trigger(_)), e) => {
                crate::ast_visitor::expr_visitor_traverse(e, map, &mut ftrig);
            }
            ExprX::WithTriggers { triggers, body: _ } => {
                for trigger in triggers.iter() {
                    for t in trigger.iter() {
                        crate::ast_visitor::expr_visitor_traverse(t, map, &mut ftrig);
                    }
                }
            }
            _ => {}
        }
    };
    for body in bodies {
        crate::ast_visitor::expr_visitor_traverse(body, &mut scope_map, &mut fbody);
    }
    natives
}

fn check_trigger_expr_arg(state: &State, expect_boxed: bool, arg: &Exp) -> Result<(), VirErr> {
    match &arg.x {
        ExpX::Var(x) => {
            if let Some(boxing) = state.trigger_vars.get(x) {
                match (expect_boxed, boxing) {
                    (false, TriggerBoxing::Native) => Ok(()),
                    (true, TriggerBoxing::Poly) => Ok(()),
                    (true, TriggerBoxing::TypeId) => Ok(()),
                    _ => {
                        // See poly.rs for an explanation
                        Err(error(
                            &arg.span,
                            format!(
                                "variable `{}` in trigger cannot appear in both arithmetic and non-arithmetic positions",
                                crate::def::user_local_name(x)
                            ),
                        ))
                    }
                }
            } else {
                Ok(())
            }
        }
        ExpX::Unary(op, arg) => match op {
            UnaryOp::Trigger(_)
            | UnaryOp::HeightTrigger
            | UnaryOp::CoerceMode { .. }
            | UnaryOp::MustBeFinalized
            | UnaryOp::MustBeElaborated => {
                // recurse inside coercions
                check_trigger_expr_arg(state, expect_boxed, arg)
            }
            UnaryOp::Not
            | UnaryOp::Clip { .. }
            | UnaryOp::BitNot(_)
            | UnaryOp::StrLen
            | UnaryOp::StrIsAscii
            | UnaryOp::CastToInteger
            | UnaryOp::InferSpecForLoopIter { .. } => Ok(()),
        },
        ExpX::UnaryOpr(op, arg) => match op {
            UnaryOpr::Box(_) | UnaryOpr::Unbox(_) | UnaryOpr::CustomErr(_) => {
                // recurse inside coercions
                check_trigger_expr_arg(state, expect_boxed, arg)
            }
            UnaryOpr::IsVariant { .. }
            | UnaryOpr::TupleField { .. }
            | UnaryOpr::Field { .. }
            | UnaryOpr::IntegerTypeBound(..)
            | UnaryOpr::HasType(_) => Ok(()),
        },
        _ => Ok(()),
    }
}

fn check_trigger_expr_args(state: &State, expect_boxed: bool, args: &Exps) -> Result<(), VirErr> {
    for arg in args.iter() {
        check_trigger_expr_arg(state, expect_boxed, arg)?;
    }
    Ok(())
}

fn check_trigger_expr(
    state: &State,
    exp: &Exp,
    free_vars: &mut HashSet<VarIdent>,
    lets: &HashSet<VarIdent>,
) -> Result<(), VirErr> {
    match &exp.x {
        ExpX::Call(..)
        | ExpX::CallLambda(..)
        | ExpX::UnaryOpr(UnaryOpr::Field { .. }, _)
        | ExpX::UnaryOpr(UnaryOpr::IsVariant { .. }, _)
        | ExpX::Unary(UnaryOp::Trigger(_) | UnaryOp::HeightTrigger, _) => {}
        ExpX::Binary(BinaryOp::Bitwise(_, _) | BinaryOp::ArrayIndex, _, _) => {}
        ExpX::Unary(UnaryOp::BitNot(_), _) => {}
        ExpX::BinaryOpr(crate::ast::BinaryOpr::ExtEq(..), _, _) => {}
        ExpX::Unary(UnaryOp::Clip { .. }, _) | ExpX::Binary(BinaryOp::Arith(..), _, _) => {}
        _ => {
            return Err(error(
                &exp.span,
                "trigger must be a function call, a field access, or arithmetic operator",
            ));
        }
    }

    let mut scope_map = ScopeMap::new();
    let ft = |free_vars: &mut HashSet<VarIdent>, t: &Typ| match &**t {
        TypX::TypParam(x) => {
            free_vars.insert(crate::def::suffix_typ_param_id(x));
            Ok(t.clone())
        }
        _ => Ok(t.clone()),
    };
    crate::sst_visitor::exp_visitor_check(
        exp,
        &mut scope_map,
        &mut |exp, _scope_map| match &exp.x {
            ExpX::Const(_) => Ok(()),
            ExpX::StaticVar(_) => Ok(()),
            ExpX::CallLambda(_, args) => check_trigger_expr_args(state, true, args),
            ExpX::Ctor(_, _, bs) => {
                for b in bs.iter() {
                    check_trigger_expr_arg(state, true, &b.a)?;
                }
                Ok(())
            }
            ExpX::ArrayLiteral(_) => {
                Err(error(&exp.span, "triggers cannot contain array literals"))
            }
            ExpX::Loc(..) | ExpX::VarLoc(..) => Ok(()),
            ExpX::ExecFnByName(..) => Ok(()),
            ExpX::Call(_, typs, args) => {
                for typ in typs.iter() {
                    crate::ast_visitor::map_typ_visitor_env(typ, free_vars, &ft).unwrap();
                }
                check_trigger_expr_args(state, true, args)
            }
            ExpX::Var(x) => {
                if lets.contains(x) {
                    return Err(error(
                        &exp.span,
                        "let variables in triggers not supported, use #![trigger ...] instead",
                    ));
                }
                free_vars.insert(x.clone());
                Ok(())
            }
            ExpX::VarAt(_, VarAt::Pre) => Ok(()),
            ExpX::Old(_, _) => panic!("internal error: Old"),
            ExpX::NullaryOpr(crate::ast::NullaryOpr::ConstGeneric(_)) => Ok(()),
            ExpX::NullaryOpr(crate::ast::NullaryOpr::TraitBound(..)) => {
                Err(error(&exp.span, "triggers cannot contain trait bounds"))
            }
            ExpX::NullaryOpr(crate::ast::NullaryOpr::TypEqualityBound(..)) => {
                Err(error(&exp.span, "triggers cannot contain trait bounds"))
            }
            ExpX::NullaryOpr(crate::ast::NullaryOpr::ConstTypBound(..)) => {
                Err(error(&exp.span, "triggers cannot contain const type bounds"))
            }
            ExpX::NullaryOpr(crate::ast::NullaryOpr::NoInferSpecForLoopIter) => {
                Err(error(&exp.span, "triggers cannot contain loop spec inference"))
            }
            ExpX::Unary(op, arg) => match op {
                UnaryOp::StrLen | UnaryOp::StrIsAscii | UnaryOp::BitNot(_) => {
                    check_trigger_expr_arg(state, true, arg)
                }
                UnaryOp::Clip { .. } => check_trigger_expr_arg(state, false, arg),
                UnaryOp::Trigger(_)
                | UnaryOp::HeightTrigger
                | UnaryOp::CoerceMode { .. }
                | UnaryOp::MustBeFinalized
                | UnaryOp::MustBeElaborated
                | UnaryOp::CastToInteger => Ok(()),
                UnaryOp::InferSpecForLoopIter { .. } => {
                    Err(error(&exp.span, "triggers cannot contain loop spec inference"))
                }
                UnaryOp::Not => Err(error(&exp.span, "triggers cannot contain boolean operators")),
            },
            ExpX::UnaryOpr(op, arg) => match op {
                UnaryOpr::Box(_) | UnaryOpr::Unbox(_) | UnaryOpr::CustomErr(_) => Ok(()),
                UnaryOpr::IsVariant { .. }
                | UnaryOpr::TupleField { .. }
                | UnaryOpr::Field { .. } => check_trigger_expr_arg(state, true, arg),
                UnaryOpr::IntegerTypeBound(..) => check_trigger_expr_arg(state, false, arg),
                UnaryOpr::HasType(_) => panic!("internal error: trigger on HasType"),
            },
            ExpX::Binary(op, arg1, arg2) => {
                use BinaryOp::*;
                match op {
                    And | Or | Xor | Implies | Eq(_) | Ne => {
                        Err(error(&exp.span, "triggers cannot contain boolean operators"))
                    }
                    HeightCompare { .. } => Err(error(
                        &exp.span,
                        "triggers cannot contain interior is_smaller_than expressions",
                    )),
                    Inequality(_) => Err(error(&exp.span, "triggers cannot contain inequalities")),
                    StrGetChar | Bitwise(..) => {
                        check_trigger_expr_arg(state, true, arg1)?;
                        check_trigger_expr_arg(state, true, arg2)
                    }
                    ArrayIndex => {
                        crate::ast_visitor::map_typ_visitor_env(&arg1.typ, free_vars, &ft).unwrap();
                        check_trigger_expr_arg(state, true, arg1)?;
                        check_trigger_expr_arg(state, true, arg2)
                    }
                    Arith(..) => {
                        check_trigger_expr_arg(state, false, arg1)?;
                        check_trigger_expr_arg(state, false, arg2)
                    }
                }
            }
            ExpX::BinaryOpr(crate::ast::BinaryOpr::ExtEq(_, typ), arg1, arg2) => {
                crate::ast_visitor::map_typ_visitor_env(typ, free_vars, &ft).unwrap();
                check_trigger_expr_arg(state, true, arg1)?;
                check_trigger_expr_arg(state, true, arg2)
            }
            ExpX::If(_, _, _) => Err(error(&exp.span, "triggers cannot contain if/else")),
            ExpX::WithTriggers(..) => {
                Err(error(&exp.span, "triggers cannot contain #![trigger ...]"))
            }
            ExpX::Bind(_, _) => {
                Err(error(&exp.span, "triggers cannot contain let/forall/exists/lambda/choose"))
            }
            ExpX::Interp(_) => {
                panic!("Found an interpreter expression {:?} outside the interpreter", exp)
            }
            ExpX::FuelConst(_) => {
                panic!("Found FuelConst expression during trigger selection")
            }
        },
    )
}

fn get_manual_triggers(state: &mut State, exp: &Exp) -> Result<(), VirErr> {
    let mut map: ScopeMap<VarIdent, bool> = ScopeMap::new();
    let mut lets: HashSet<VarIdent> = HashSet::new();
    map.push_scope(false);
    for x in state.trigger_vars.keys() {
        map.insert(x.clone(), true).expect("duplicate bound variables");
    }
    crate::sst_visitor::exp_visitor_check(exp, &mut map, &mut |exp, map| {
        // this closure mutates `state`
        match &exp.x {
            ExpX::Unary(UnaryOp::Trigger(TriggerAnnotation::AutoTrigger), _) => {
                if map.num_scopes() == 1 {
                    state.auto_trigger = AutoType::Regular;
                }
                Ok(())
            }
            ExpX::Unary(UnaryOp::Trigger(TriggerAnnotation::AllTriggers), _) => {
                if map.num_scopes() == 1 {
                    state.auto_trigger = AutoType::All;
                }
                Ok(())
            }
            ExpX::Unary(UnaryOp::Trigger(TriggerAnnotation::Trigger(group)), e1) => {
                let mut free_vars: HashSet<VarIdent> = HashSet::new();
                let e1 = preprocess_exp(&e1);
                check_trigger_expr(state, &e1, &mut free_vars, &lets)?;
                for x in &free_vars {
                    if map.get(x) == Some(&true) && !state.trigger_vars.contains_key(x) {
                        // If the trigger contains variables declared by a nested quantifier,
                        // it must be the nested quantifier's trigger, not ours.
                        return Ok(());
                    }
                }
                if !state.triggers.contains_key(group) {
                    state.triggers.insert(*group, Vec::new());
                    state.coverage.insert(*group, HashSet::new());
                }
                state.triggers.get_mut(group).unwrap().push(e1.clone());
                for x in &free_vars {
                    if state.trigger_vars.contains_key(x) {
                        state.coverage.get_mut(group).unwrap().insert(x.clone());
                    }
                }
                Ok(())
            }
            ExpX::WithTriggers(triggers, _body) => {
                if map.num_scopes() == 1 {
                    for (n, trigger) in triggers.iter().enumerate() {
                        let group = Some(n as u64);
                        let mut coverage: HashSet<VarIdent> = HashSet::new();
                        let es: Vec<Exp> = trigger.iter().map(preprocess_exp).collect();
                        for e in &es {
                            let mut free_vars: HashSet<VarIdent> = HashSet::new();
                            check_trigger_expr(state, e, &mut free_vars, &lets)?;
                            for x in free_vars {
                                if state.trigger_vars.contains_key(&x) {
                                    coverage.insert(x);
                                }
                            }
                        }
                        state.triggers.insert(group, es);
                        state.coverage.insert(group, coverage);
                    }
                }
                Ok(())
            }
            ExpX::Bind(bnd, _) => {
                let bvars: Vec<VarIdent> = match &bnd.x {
                    BndX::Let(binders) => binders.iter().map(|b| b.name.clone()).collect(),
                    BndX::Quant(_, binders, _)
                    | BndX::Lambda(binders, _)
                    | BndX::Choose(binders, _, _) => {
                        binders.iter().map(|b| b.name.clone()).collect()
                    }
                };
                for x in bvars {
                    if map.contains_key(&x) {
                        return Err(error(&bnd.span, "variable shadowing not yet supported"));
                    }
                }
                if let BndX::Let(binders) = &bnd.x {
                    lets.extend(binders.iter().map(|b| b.name.clone()));
                }
                Ok(())
            }
            _ => Ok(()),
        }
    })?;
    map.pop_scope();
    assert_eq!(map.num_scopes(), 0);
    Ok(())
}

pub(crate) fn build_triggers(
    ctx: &Ctx,
    span: &Span,
    vars: &Vec<(VarIdent, TriggerBoxing)>,
    exp: &Exp,
    allow_empty: bool,
) -> Result<Trigs, VirErr> {
    let mut state = State {
        auto_trigger: AutoType::None,
        trigger_vars: vars.iter().cloned().collect(),
        triggers: BTreeMap::new(),
        coverage: HashMap::new(),
    };
    get_manual_triggers(&mut state, exp)?;
    if state.triggers.len() > 0 || allow_empty {
        if state.auto_trigger != AutoType::None {
            return Err(error(
                span,
                "cannot use both manual triggers (#[trigger] or #![trigger ...]) and #![auto]",
            ));
        }
        let mut trigs: Vec<Trig> = Vec::new();
        for (group, trig) in state.triggers {
            for (x, _) in vars {
                if !state.coverage[&group].contains(x) {
                    let group_name = match group {
                        None => "".to_string(),
                        Some(id) => format!(" group {}", id),
                    };
                    return Err(error(
                        span,
                        format!(
                            "trigger{} does not cover variable {}",
                            group_name,
                            crate::def::user_local_name(x)
                        ),
                    ));
                }
            }
            trigs.push(Arc::new(trig.clone()));
        }
        Ok(Arc::new(trigs))
    } else {
        let vars = &vars.iter().cloned().map(|(x, _)| x).collect();
        crate::triggers_auto::build_triggers(ctx, span, vars, exp, state.auto_trigger)
    }
}
