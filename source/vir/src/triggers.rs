use crate::ast::{
    BinaryOp, SpannedTyped, TriggerAnnotation, Typ, TypX, UnaryOp, UnaryOpr, VarAt, VarBinders,
    VarIdent, VirErr,
};
use crate::context::Ctx;
use crate::messages::{Span, error};
use crate::sst::{BndX, Exp, ExpX, Exps, Trig, Trigs};
use crate::triggers_auto::AutoType;
use crate::util::vec_map;
use air::scope_map::ScopeMap;
use std::collections::{BTreeMap, HashMap, HashSet};
use std::sync::Arc;

// Manual triggers
struct State {
    // use results from triggers_auto, no questions asked
    auto_trigger: AutoType,
    // variables the triggers must cover
    trigger_vars: HashSet<VarIdent>,
    // user-specified triggers (for sortedness stability, use BTreeMap rather than HashMap)
    triggers: BTreeMap<Option<u64>, Vec<Exp>>,
    // trigger_vars covered by each trigger
    coverage: HashMap<Option<u64>, HashSet<VarIdent>>,
    // a variable cannot be both native and poly, so these should not intersect:
}

fn preprocess_exp(exp: &Exp) -> Exp {
    match &exp.x {
        ExpX::UnaryOpr(UnaryOpr::Box(_), _) | ExpX::UnaryOpr(UnaryOpr::Unbox(_), _) => {
            panic!("unexpected box")
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

pub(crate) fn native_quant_vars(bs: &VarBinders<Typ>, triggers: &Trigs) -> HashSet<VarIdent> {
    struct NativeVars<'a> {
        bs: &'a VarBinders<Typ>,
        natives: HashSet<VarIdent>,
        polys: HashSet<VarIdent>,
    }
    use crate::sst_visitor::{NoScoper, Visitor, Walk};
    impl<'a> Visitor<Walk, (), NoScoper> for NativeVars<'a> {
        fn visit_exp(&mut self, exp: &Exp) -> Result<(), ()> {
            let mut check_arg = |e: &Exp, is_native: bool| match &e.x {
                ExpX::Var(x) => {
                    if self.bs.iter().any(|b| &b.name == x) {
                        if is_native {
                            self.natives.insert(x.clone());
                        } else {
                            self.polys.insert(x.clone());
                        }
                    }
                }
                _ => {}
            };
            match &exp.x {
                ExpX::Unary(op, arg) => match op {
                    UnaryOp::Clip { .. } => check_arg(arg, true),
                    _ => check_arg(arg, false),
                },
                ExpX::UnaryOpr(UnaryOpr::IntegerTypeBound(..), arg) => check_arg(arg, true),
                ExpX::UnaryOpr(_, arg) => check_arg(arg, false),
                ExpX::Binary(op, arg1, arg2) => match op {
                    BinaryOp::Inequality(_) | BinaryOp::Arith(..) => {
                        check_arg(arg1, true);
                        check_arg(arg2, true);
                    }
                    _ => {
                        check_arg(arg1, false);
                        check_arg(arg2, false);
                    }
                },
                ExpX::BinaryOpr(crate::ast::BinaryOpr::ExtEq(..), arg1, arg2) => {
                    check_arg(arg1, false);
                    check_arg(arg2, false);
                }
                ExpX::Call(_, _, args) | ExpX::CallLambda(_, args) => {
                    for arg in args.iter() {
                        check_arg(arg, false);
                    }
                }
                _ => {}
            }
            let _ = self.visit_exp_rec(exp);
            Ok(())
        }
    }
    let mut native_vars = NativeVars { bs, natives: HashSet::new(), polys: HashSet::new() };
    for trig in triggers.iter() {
        for exp in trig.iter() {
            let _ = native_vars.visit_exp(exp);
        }
    }
    // Return every bound variable used only natively:
    // (bound variables are poly by default, so we lean towards poly for vars used both ways;
    // either choice would be ok)
    &native_vars.natives - &native_vars.polys
}

fn check_trigger_expr_arg(state: &mut State, arg: &Exp) {
    match &arg.x {
        ExpX::Unary(op, arg) => match op {
            UnaryOp::Trigger(_)
            | UnaryOp::HeightTrigger
            | UnaryOp::CoerceMode { .. }
            | UnaryOp::ToDyn
            | UnaryOp::MustBeFinalized
            | UnaryOp::MustBeElaborated => {
                // recurse inside coercions
                check_trigger_expr_arg(state, arg)
            }
            UnaryOp::Not
            | UnaryOp::Clip { .. }
            | UnaryOp::FloatToBits
            | UnaryOp::IntToReal
            | UnaryOp::RealToInt
            | UnaryOp::BitNot(_)
            | UnaryOp::StrLen
            | UnaryOp::StrIsAscii
            | UnaryOp::CastToInteger
            | UnaryOp::MutRefCurrent
            | UnaryOp::MutRefFuture(_)
            | UnaryOp::MutRefFinal
            | UnaryOp::Length(_)
            | UnaryOp::InferSpecForLoopIter { .. } => {}
        },
        ExpX::UnaryOpr(op, arg) => match op {
            UnaryOpr::Box(_) | UnaryOpr::Unbox(_) => panic!("unexpected box"),
            UnaryOpr::CustomErr(_) => {
                // recurse inside coercions
                check_trigger_expr_arg(state, arg)
            }
            UnaryOpr::IsVariant { .. }
            | UnaryOpr::Field { .. }
            | UnaryOpr::IntegerTypeBound(..)
            | UnaryOpr::HasType(_) => {}
            UnaryOpr::HasResolved(_) => {}
        },
        _ => {}
    }
}

fn check_trigger_expr_args(state: &mut State, args: &Exps) {
    for arg in args.iter() {
        check_trigger_expr_arg(state, arg);
    }
}

fn get_free_vars(exp: &Exp) -> Result<HashSet<VarIdent>, VirErr> {
    let mut scope_map = ScopeMap::new();
    let mut free_vars = HashSet::<VarIdent>::new();
    crate::sst_visitor::exp_typ_visitor_check(
        exp,
        &mut scope_map,
        &mut free_vars,
        &mut |exp: &Exp, free_vars: &mut HashSet<VarIdent>, _scope_map| match &exp.x {
            ExpX::Var(x) => {
                free_vars.insert(x.clone());
                Ok(())
            }
            ExpX::Bind(_, _) => {
                Err(error(&exp.span, "triggers cannot contain let/forall/exists/lambda/choose"))
            }
            _ => Ok(()),
        },
        &mut |typ: &Typ, free_vars: &mut HashSet<VarIdent>, _scope_map| match &**typ {
            TypX::TypParam(x) => {
                free_vars.insert(crate::def::suffix_typ_param_id(x));
                Ok(())
            }
            _ => Ok(()),
        },
    )?;
    Ok(free_vars)
}

fn check_trigger_expr(
    state: &mut State,
    exp: &Exp,
    lets: &HashSet<VarIdent>,
) -> Result<(), VirErr> {
    match &exp.x {
        ExpX::Call(..)
        | ExpX::CallLambda(..)
        | ExpX::UnaryOpr(UnaryOpr::Field { .. }, _)
        | ExpX::UnaryOpr(UnaryOpr::IsVariant { .. }, _)
        | ExpX::Unary(UnaryOp::Trigger(_) | UnaryOp::HeightTrigger, _) => {}
        ExpX::Binary(BinaryOp::Bitwise(_, _) | BinaryOp::Index(..), _, _) => {}
        ExpX::Unary(UnaryOp::BitNot(_), _) => {}
        ExpX::BinaryOpr(crate::ast::BinaryOpr::ExtEq(..), _, _) => {}
        ExpX::Unary(UnaryOp::Clip { .. }, _) | ExpX::Binary(BinaryOp::Arith(..), _, _) => {}
        ExpX::UnaryOpr(UnaryOpr::HasResolved(_), _) => {}
        _ => {
            return Err(error(
                &exp.span,
                "trigger must be a function call, a field access, or arithmetic operator",
            ));
        }
    }

    let mut scope_map = ScopeMap::new();
    crate::sst_visitor::exp_visitor_check(
        exp,
        &mut scope_map,
        &mut |exp, _scope_map| match &exp.x {
            ExpX::Const(_) => Ok(()),
            ExpX::StaticVar(_) => Ok(()),
            ExpX::CallLambda(_, args) => {
                check_trigger_expr_args(state, args);
                Ok(())
            }
            ExpX::Ctor(_, _, bs) => {
                for b in bs.iter() {
                    check_trigger_expr_arg(state, &b.a);
                }
                Ok(())
            }
            ExpX::ArrayLiteral(_) => {
                Err(error(&exp.span, "triggers cannot contain array literals"))
            }
            ExpX::Loc(..) | ExpX::VarLoc(..) => Ok(()),
            ExpX::ExecFnByName(..) => Ok(()),
            ExpX::Call(_, _typs, args) => {
                check_trigger_expr_args(state, args);
                Ok(())
            }
            ExpX::Var(x) => {
                if lets.contains(x) {
                    return Err(error(
                        &exp.span,
                        "let variables in triggers not supported, use #![trigger ...] instead",
                    ));
                }
                Ok(())
            }
            ExpX::VarAt(_, VarAt::Pre) => Ok(()),
            ExpX::Old(_, _) => panic!("internal error: Old"),
            ExpX::NullaryOpr(crate::ast::NullaryOpr::ConstGeneric(_typ)) => Ok(()),
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
                UnaryOp::StrLen
                | UnaryOp::StrIsAscii
                | UnaryOp::BitNot(_)
                | UnaryOp::MutRefCurrent
                | UnaryOp::MutRefFuture(_)
                | UnaryOp::MutRefFinal => {
                    check_trigger_expr_arg(state, arg);
                    Ok(())
                }
                UnaryOp::Clip { .. }
                | UnaryOp::FloatToBits
                | UnaryOp::IntToReal
                | UnaryOp::RealToInt => {
                    check_trigger_expr_arg(state, arg);
                    Ok(())
                }
                UnaryOp::Trigger(_)
                | UnaryOp::HeightTrigger
                | UnaryOp::CoerceMode { .. }
                | UnaryOp::ToDyn
                | UnaryOp::MustBeFinalized
                | UnaryOp::MustBeElaborated
                | UnaryOp::CastToInteger => Ok(()),
                UnaryOp::InferSpecForLoopIter { .. } => {
                    Err(error(&exp.span, "triggers cannot contain loop spec inference"))
                }
                UnaryOp::Not => Err(error(&exp.span, "triggers cannot contain boolean operators")),
                UnaryOp::Length(_) => {
                    Err(error(&exp.span, "triggers cannot contain builtin Length operator"))
                }
            },
            ExpX::UnaryOpr(op, arg) => match op {
                UnaryOpr::Box(_) | UnaryOpr::Unbox(_) => panic!("unexpected box"),
                UnaryOpr::CustomErr(_) => Ok(()),
                UnaryOpr::IsVariant { .. } | UnaryOpr::Field { .. } => {
                    check_trigger_expr_arg(state, arg);
                    Ok(())
                }
                UnaryOpr::IntegerTypeBound(..) => {
                    check_trigger_expr_arg(state, arg);
                    Ok(())
                }
                UnaryOpr::HasType(_) => panic!("internal error: trigger on HasType"),
                UnaryOpr::HasResolved(_t) => {
                    check_trigger_expr_arg(state, arg);
                    Ok(())
                }
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
                        check_trigger_expr_arg(state, arg1);
                        check_trigger_expr_arg(state, arg2);
                        Ok(())
                    }
                    Index(..) => {
                        check_trigger_expr_arg(state, arg1);
                        check_trigger_expr_arg(state, arg2);
                        Ok(())
                    }
                    Arith(..) | RealArith(..) => {
                        check_trigger_expr_arg(state, arg1);
                        check_trigger_expr_arg(state, arg2);
                        Ok(())
                    }
                }
            }
            ExpX::BinaryOpr(crate::ast::BinaryOpr::ExtEq(_, _typ), arg1, arg2) => {
                check_trigger_expr_arg(state, arg1);
                check_trigger_expr_arg(state, arg2);
                Ok(())
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
    // REVIEW: 'lets' is an over-approximation because nothing ever gets removed
    // while you traverse?
    let mut lets: HashSet<VarIdent> = HashSet::new();
    map.push_scope(false);
    for x in state.trigger_vars.iter() {
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
                let free_vars: HashSet<VarIdent> = get_free_vars(e1)?;
                let e1 = preprocess_exp(&e1);
                for x in &free_vars {
                    if map.get(x) == Some(&true)
                        && !state.trigger_vars.contains(x)
                        && !lets.contains(x)
                    {
                        // If the trigger contains variables declared by a nested quantifier,
                        // it must be the nested quantifier's trigger, not ours.
                        return Ok(());
                    }
                }
                check_trigger_expr(state, &e1, &lets)?;
                // If the trigger doesn't contain *any* of our trigger vars, then it must
                // be for a more outer quantifier
                if !state.trigger_vars.iter().any(|trigger_var| free_vars.contains(trigger_var)) {
                    return Ok(());
                }
                if !state.triggers.contains_key(group) {
                    state.triggers.insert(*group, Vec::new());
                    state.coverage.insert(*group, HashSet::new());
                }
                state.triggers.get_mut(group).unwrap().push(e1.clone());
                for x in &free_vars {
                    if state.trigger_vars.contains(x) {
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
                            let free_vars: HashSet<VarIdent> = get_free_vars(e)?;
                            check_trigger_expr(state, e, &lets)?;
                            for x in free_vars {
                                if state.trigger_vars.contains(&x) {
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
                    BndX::Quant(_, binders, _, _)
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
    vars: &Vec<VarIdent>,
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
            for x in vars {
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
        let mut chosen_triggers_vec = ctx.global.chosen_triggers.borrow_mut();
        let found_triggers: Vec<Vec<(Span, String)>> =
            vec_map(&trigs, |trig| vec_map(&trig, |t| (t.span.clone(), format!("{:?}", t.x))));
        let module = match &ctx.fun {
            Some(crate::context::FunctionCtx { module_for_chosen_triggers: Some(m), .. }) => {
                m.clone()
            }
            _ => ctx.module.x.path.clone(),
        };
        let chosen_triggers = crate::context::ChosenTriggers {
            module,
            span: span.clone(),
            triggers: found_triggers,
            low_confidence: false,
            manual: true,
        };
        chosen_triggers_vec.push(chosen_triggers);
        Ok(Arc::new(trigs))
    } else {
        crate::triggers_auto::build_triggers(ctx, span, vars, exp, state.auto_trigger)
    }
}
