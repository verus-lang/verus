use crate::ast::{BinaryOp, Ident, TriggerAnnotation, Typ, TypX, UnaryOp, UnaryOpr, VarAt, VirErr};
use crate::ast_util::{err_str, err_string};
use crate::context::Ctx;
use crate::sst::{BndX, Exp, ExpX, Trig, Trigs, UniqueIdent};
use air::ast::Span;
use air::scope_map::ScopeMap;
use std::collections::{BTreeMap, HashMap, HashSet};
use std::sync::Arc;

// Manual triggers
struct State {
    // use results from triggers_auto, no questions asked
    auto_trigger: bool,
    // parameters boxed = true: enables triggers on functions
    // parameters boxed = false: enables triggers on arithmetic
    boxed_params: bool,
    // variables the triggers must cover
    trigger_vars: HashSet<Ident>,
    // user-specified triggers (for sortedness stability, use BTreeMap rather than HashMap)
    triggers: BTreeMap<Option<u64>, Vec<Exp>>,
    // trigger_vars covered by each trigger
    coverage: HashMap<Option<u64>, HashSet<Ident>>,
}

fn remove_boxing(exp: &Exp) -> Exp {
    match &exp.x {
        ExpX::UnaryOpr(UnaryOpr::Box(_), e) | ExpX::UnaryOpr(UnaryOpr::Unbox(_), e) => {
            remove_boxing(e)
        }
        _ => exp.clone(),
    }
}

fn check_trigger_expr(
    state: &State,
    exp: &Exp,
    free_vars: &mut HashSet<Ident>,
    lets: &HashSet<Ident>,
) -> Result<(), VirErr> {
    if state.boxed_params {
        match &exp.x {
            ExpX::Call(..)
            | ExpX::UnaryOpr(UnaryOpr::Field { .. }, _)
            | ExpX::Unary(UnaryOp::Trigger(_), _) => {}
            // allow triggers for bitvector operators
            ExpX::Binary(BinaryOp::Bitwise(_), _, _) | ExpX::Unary(UnaryOp::BitNot, _) => {}
            _ => {
                return err_str(
                    &exp.span,
                    "trigger must be a function call, a field access, or a bitwise operator",
                );
            }
        }
    } else {
        match &exp.x {
            ExpX::Unary(UnaryOp::Trigger(_), _)
            | ExpX::Unary(UnaryOp::Clip { .. }, _)
            | ExpX::Binary(BinaryOp::Arith(..), _, _) => {}
            _ => {
                return err_str(
                    &exp.span,
                    "trigger in forall_arith must be an integer arithmetic operator",
                );
            }
        }
    }

    let mut scope_map = ScopeMap::new();
    if state.boxed_params {
        crate::sst_visitor::exp_visitor_check(
            exp,
            &mut scope_map,
            &mut |exp, _scope_map| match &exp.x {
                ExpX::Const(_)
                | ExpX::CallLambda(..)
                | ExpX::Ctor(..)
                | ExpX::Loc(..)
                | ExpX::VarLoc(..) => Ok(()),
                ExpX::Call(_, typs, _) => {
                    for typ in typs.iter() {
                        let ft = |free_vars: &mut HashSet<Ident>, t: &Typ| match &**t {
                            TypX::TypParam(x) => {
                                free_vars.insert(crate::def::suffix_typ_param_id(x));
                                Ok(t.clone())
                            }
                            _ => Ok(t.clone()),
                        };
                        crate::ast_visitor::map_typ_visitor_env(typ, free_vars, &ft).unwrap();
                    }
                    Ok(())
                }
                ExpX::Var(UniqueIdent { name: x, local: None }) => {
                    if lets.contains(x) {
                        return err_str(
                            &exp.span,
                            "let variables in triggers not supported, use with_triggers! instead",
                        );
                    }
                    free_vars.insert(x.clone());
                    Ok(())
                }
                ExpX::Var(UniqueIdent { name: _, local: Some(_) }) => Ok(()),
                ExpX::VarAt(_, VarAt::Pre) => Ok(()),
                ExpX::Old(_, _) => panic!("internal error: Old"),
                ExpX::Unary(op, _) => match op {
                    UnaryOp::Trigger(_)
                    | UnaryOp::Clip { .. }
                    | UnaryOp::BitNot
                    | UnaryOp::StrLen
                    | UnaryOp::StrIsAscii
                    | UnaryOp::CharToInt => Ok(()),
                    UnaryOp::CoerceMode { .. } => Ok(()),
                    UnaryOp::MustBeFinalized => Ok(()),
                    UnaryOp::Not => err_str(&exp.span, "triggers cannot contain boolean operators"),
                },
                ExpX::UnaryOpr(op, _) => match op {
                    UnaryOpr::Box(_)
                    | UnaryOpr::Unbox(_)
                    | UnaryOpr::IsVariant { .. }
                    | UnaryOpr::TupleField { .. }
                    | UnaryOpr::Field { .. } => Ok(()),
                    UnaryOpr::HasType(_) => panic!("internal error: trigger on HasType"),
                },
                ExpX::Binary(op, _, _) => {
                    use BinaryOp::*;
                    match op {
                        And | Or | Xor | Implies | Eq(_) | Ne => {
                            err_str(&exp.span, "triggers cannot contain boolean operators")
                        }
                        Inequality(_) => Ok(()),
                        Arith(..) => err_str(
                            &exp.span,
                            "triggers cannot contain integer arithmetic\nuse forall_arith for quantifiers on integer arithmetic",
                        ),
                        Bitwise(..) => Ok(()),
                        StrGetChar => Ok(()),
                    }
                }
                ExpX::If(_, _, _) => err_str(&exp.span, "triggers cannot contain if/else"),
                ExpX::WithTriggers(..) => {
                    err_str(&exp.span, "triggers cannot contain with_triggers")
                }
                ExpX::Bind(_, _) => {
                    err_str(&exp.span, "triggers cannot contain let/forall/exists/lambda/choose")
                }
                ExpX::Interp(_) => {
                    panic!("Found an interpreter expression {:?} outside the interpreter", exp)
                }
            },
        )
    } else {
        crate::sst_visitor::exp_visitor_check(exp, &mut scope_map, &mut |exp, _scope_map| {
            if match &exp.x {
                ExpX::Const(_) | ExpX::Loc(..) | ExpX::VarLoc(..) => true,
                ExpX::Var(UniqueIdent { name: x, local: None }) => {
                    if lets.contains(x) {
                        return err_str(
                            &exp.span,
                            "let variables in triggers not supported, use with_triggers! instead",
                        );
                    }
                    free_vars.insert(x.clone());
                    true
                }
                ExpX::Var(UniqueIdent { name: _, local: Some(_) }) => true,
                ExpX::VarAt(_, VarAt::Pre) => true,
                ExpX::Old(_, _) => panic!("internal error: Old"),
                ExpX::Unary(op, _) => match op {
                    UnaryOp::Trigger(_)
                    | UnaryOp::Clip { .. }
                    | UnaryOp::CoerceMode { .. }
                    | UnaryOp::CharToInt => true,
                    UnaryOp::MustBeFinalized => true,
                    UnaryOp::Not | UnaryOp::BitNot | UnaryOp::StrLen | UnaryOp::StrIsAscii => false,
                },
                ExpX::Binary(op, _, _) => {
                    use BinaryOp::*;
                    match op {
                        Arith(..) => true,
                        _ => false,
                    }
                }
                _ => false,
            } {
                Ok(())
            } else {
                err_str(&exp.span, "triggers in forall_arith can only contain arithmetic")
            }
        })
    }
}

fn get_manual_triggers(state: &mut State, exp: &Exp) -> Result<(), VirErr> {
    let mut map: ScopeMap<Ident, bool> = ScopeMap::new();
    let mut lets: HashSet<Ident> = HashSet::new();
    map.push_scope(false);
    for x in &state.trigger_vars {
        map.insert(x.clone(), true).expect("duplicate bound variables");
    }
    crate::sst_visitor::exp_visitor_check(exp, &mut map, &mut |exp, map| {
        // this closure mutates `state`
        match &exp.x {
            ExpX::Unary(UnaryOp::Trigger(TriggerAnnotation::AutoTrigger), _) => {
                if map.num_scopes() == 1 {
                    state.auto_trigger = true;
                }
                Ok(())
            }
            ExpX::Unary(UnaryOp::Trigger(TriggerAnnotation::Trigger(group)), e1) => {
                let mut free_vars: HashSet<Ident> = HashSet::new();
                let e1 = remove_boxing(&e1);
                check_trigger_expr(state, &e1, &mut free_vars, &lets)?;
                for x in &free_vars {
                    if map.get(x) == Some(&true) && !state.trigger_vars.contains(x) {
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
                        let mut coverage: HashSet<Ident> = HashSet::new();
                        let es: Vec<Exp> = trigger.iter().map(remove_boxing).collect();
                        for e in &es {
                            let mut free_vars: HashSet<Ident> = HashSet::new();
                            check_trigger_expr(state, e, &mut free_vars, &lets)?;
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
                let bvars: Vec<Ident> = match &bnd.x {
                    BndX::Let(binders) => binders.iter().map(|b| b.name.clone()).collect(),
                    BndX::Quant(_, binders, _)
                    | BndX::Lambda(binders)
                    | BndX::Choose(binders, _, _) => {
                        binders.iter().map(|b| b.name.clone()).collect()
                    }
                };
                for x in bvars {
                    if map.contains_key(&x) {
                        return err_str(&bnd.span, "variable shadowing not yet supported");
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
    vars: &Vec<Ident>,
    exp: &Exp,
    boxed_params: bool,
) -> Result<Trigs, VirErr> {
    let mut state = State {
        auto_trigger: false,
        boxed_params,
        trigger_vars: vars.iter().cloned().collect(),
        triggers: BTreeMap::new(),
        coverage: HashMap::new(),
    };
    get_manual_triggers(&mut state, exp)?;
    if state.triggers.len() > 0 {
        if state.auto_trigger {
            return err_str(
                span,
                "cannot use both manual triggers (#[trigger] or with_triggers) and #[auto_trigger]",
            );
        }
        let mut trigs: Vec<Trig> = Vec::new();
        for (group, trig) in state.triggers {
            for x in vars {
                if !state.coverage[&group].contains(x) {
                    let group_name = match group {
                        None => "".to_string(),
                        Some(id) => format!(" group {}", id),
                    };
                    return err_string(
                        span,
                        format!(
                            "trigger{} does not cover variable {}",
                            group_name,
                            crate::def::user_local_name(x)
                        ),
                    );
                }
            }
            trigs.push(Arc::new(trig.clone()));
        }
        Ok(Arc::new(trigs))
    } else if boxed_params {
        crate::triggers_auto::build_triggers(ctx, span, vars, exp, state.auto_trigger)
    } else {
        return err_str(span, "manual trigger (#[trigger] or with_triggers) is required");
    }
}
