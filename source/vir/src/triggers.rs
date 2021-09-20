use crate::ast::{BinaryOp, Ident, UnaryOp, UnaryOpr, VirErr};
use crate::ast_util::{err_str, err_string};
use crate::context::Ctx;
use crate::sst::{BndX, Exp, ExpX, Trig, Trigs};
use air::ast::Span;
use air::scope_map::ScopeMap;
use std::collections::{HashMap, HashSet};
use std::sync::Arc;

// Manual triggers
struct State {
    trigger_vars: HashSet<Ident>, // variables the triggers must cover
    triggers: HashMap<Option<u64>, Vec<Exp>>, // user-specified triggers
    coverage: HashMap<Option<u64>, HashSet<Ident>>, // trigger_vars covered by each trigger
}

fn check_trigger_expr(exp: &Exp, free_vars: &mut HashSet<Ident>) -> Result<(), VirErr> {
    match &exp.x {
        ExpX::Call(_, _, _, _) | ExpX::Field { .. } | ExpX::Unary(UnaryOp::Trigger(_), _) => {}
        // REVIEW: Z3 allows some arithmetic, but it's not clear we want to allow it
        _ => {
            return err_str(&exp.span, "trigger must be a function call or a field access");
        }
    }
    let mut f = |exp: &Exp, _: &mut _| match &exp.x {
        ExpX::Const(_) | ExpX::Call(_, _, _, _) | ExpX::Field { .. } | ExpX::Ctor(_, _, _) => {
            Ok(exp.clone())
        }
        ExpX::Var(x) => {
            free_vars.insert(x.clone());
            Ok(exp.clone())
        }
        ExpX::Old(_, _) => panic!("internal error: Old"),
        ExpX::Unary(op, _) => match op {
            UnaryOp::Trigger(_) | UnaryOp::Clip(_) => Ok(exp.clone()),
            UnaryOp::Not => err_str(&exp.span, "triggers cannot contain boolean operators"),
        },
        ExpX::UnaryOpr(op, _) => match op {
            UnaryOpr::Box(_) | UnaryOpr::Unbox(_) => Ok(exp.clone()),
        },
        ExpX::Binary(op, _, _) => {
            use BinaryOp::*;
            match op {
                And | Or | Implies | Eq | Ne => {
                    err_str(&exp.span, "triggers cannot contain boolean operators")
                }
                Le | Ge | Lt | Gt => Ok(exp.clone()),
                Add | Sub | Mul | EuclideanDiv | EuclideanMod => Ok(exp.clone()),
            }
        }
        ExpX::If(_, _, _) => err_str(&exp.span, "triggers cannot contain if/else"),
        ExpX::Bind(_, _) => err_str(&exp.span, "triggers cannot contain let/forall/exists"),
    };
    let mut map: ScopeMap<Ident, bool> = ScopeMap::new();
    let _ = crate::sst_visitor::map_exp_visitor_bind(exp, &mut map, &mut f)?;
    Ok(())
}

fn get_manual_triggers(state: &mut State, exp: &Exp) -> Result<(), VirErr> {
    let mut map: ScopeMap<Ident, bool> = ScopeMap::new();
    map.push_scope(false);
    for x in &state.trigger_vars {
        map.insert(x.clone(), true).expect("duplicate bound variables");
    }
    let mut f = |exp: &Exp, map: &mut ScopeMap<Ident, bool>| match &exp.x {
        ExpX::Unary(UnaryOp::Trigger(group), e1) => {
            let mut free_vars: HashSet<Ident> = HashSet::new();
            check_trigger_expr(e1, &mut free_vars)?;
            for x in &free_vars {
                if map.get(x).cloned() == Some(true) && !state.trigger_vars.contains(x) {
                    // If the trigger contains variables declared by a nested quantifier,
                    // it must be the nested quantifier's trigger, not ours.
                    return Ok(exp.clone());
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
            Ok(exp.clone())
        }
        ExpX::Bind(bnd, _) => {
            let bvars: Vec<Ident> = match &bnd.x {
                BndX::Let(binders) => binders.iter().map(|b| b.name.clone()).collect(),
                BndX::Quant(_, binders, _) => binders.iter().map(|b| b.name.clone()).collect(),
            };
            for x in bvars {
                if map.contains_key(&x) {
                    return err_str(&bnd.span, "variable shadowing not yet supported");
                }
            }
            Ok(exp.clone())
        }
        _ => Ok(exp.clone()),
    };
    let _ = crate::sst_visitor::map_exp_visitor_bind(exp, &mut map, &mut f)?;
    map.pop_scope();
    assert_eq!(map.num_scopes(), 0);
    Ok(())
}

pub(crate) fn build_triggers(
    ctx: &Ctx,
    span: &Span,
    vars: &Vec<Ident>,
    exp: &Exp,
) -> Result<Trigs, VirErr> {
    let mut state = State {
        trigger_vars: vars.iter().cloned().collect(),
        triggers: HashMap::new(),
        coverage: HashMap::new(),
    };
    get_manual_triggers(&mut state, exp)?;
    if state.triggers.len() > 0 {
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
                        format!("trigger{} does not cover variable {}", group_name, x),
                    );
                }
            }
            trigs.push(Arc::new(trig.clone()));
        }
        Ok(Arc::new(trigs))
    } else {
        crate::triggers_auto::build_triggers(ctx, span, vars, exp)
    }
}
