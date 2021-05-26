use crate::ast::{BinaryOp, Ident, UnaryOp, UnaryOpr, VirErr};
use crate::ast_util::{err_str, err_string};
use crate::context::Ctx;
use crate::sst::{Bnd, BndX, Exp, ExpX, Trig, Trigs};
use air::ast::Span;
use std::collections::{HashMap, HashSet};
use std::rc::Rc;

// Manual triggers
struct State {
    trigger_vars: HashSet<Ident>, // variables the triggers must cover
    triggers: HashMap<Option<u64>, Vec<Exp>>, // user-specified triggers
    coverage: HashMap<Option<u64>, HashSet<Ident>>, // trigger_vars covered by each trigger
}

fn check_trigger_expr(exp: &Exp, free_vars: &mut HashSet<Ident>) -> Result<(), VirErr> {
    let mut fb = |bnd: &Bnd| Ok(bnd.clone());
    match &exp.x {
        ExpX::Call(_, _, _) | ExpX::Field { .. } | ExpX::Unary(UnaryOp::Trigger(_), _) => {}
        // REVIEW: Z3 allows some arithmetic, but it's not clear we want to allow it
        _ => {
            return err_str(&exp.span, "trigger must be a function call or a field access");
        }
    }
    let mut f = |exp: &Exp| match &exp.x {
        ExpX::Const(_) | ExpX::Call(_, _, _) | ExpX::Field { .. } | ExpX::Ctor(_, _, _) => {
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
    let _ = crate::sst_visitor::map_exp_visitor_bind(exp, &mut fb, &mut f)?;
    Ok(())
}

fn get_manual_triggers(state: &mut State, exp: &Exp) -> Result<(), VirErr> {
    let quant_vars: HashSet<Ident> = state.trigger_vars.clone();
    let quant_vars_cell = std::cell::RefCell::new(quant_vars);
    let mut fb = |bnd: &Bnd| match &bnd.x {
        BndX::Let(binders) => {
            let quant_vars = quant_vars_cell.borrow();
            for binder in binders.iter() {
                if quant_vars.contains(&*binder.name) {
                    return err_string(
                        &bnd.span,
                        format!(
                            "variable {} cannot shadow quantifier variable with same name",
                            binder.name
                        ),
                    );
                }
            }
            Ok(bnd.clone())
        }
        BndX::Quant(_, binders, _) => {
            let mut quant_vars = quant_vars_cell.borrow_mut();
            for binder in binders.iter() {
                if quant_vars.contains(&*binder.name) {
                    return err_string(
                        &bnd.span,
                        format!(
                            "variable {} cannot shadow quantifier variable with same name",
                            binder.name
                        ),
                    );
                }
                quant_vars.insert(binder.name.clone());
            }
            Ok(bnd.clone())
        }
    };
    let mut f = |exp: &Exp| match &exp.x {
        ExpX::Unary(UnaryOp::Trigger(group), e1) => {
            let quant_vars = quant_vars_cell.borrow();
            let mut free_vars: HashSet<Ident> = HashSet::new();
            check_trigger_expr(e1, &mut free_vars)?;
            for x in &free_vars {
                if quant_vars.contains(x) && !state.trigger_vars.contains(x) {
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
        ExpX::Bind(bnd, _) => match &bnd.x {
            BndX::Quant(_, binders, _) => {
                let mut quant_vars = quant_vars_cell.borrow_mut();
                for binder in binders.iter() {
                    quant_vars.remove(&binder.name);
                }
                Ok(exp.clone())
            }
            _ => Ok(exp.clone()),
        },
        _ => Ok(exp.clone()),
    };
    let _ = crate::sst_visitor::map_exp_visitor_bind(exp, &mut fb, &mut f)?;
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
            trigs.push(Rc::new(trig.clone()));
        }
        Ok(Rc::new(trigs))
    } else {
        crate::triggers_auto::build_triggers(ctx, span, vars, exp)
    }
}
