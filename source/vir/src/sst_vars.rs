use crate::ast::{Typ, UnaryOpr, VarIdent};
use crate::def::Spanned;
use crate::sst::{Dest, Exp, ExpX, Stm, StmX, Stms, UniqueIdent};
use crate::sst_visitor::exp_visitor_check;
use air::scope_map::ScopeMap;
use indexmap::{IndexMap, IndexSet};
use std::sync::Arc;

fn to_ident_set(input: &IndexSet<UniqueIdent>) -> IndexSet<VarIdent> {
    let mut output = IndexSet::new();
    for item in input {
        output.insert(item.clone());
    }
    output
}

// Compute:
// - which variables have definitely been assigned to up to each statement
// - which variables have been modified within each statement
pub type AssignMap = IndexMap<*const Spanned<StmX>, IndexSet<VarIdent>>;

pub(crate) fn get_loc_var(exp: &Exp) -> UniqueIdent {
    match &exp.x {
        ExpX::Loc(x) => get_loc_var(x),
        ExpX::UnaryOpr(UnaryOpr::Field { .. }, x) => get_loc_var(x),
        ExpX::UnaryOpr(UnaryOpr::Box(_) | UnaryOpr::Unbox(_), x) => get_loc_var(x),
        ExpX::VarLoc(x) => x.clone(),
        _ => panic!("lhs {:?} unsupported", exp),
    }
}

pub(crate) fn stm_assign(
    assign_map: &mut AssignMap,
    declared: &IndexMap<UniqueIdent, Typ>,
    assigned: &mut IndexSet<UniqueIdent>,
    modified: &mut IndexSet<UniqueIdent>,
    stm: &Stm,
) -> Stm {
    let result = match &stm.x {
        StmX::Call { args, dest, .. } => {
            if let Some(dest) = dest {
                let var: UniqueIdent = get_loc_var(&dest.dest);
                assigned.insert(var.clone());
                if !dest.is_init {
                    modified.insert(var.clone());
                }
            }
            for arg in args.iter() {
                // Search for any ExpX::Loc in the arg, which might be modified.
                // Given current limitations, I think the only way this can happen
                // is if either
                //    arg.x = ExpX::Loc(loc)
                // or
                //    arg.x = UnaryOpr(Box, ExpX::Loc(loc))

                exp_visitor_check::<(), _>(arg, &mut ScopeMap::new(), &mut |e, _| {
                    if let ExpX::Loc(loc) = &e.x {
                        let var = get_loc_var(loc);
                        modified.insert(var);
                    }
                    Ok(())
                })
                .unwrap();
            }
            stm.clone()
        }
        StmX::AssertQuery { mode, typ_inv_exps, typ_inv_vars, body } => {
            assert!(typ_inv_vars.len() == 0);
            let vars = crate::sst_util::free_vars_exps(typ_inv_exps);
            let mode = *mode;
            let typ_inv_exps = Arc::new(vec![]);
            let typ_inv_vars = Arc::new(
                declared.clone().into_iter().filter(|(x, _)| vars.contains_key(x)).collect(),
            );
            let body = body.clone();
            stm.new_x(StmX::AssertQuery { mode, typ_inv_exps, typ_inv_vars, body })
        }
        StmX::Assert(..)
        | StmX::AssertBitVector { .. }
        | StmX::AssertCompute(..)
        | StmX::Assume(_)
        | StmX::Fuel(..)
        | StmX::RevealString(_)
        | StmX::Return { .. }
        | StmX::Air(_) => stm.clone(),
        StmX::Assign { lhs: Dest { dest, is_init }, rhs: _ } => {
            let var = get_loc_var(dest);
            assigned.insert(var.clone());
            if !is_init {
                modified.insert(var.clone());
            }
            stm.clone()
        }
        StmX::DeadEnd(s) => {
            let s = stm_assign(assign_map, declared, assigned, modified, s);
            Spanned::new(stm.span.clone(), StmX::DeadEnd(s))
        }
        StmX::BreakOrContinue { label: _, is_break: _ } => stm.clone(),
        StmX::ClosureInner { body, typ_inv_vars } => {
            let pre_modified = modified.clone();
            let pre_assigned = assigned.clone();
            let body = stm_assign(assign_map, declared, assigned, modified, body);
            *assigned = pre_assigned;
            *modified = pre_modified;

            Spanned::new(
                stm.span.clone(),
                StmX::ClosureInner { body, typ_inv_vars: typ_inv_vars.clone() },
            )
        }
        StmX::If(cond, lhs, rhs) => {
            let mut pre_assigned = assigned.clone();

            let lhs = stm_assign(assign_map, declared, assigned, modified, lhs);
            let lhs_assigned = assigned.clone();
            *assigned = pre_assigned.clone();

            let rhs = rhs.as_ref().map(|s| stm_assign(assign_map, declared, assigned, modified, s));
            let rhs_assigned = &assigned;

            for x in declared.keys() {
                if lhs_assigned.contains(x) && rhs_assigned.contains(x) && !pre_assigned.contains(x)
                {
                    pre_assigned.insert(x.clone());
                }
            }

            *assigned = pre_assigned;
            Spanned::new(stm.span.clone(), StmX::If(cond.clone(), lhs, rhs))
        }
        StmX::Loop {
            loop_isolation,
            is_for_loop,
            id,
            label,
            cond,
            body,
            invs,
            decrease,
            typ_inv_vars,
            modified_vars,
        } => {
            let mut pre_modified = modified.clone();
            *modified = IndexSet::new();
            let cond = if let Some((cond_stm, cond_exp)) = cond {
                let cond_stm = stm_assign(assign_map, declared, assigned, modified, cond_stm);
                Some((cond_stm, cond_exp.clone()))
            } else {
                None
            };

            let pre_assigned = assigned.clone();
            let body = stm_assign(assign_map, declared, assigned, modified, body);
            *assigned = pre_assigned;

            assert!(modified_vars.len() == 0);
            let mut modified_vars: Vec<UniqueIdent> = Vec::new();
            for x in modified.iter() {
                if declared.contains_key(x) {
                    modified_vars.push(x.clone());
                    pre_modified.insert(x.clone());
                }
            }
            *modified = pre_modified;

            assert!(typ_inv_vars.len() == 0);
            let mut typ_inv_vars: Vec<(UniqueIdent, Typ)> = Vec::new();
            for x in assigned.iter() {
                typ_inv_vars.push((x.clone(), declared[x].clone()));
            }
            let loop_x = StmX::Loop {
                loop_isolation: *loop_isolation,
                is_for_loop: *is_for_loop,
                id: *id,
                label: label.clone(),
                cond,
                body,
                invs: invs.clone(),
                decrease: decrease.clone(),
                typ_inv_vars: Arc::new(typ_inv_vars),
                modified_vars: Arc::new(modified_vars),
            };
            Spanned::new(stm.span.clone(), loop_x)
        }
        StmX::OpenInvariant(ns_exp, body_stm) => {
            let body_stm = stm_assign(assign_map, declared, assigned, modified, body_stm);
            Spanned::new(stm.span.clone(), StmX::OpenInvariant(ns_exp.clone(), body_stm))
        }
        StmX::Block(stms) => {
            let mut pre_assigned = assigned.clone();
            let stms = stms_assign(assign_map, declared, assigned, modified, stms);
            for x in declared.keys() {
                if assigned.contains(x) && !pre_assigned.contains(x) {
                    pre_assigned.insert(x.clone());
                }
            }
            *assigned = pre_assigned;
            Spanned::new(stm.span.clone(), StmX::Block(stms))
        }
    };

    assign_map.insert(Arc::as_ptr(&result), to_ident_set(assigned));
    result
}

fn stms_assign(
    assign_map: &mut AssignMap,
    declared: &IndexMap<UniqueIdent, Typ>,
    assigned: &mut IndexSet<UniqueIdent>,
    modified: &mut IndexSet<UniqueIdent>,
    stms: &Stms,
) -> Stms {
    let stms: Vec<Stm> =
        stms.iter().map(|s| stm_assign(assign_map, declared, assigned, modified, s)).collect();
    Arc::new(stms)
}
