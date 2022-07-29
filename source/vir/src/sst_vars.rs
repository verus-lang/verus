use crate::ast::{Typ, UnaryOpr};
use crate::def::Spanned;
use crate::sst::{Dest, Exp, ExpX, Stm, StmX, Stms, UniqueIdent};
use std::collections::{HashMap, HashSet};
use std::sync::Arc;

fn to_ident_set(input: &HashSet<UniqueIdent>) -> HashSet<Arc<String>> {
    let mut output = HashSet::new();
    for item in input {
        output.insert(item.name.clone());
    }
    output
}

// Compute:
// - which variables have definitely been assigned to up to each statement
// - which variables have been modified within each statement
pub type AssignMap = HashMap<*const Spanned<StmX>, HashSet<Arc<String>>>;

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
    declared: &HashMap<UniqueIdent, Typ>,
    assigned: &mut HashSet<UniqueIdent>,
    modified: &mut HashSet<UniqueIdent>,
    stm: &Stm,
) -> Stm {
    let result = match &stm.x {
        StmX::Call(_, _, _, _, Some(dest)) => {
            let var: UniqueIdent = get_loc_var(&dest.dest);
            assigned.insert(var.clone());
            if !dest.is_init {
                modified.insert(var.clone());
            }
            stm.clone()
        }
        StmX::Call(..)
        | StmX::Assert(..)
        | StmX::AssertBV(..)
        | StmX::AssertBitVector { .. }
        | StmX::AssertQuery { .. }
        | StmX::Assume(_)
        | StmX::Fuel(..) => stm.clone(),
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
        StmX::While { cond_stms, cond_exp, body, invs, typ_inv_vars, modified_vars } => {
            let mut pre_modified = modified.clone();
            *modified = HashSet::new();
            let cond_stms = stms_assign(assign_map, declared, assigned, modified, cond_stms);

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
            let while_x = StmX::While {
                cond_stms,
                cond_exp: cond_exp.clone(),
                body,
                invs: invs.clone(),
                typ_inv_vars: Arc::new(typ_inv_vars),
                modified_vars: Arc::new(modified_vars),
            };
            Spanned::new(stm.span.clone(), while_x)
        }
        StmX::OpenInvariant(inv, ident, ty, body_stm, atomicity) => {
            assigned.insert(ident.clone());
            modified.insert(ident.clone());
            let body_stm = stm_assign(assign_map, declared, assigned, modified, body_stm);
            Spanned::new(
                stm.span.clone(),
                StmX::OpenInvariant(inv.clone(), ident.clone(), ty.clone(), body_stm, *atomicity),
            )
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

pub(crate) fn stms_assign(
    assign_map: &mut AssignMap,
    declared: &HashMap<UniqueIdent, Typ>,
    assigned: &mut HashSet<UniqueIdent>,
    modified: &mut HashSet<UniqueIdent>,
    stms: &Stms,
) -> Stms {
    let stms: Vec<Stm> =
        stms.iter().map(|s| stm_assign(assign_map, declared, assigned, modified, s)).collect();
    Arc::new(stms)
}
