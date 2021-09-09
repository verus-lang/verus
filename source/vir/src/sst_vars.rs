use crate::ast::{Ident, Typ};
use crate::def::Spanned;
use crate::sst::{ExpX, Stm, StmX};
use std::collections::{HashMap, HashSet};
use std::sync::Arc;

// Compute:
// - which variables have definitely been assigned to up to each statement
// - which variables have been modified within each statement
pub(crate) fn stm_assign(
    declared: &mut HashMap<Ident, Typ>,
    assigned: &mut HashSet<Ident>,
    modified: &mut HashSet<Ident>,
    stm: &Stm,
) -> Stm {
    match &stm.x {
        StmX::Call(_, _, _, Some(dest)) => {
            assigned.insert(dest.var.clone());
            modified.insert(dest.var.clone());
            stm.clone()
        }
        StmX::Call(_, _, _, _) | StmX::Assert(_) | StmX::Assume(_) | StmX::Fuel(_, _) => {
            stm.clone()
        }
        StmX::Decl { ident: x, typ, init, .. } => {
            if declared.contains_key(x) {
                // If we want to support shadowed variables, we should rename them to be unique
                panic!("shadowed variables not yet supported {:?}", &stm.span);
            }
            declared.insert(x.clone(), typ.clone());
            if *init {
                assigned.insert(x.clone());
            }
            stm.clone()
        }
        StmX::Assign(lhs, _) => {
            match &lhs.x {
                ExpX::Var(x) => {
                    assigned.insert(x.clone());
                    modified.insert(x.clone());
                }
                _ => panic!("unexpected lhs {:?} in assign", lhs),
            };
            stm.clone()
        }
        StmX::If(cond, lhs, rhs) => {
            let pre_declared = declared.clone();
            let mut pre_assigned = assigned.clone();

            let lhs = stm_assign(declared, assigned, modified, lhs);
            let lhs_assigned = assigned.clone();
            *assigned = pre_assigned.clone();
            *declared = pre_declared.clone();

            let rhs = rhs.as_ref().map(|s| stm_assign(declared, assigned, modified, s));
            let rhs_assigned = &assigned;

            for x in pre_declared.keys() {
                if lhs_assigned.contains(x) && rhs_assigned.contains(x) && !pre_assigned.contains(x)
                {
                    pre_assigned.insert(x.clone());
                }
            }

            *assigned = pre_assigned;
            *declared = pre_declared;
            Spanned::new(stm.span.clone(), StmX::If(cond.clone(), lhs, rhs))
        }
        StmX::While { cond, body, invs, typ_inv_vars, modified_vars } => {
            let pre_declared = declared.clone();
            let pre_assigned = assigned.clone();
            let mut pre_modified = modified.clone();
            *modified = HashSet::new();
            let body = stm_assign(declared, assigned, modified, body);
            *assigned = pre_assigned;
            *declared = pre_declared;

            assert!(modified_vars.len() == 0);
            let mut modified_vars: Vec<Ident> = Vec::new();
            for x in modified.iter() {
                if declared.contains_key(x) {
                    modified_vars.push(x.clone());
                    pre_modified.insert(x.clone());
                }
            }
            *modified = pre_modified;

            assert!(typ_inv_vars.len() == 0);
            let mut typ_inv_vars: Vec<(Ident, Typ)> = Vec::new();
            for x in assigned.iter() {
                typ_inv_vars.push((x.clone(), declared[x].clone()));
            }
            let while_x = StmX::While {
                cond: cond.clone(),
                body,
                invs: invs.clone(),
                typ_inv_vars: Arc::new(typ_inv_vars),
                modified_vars: Arc::new(modified_vars),
            };
            Spanned::new(stm.span.clone(), while_x)
        }
        StmX::Block(stms) => {
            let pre_declared = declared.clone();
            let mut pre_assigned = assigned.clone();
            let stms: Vec<Stm> =
                stms.iter().map(|s| stm_assign(declared, assigned, modified, s)).collect();
            for x in pre_declared.keys() {
                if assigned.contains(x) && !pre_assigned.contains(x) {
                    pre_assigned.insert(x.clone());
                }
            }
            *assigned = pre_assigned;
            *declared = pre_declared;
            Spanned::new(stm.span.clone(), StmX::Block(Arc::new(stms)))
        }
    }
}
