use crate::sst::{Exp, ExpX, Stm, UniqueIdent};
use std::collections::HashSet;

pub(crate) fn referenced_vars_exp(exp: &Exp) -> HashSet<UniqueIdent> {
    referenced_vars_exp_sm(exp, &mut crate::sst_visitor::VisitorScopeMap::new())
}

fn referenced_vars_exp_sm(
    exp: &Exp,
    scope_map: &mut crate::sst_visitor::VisitorScopeMap,
) -> HashSet<UniqueIdent> {
    let mut vars: HashSet<UniqueIdent> = HashSet::new();
    crate::sst_visitor::exp_visitor_dfs::<(), _>(exp, scope_map, &mut |e, _| {
        match &e.x {
            ExpX::Var(x) | ExpX::VarLoc(x) => {
                vars.insert(x.clone());
            }
            _ => (),
        }
        crate::sst_visitor::VisitorControlFlow::Recurse
    });
    vars
}

pub(crate) fn referenced_vars_stm(stm: &Stm) -> HashSet<UniqueIdent> {
    let mut vars: HashSet<UniqueIdent> = HashSet::new();
    crate::sst_visitor::stm_exp_visitor_dfs::<(), _>(stm, &mut |exp, scope_map| {
        vars.extend(referenced_vars_exp_sm(exp, scope_map).into_iter());
        crate::sst_visitor::VisitorControlFlow::Recurse
    });
    vars
}
