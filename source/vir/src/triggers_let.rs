// Z3 inlines `let`s before checking patterns, so a trigger over a let-bound `if`/`else` is
// silently dropped (Z3 only warns). Reject such triggers after selection instead (#740).
// cvc5 accepts `if` in patterns, so this check is Z3-only.

use crate::ast::{VarIdent, VirErr};
use crate::def::user_local_name;
use crate::messages::error_with_label;
use crate::sst::{BndX, Exp, ExpX, FunctionSst, Stm, Trigs};
use crate::sst_util::free_vars_exp;
use crate::sst_visitor::{
    NoScoper, Visitor, VisitorControlFlow, VisitorScopeMap, Walk, exp_visitor_dfs,
};
use std::collections::{HashMap, HashSet};

fn contains_if(exp: &Exp) -> bool {
    let mut map = VisitorScopeMap::new();
    let res = exp_visitor_dfs::<(), _>(exp, &mut map, &mut |e, _| match &e.x {
        ExpX::If(..) => VisitorControlFlow::Stop(()),
        _ => VisitorControlFlow::Recurse,
    });
    matches!(res, VisitorControlFlow::Stop(()))
}

struct LetTriggerChecker {
    // let-bound variables in scope
    let_defs: HashMap<VarIdent, Exp>,
}

impl LetTriggerChecker {
    // the `if`/`else` that `x` is (transitively) let-bound to, if any
    fn resolve_to_if(&self, x: &VarIdent, visited: &mut HashSet<VarIdent>) -> Option<Exp> {
        if !visited.insert(x.clone()) {
            return None;
        }
        let val = self.let_defs.get(x)?;
        if contains_if(val) {
            return Some(val.clone());
        }
        free_vars_exp(val).keys().find_map(|y| self.resolve_to_if(y, visited))
    }

    fn check_trigs(&self, trigs: &Trigs) -> Result<(), VirErr> {
        for t in trigs.iter().flat_map(|trig| trig.iter()) {
            for x in free_vars_exp(t).keys() {
                if let Some(if_exp) = self.resolve_to_if(x, &mut HashSet::new()) {
                    let msg = format!(
                        "trigger contains an `if`/`else` after inlining the let-bound variable \
                         `{}`; Z3 would silently ignore this trigger",
                        user_local_name(x),
                    );
                    return Err(error_with_label(&t.span, msg, "trigger chosen here")
                        .secondary_label(&if_exp.span, "...bound to this `if`/`else`"));
                }
            }
        }
        Ok(())
    }
}

impl Visitor<Walk, VirErr, NoScoper> for LetTriggerChecker {
    fn visit_stm(&mut self, stm: &Stm) -> Result<(), VirErr> {
        self.visit_stm_rec(stm)
    }

    fn visit_exp(&mut self, exp: &Exp) -> Result<(), VirErr> {
        let ExpX::Bind(bnd, body) = &exp.x else {
            return self.visit_exp_rec(exp);
        };
        match &bnd.x {
            BndX::Let(binders) => {
                for b in binders.iter() {
                    self.visit_exp(&b.a)?;
                }
                let saved: Vec<_> = binders
                    .iter()
                    .map(|b| (b.name.clone(), self.let_defs.insert(b.name.clone(), b.a.clone())))
                    .collect();
                let res = self.visit_exp(body);
                for (name, prev) in saved {
                    match prev {
                        Some(prev) => self.let_defs.insert(name, prev),
                        None => self.let_defs.remove(&name),
                    };
                }
                res
            }
            BndX::Quant(_, _, trigs, _) | BndX::Lambda(_, trigs) => {
                self.check_trigs(trigs)?;
                self.visit_exp(body)
            }
            BndX::Choose(_, trigs, cond) => {
                self.check_trigs(trigs)?;
                self.visit_exp(cond)?;
                self.visit_exp(body)
            }
        }
    }
}

pub(crate) fn check_let_bound_if_triggers(function: &FunctionSst) -> Result<(), VirErr> {
    LetTriggerChecker { let_defs: HashMap::new() }.visit_function(function)
}
