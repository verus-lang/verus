/*!
Handles monomorphization, where we produce specialized code from a polymorphic function.

For example, if we have
```no_run
spec fn f<A>(a: A) -> A { ... }

proof fn proof1<B>(b: B) {
  let x = f(b);
  let y = f(true);
}
```
we need to generate two functions, `(f Poly Poly)`, and `(f bool bool)` in the
emitted SMT code. This is done to meet 3 design criteria:
1. We want to verify a function exactly once, so we cannot specialize `proof1`
    on demand every time someone calls it.
2. We want to leverage SMT solver's capability as much as possible. Coercing a
primitive type such as `bool` or `int` to poly, even though we know `f(bool)` is
specialized, hinders this.
3. We want to ensure the generated AIR code can be type-checked by AIR.
 */
use crate::ast::Fun;
use crate::ast_util::n_types_equal;
use crate::sst::{CallFun, Exp, ExpX, KrateSstX, Stm};
use crate::sst_visitor::{self, Visitor};
use crate::{
    ast::{Ident, TypX, Typs},
    sst::{FunctionSst, KrateSst},
};
use std::collections::{HashMap, HashSet};
use std::sync::Arc;

/**
This stores one instance of specialization of a particular function. This
structure handles deduplication of essentially isomorphic call sites.
 */
#[derive(Debug, Hash)]
pub struct Specialization {
    typs: Typs,
}
impl Specialization {
    pub fn empty() -> Self {
        Self { typs: Arc::new(vec![]) }
    }
    pub fn from_exp(exp: &ExpX) -> Option<(&Fun, Self)> {
        let ExpX::Call(CallFun::Fun(fun, _) | CallFun::Recursive(fun), typs, _) = exp else {
            return None;
        };
        let result = Self { typs: typs.clone() };
        Some((fun, result))
    }
    pub fn transform_ident(&self, ident: Ident) -> Ident {
        if self.typs.is_empty() {
            return ident;
        }
        // FIXME: Find a way to generate unique names given type arguments
        let suffix = if n_types_equal(&self.typs, &Arc::new(vec![Arc::new(TypX::Bool)])) {
            "_bool"
        } else {
            "_mystery"
        };
        Arc::new(ident.as_ref().clone() + suffix)
    }
    pub fn comment(&self) -> String {
        format!(" specialized to {:?}", &self.typs)
    }
}
impl PartialEq for Specialization {
    fn eq(&self, other: &Self) -> bool {
        n_types_equal(&self.typs, &other.typs)
    }
}
impl Eq for Specialization {}

/**
Utility for walking through the expression tree.

This must be doubly recursive on both expressions and statements, hence its
structure mirrors `StmExpVisitorDfs`.
 */
struct SpecializationVisitor {
    invocations: Vec<(Fun, Specialization)>,
}
impl SpecializationVisitor {
    fn new() -> Self {
        Self { invocations: vec![] }
    }
}
impl Visitor<sst_visitor::Walk, (), sst_visitor::NoScoper> for SpecializationVisitor {
    fn visit_exp(&mut self, exp: &Exp) -> Result<(), ()> {
        if let Some((fun, spec)) = Specialization::from_exp(&exp.x) {
            self.invocations.push((fun.clone(), spec));
        }
        self.visit_exp_rec(exp)
    }
    fn visit_stm(&mut self, stm: &Stm) -> Result<(), ()> {
        self.visit_stm_rec(stm)
    }
}

pub(crate) fn collect_specializations_from_function(
    function: &FunctionSst,
) -> Vec<(Fun, Specialization)> {
    let mut visitor = SpecializationVisitor::new();
    visitor.visit_function(function).unwrap();
    visitor.invocations
}
/**
Collect all polymorphic function invocations in a module
 */
pub fn mono_krate_for_module(krate: &KrateSst) -> HashMap<Fun, HashSet<Specialization>> {
    let mut invocations: HashMap<Fun, HashSet<Specialization>> = HashMap::new();
    let KrateSstX { functions, .. } = &**krate;
    for f in functions.iter() {
        for (fun, spec) in collect_specializations_from_function(f).into_iter() {
            invocations.entry(fun).or_insert_with(HashSet::new).insert(spec);
        }
    }
    invocations
}
