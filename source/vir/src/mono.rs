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
use crate::ast::{Function, Krate, KrateX};
use crate::poly;
use crate::{
    ast::{CallTarget, ExprX, Fun, Typs},
    ast_visitor::{self, VisitorScopeMap},
    context::Ctx,
};
use air::scope_map::ScopeMap;
use std::collections::{HashMap, HashSet};

pub(crate) fn collect_specializations_from_function(
    ctx: &Ctx,
    function: &Function,
) -> Vec<(Fun, Typs)> {
    let mut invocations: Vec<(Fun, Typs)> = vec![];
    let Some(body) = &function.x.body else {
        return vec![];
    };
    let mut map: VisitorScopeMap = ScopeMap::new();
    ast_visitor::expr_visitor_dfs::<(), _>(body, &mut map, &mut |scope_map, expr| {
        match &expr.x {
            ExprX::Call(CallTarget::Fun(_, f, typs, _, _), _) => {
                invocations.push((f.clone(), typs.clone()));
            }
            _ => (),
        }
        ast_visitor::VisitorControlFlow::Recurse
    });
    invocations
}
/**
Collect all polymorphic function invocations in a module
 */
pub fn mono_krate_for_module(ctx: &mut Ctx, krate: &Krate) -> HashMap<Fun, Vec<Typs>> {
    let mut invocations: HashMap<Fun, Vec<Typs>> = HashMap::new();
    let KrateX {
        functions,
        reveal_groups,
        datatypes,
        traits,
        trait_impls,
        assoc_type_impls,
        modules: module_ids,
        external_fns,
        external_types,
        path_as_rust_names,
        arch,
    } = &**krate;
    for f in functions.iter() {
        for (fun, typs) in collect_specializations_from_function(ctx, f).into_iter() {
            invocations.entry(fun).or_insert_with(Vec::new).push(typs)
        }
    }
    invocations
}
