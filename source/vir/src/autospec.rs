use crate::ast::{
    AutospecUsage, CallTarget, Expr, ExprX, Fun, Function, Krate, KrateX, SpannedTyped, VirErr,
};
use crate::ast_visitor::VisitorScopeMap;
use crate::util::vec_map_result;
pub use air::ast_util::{ident_binder, str_ident};
use air::scope_map::ScopeMap;
use std::collections::HashMap;
use std::sync::Arc;

fn simplify_one_expr(functions: &HashMap<Fun, Function>, expr: &Expr) -> Result<Expr, VirErr> {
    let new_tgt = |tgt: &Fun, autospec_usage: AutospecUsage| match autospec_usage {
        AutospecUsage::IfMarked => match &functions[tgt].x.attrs.autospec {
            None => tgt.clone(),
            Some(new_tgt) => new_tgt.clone(),
        },
        AutospecUsage::Final => tgt.clone(),
    };
    match &expr.x {
        ExprX::ConstVar(tgt, autospec_usage) => {
            let tgt = new_tgt(tgt, *autospec_usage);
            let var = ExprX::ConstVar(tgt, AutospecUsage::Final);
            Ok(SpannedTyped::new(&expr.span, &expr.typ, var))
        }
        ExprX::Call(CallTarget::Fun(kind, tgt, typs, impl_paths, autospec_usage), args) => {
            let tgt = new_tgt(tgt, *autospec_usage);
            let call = ExprX::Call(
                CallTarget::Fun(
                    kind.clone(),
                    tgt.clone(),
                    typs.clone(),
                    impl_paths.clone(),
                    AutospecUsage::Final,
                ),
                args.clone(),
            );
            Ok(SpannedTyped::new(&expr.span, &expr.typ, call))
        }
        _ => Ok(expr.clone()),
    }
}

fn simplify_function(
    func_map: &HashMap<Fun, Function>,
    function: &Function,
) -> Result<Function, VirErr> {
    let mut map: VisitorScopeMap = ScopeMap::new();
    crate::ast_visitor::map_function_visitor_env(
        &function,
        &mut map,
        &mut (),
        &|_state, _, expr| simplify_one_expr(func_map, expr),
        &|_state, _, stmt| Ok(vec![stmt.clone()]),
        &|_state, typ| Ok(typ.clone()),
    )
}

pub fn resolve_autospec(krate: &Krate) -> Result<Krate, VirErr> {
    let KrateX {
        functions,
        reveal_groups,
        datatypes,
        traits,
        trait_impls,
        modules: module_ids,
        assoc_type_impls,
        external_fns,
        external_types,
        path_as_rust_names,
        arch,
    } = &**krate;

    let mut func_map: HashMap<Fun, Function> = HashMap::new();
    for function in functions.iter() {
        func_map.insert(function.x.name.clone(), function.clone());
    }

    let functions = vec_map_result(functions, |f| simplify_function(&func_map, f))?;

    let datatypes = datatypes.clone();
    let traits = traits.clone();
    let module_ids = module_ids.clone();
    let external_fns = external_fns.clone();
    let external_types = external_types.clone();
    let krate = Arc::new(KrateX {
        functions,
        reveal_groups: reveal_groups.clone(),
        datatypes,
        traits,
        trait_impls: trait_impls.clone(),
        assoc_type_impls: assoc_type_impls.clone(),
        modules: module_ids,
        external_fns,
        external_types,
        path_as_rust_names: path_as_rust_names.clone(),
        arch: arch.clone(),
    });

    Ok(krate)
}
