use crate::ast::{
    AutospecUsage, CallTarget, Expr, ExprX, Fun, Function, Ident, Krate, KrateX, SpannedTyped, Typ,
    VirErr,
};
use crate::util::vec_map_result;
pub use air::ast_util::{ident_binder, str_ident};
pub use air::messages::error as msg_error;
use air::scope_map::ScopeMap;
use std::collections::HashMap;
use std::sync::Arc;

fn simplify_one_expr(functions: &HashMap<Fun, Function>, expr: &Expr) -> Result<Expr, VirErr> {
    match &expr.x {
        ExprX::Call(CallTarget::Fun(kind, tgt, typs, impl_paths, autospec_usage), args) => {
            let tgt = match *autospec_usage {
                AutospecUsage::IfMarked => match &functions[tgt].x.attrs.autospec {
                    None => tgt,
                    Some(new_tgt) => new_tgt,
                },
                AutospecUsage::Final => tgt,
            };

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
    let mut map: ScopeMap<Ident, Typ> = ScopeMap::new();
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
        datatypes,
        traits,
        trait_impls,
        module_ids,
        assoc_type_impls,
        external_fns,
        external_types,
        path_as_rust_names,
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
        datatypes,
        traits,
        trait_impls: trait_impls.clone(),
        assoc_type_impls: assoc_type_impls.clone(),
        module_ids,
        external_fns,
        external_types,
        path_as_rust_names: path_as_rust_names.clone(),
    });

    Ok(krate)
}
