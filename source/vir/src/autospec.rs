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
            use crate::ast::CallTargetKind;
            let (kind, tgt, typs, impl_paths) = match (kind, autospec_usage) {
                (
                    CallTargetKind::DynamicResolved {
                        resolved,
                        typs: r_typs,
                        impl_paths: r_impl_paths,
                        is_trait_default,
                    },
                    AutospecUsage::IfMarked,
                ) => {
                    if functions.get(resolved).is_some_and(|f| f.x.attrs.autospec.is_some()) {
                        (
                            CallTargetKind::Static,
                            new_tgt(resolved, *autospec_usage),
                            r_typs.clone(),
                            r_impl_paths.clone(),
                        )
                    } else if functions.get(tgt).is_some_and(|f| f.x.attrs.autospec.is_some()) {
                        let new_t = &functions[tgt].x.attrs.autospec.as_ref().unwrap();
                        // calling tgt = T::exec, resolved = impl::exec
                        // new_t = T::spec, so check for new_resolved = impl::spec first
                        let new_resolved_path =
                            resolved.path.pop_segment().push_segment(new_t.path.last_segment());
                        let new_resolved = Arc::new(crate::ast::FunX { path: new_resolved_path });
                        let kind = if !is_trait_default && functions.contains_key(&new_resolved) {
                            CallTargetKind::DynamicResolved {
                                resolved: new_resolved,
                                typs: r_typs.clone(),
                                impl_paths: r_impl_paths.clone(),
                                is_trait_default: *is_trait_default,
                            }
                        } else {
                            CallTargetKind::Dynamic
                        };
                        (kind, new_tgt(tgt, *autospec_usage), typs.clone(), impl_paths.clone())
                    } else {
                        (kind.clone(), tgt.clone(), typs.clone(), impl_paths.clone())
                    }
                }
                _ => {
                    (kind.clone(), new_tgt(tgt, *autospec_usage), typs.clone(), impl_paths.clone())
                }
            };
            let call = ExprX::Call(
                CallTarget::Fun(kind, tgt, typs, impl_paths, AutospecUsage::Final),
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
