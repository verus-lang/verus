use crate::ast::{
    AutospecUsage, CallTarget, Expr, ExprX, Fun, Function, FunctionStub, SpannedTyped, VirErr,
};
use crate::ast_visitor::VisitorScopeMap;
pub use air::ast_util::{ident_binder, str_ident};
use air::scope_map::ScopeMap;
use std::collections::HashMap;
use std::sync::Arc;

fn simplify_one_expr(functions: &HashMap<Fun, FunctionStub>, expr: &Expr) -> Result<Expr, VirErr> {
    // AssumeExternal
    let expr = match &expr.x {
        // TODO: ConstVar
        ExprX::Call {
            target: CallTarget::Fun(kind, tgt, _typs, _impl_paths, attrs),
            args,
            post_args,
            body,
            unwind_path,
        } => {
            let tgt_func = functions.get(tgt);
            let mut found = tgt_func.is_some();
            match kind {
                crate::ast::CallTargetKind::DynamicResolved { resolved, .. } => {
                    found = found
                        && (functions.contains_key(resolved)
                            || tgt_func.unwrap().x.kind.has_default());
                }
                _ => {}
            };
            if found {
                expr.clone()
            } else if attrs.assume_external_allowed {
                let target = CallTarget::AssumeExternal;
                expr.new_x(ExprX::Call {
                    target,
                    args: args.clone(),
                    post_args: post_args.clone(),
                    body: body.clone(),
                    unwind_path: unwind_path.clone(),
                })
            } else {
                // should have been flagged by well_formed before reaching here
                unreachable!("internal error: function {:?} not found", tgt)
            }
        }
        _ => expr.clone(),
    };

    // autospec
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
        ExprX::Call {
            target: CallTarget::Fun(kind, tgt, typs, impl_paths, attrs),
            args,
            post_args,
            body,
            unwind_path,
        } => {
            use crate::ast::CallTargetKind;
            let autospec_usage = attrs.autospec;
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
                            new_tgt(resolved, autospec_usage),
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
                        (kind, new_tgt(tgt, autospec_usage), typs.clone(), impl_paths.clone())
                    } else {
                        (kind.clone(), tgt.clone(), typs.clone(), impl_paths.clone())
                    }
                }
                _ => (kind.clone(), new_tgt(tgt, autospec_usage), typs.clone(), impl_paths.clone()),
            };
            let attrs = crate::ast::CallTargetAttrs {
                autospec: AutospecUsage::Final,
                const_var: attrs.const_var,
                assume_external_allowed: false,
            };
            let call = ExprX::Call {
                target: CallTarget::Fun(kind, tgt, typs, impl_paths, attrs),
                args: args.clone(),
                post_args: post_args.clone(),
                body: body.clone(),
                unwind_path: unwind_path.clone(),
            };
            Ok(SpannedTyped::new(&expr.span, &expr.typ, call))
        }
        _ => Ok(expr.clone()),
    }
}

pub fn resolve_autospec_in_function(
    func_map: &HashMap<Fun, FunctionStub>,
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
        &|_state, _, place| Ok(place.clone()),
        &|_state, _, pat| Ok(pat.clone()),
    )
}
