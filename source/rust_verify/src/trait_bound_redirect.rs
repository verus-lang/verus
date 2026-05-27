use crate::context::Context;
use std::collections::HashMap;
use std::sync::Arc;
use vir::ast::*;
use vir::ast_util::{fun_as_friendly_rust_name, typ_to_diagnostic_str, types_equal};
use vir::messages::*;

pub fn handle_trait_conditional_fns<'tcx>(
    ctxt: &Context<'tcx>,
    krate: &mut KrateX,
) -> Result<(), VirErr> {
    let mut fun_map: HashMap<Fun, Function> = HashMap::new();
    for f in &krate.functions {
        fun_map.insert(f.x.name.clone(), f.clone());
    }
    let mut tr_map: HashMap<Path, Trait> = HashMap::new();
    for tr in &krate.traits {
        tr_map.insert(tr.x.name.clone(), tr.clone());
    }

    for function in &mut krate.functions {
        if let Some(fun) = &function.x.attrs.trait_bound_conditional {
            match &fun_map.get(fun) {
                Some(redirect_function) => {
                    trait_bound_condition_redirect(ctxt, &tr_map, function, redirect_function)?;
                }
                None => {
                    return Err(error(
                        &function.span,
                        format!(
                            "if_trait_bound_then_redirect_to: no function found for path {}",
                            fun_as_friendly_rust_name(fun),
                        ),
                    ));
                }
            }
        }
    }

    Ok(())
}

fn trait_bound_condition_redirect<'tcx>(
    ctxt: &Context<'tcx>,
    tr_map: &HashMap<Path, Trait>,
    function: &mut Function,
    redirect_function: &Function,
) -> Result<(), VirErr> {
    let Some(old_body) = &function.x.body else {
        return Err(error(
            &function.span,
            "'if_trait_bound_then_redirect_to' may only be applied to a function with a body",
        ));
    };
    if function.x.mode != Mode::Spec {
        return Err(error(
            &function.span,
            "'if_trait_bound_then_redirect_to' may only be applied to a spec-mode function",
        ));
    }
    if redirect_function.x.mode != Mode::Spec {
        return Err(error(
            &function.span,
            format!(
                "'if_trait_bound_then_redirect_to': the function `{:}` is not a spec function",
                fun_as_friendly_rust_name(&redirect_function.x.name),
            ),
        ));
    }
    if function.x.typ_params != redirect_function.x.typ_params {
        return Err(error(
            &function.span,
            format!(
                "'if_trait_bound_then_redirect_to': the functions `{:}` and `{:}` must have the same generic type parameters (but not necessarily the same bounds)",
                fun_as_friendly_rust_name(&function.x.name),
                fun_as_friendly_rust_name(&redirect_function.x.name),
            ),
        ));
    }
    if function.x.params.len() != redirect_function.x.params.len() {
        return Err(error(
            &function.span,
            format!(
                "'if_trait_bound_then_redirect_to': the functions `{:}` and `{:}` must have the same number of parameters",
                fun_as_friendly_rust_name(&function.x.name),
                fun_as_friendly_rust_name(&redirect_function.x.name),
            ),
        ));
    }
    for (i, (p1, p2)) in function.x.params.iter().zip(redirect_function.x.params.iter()).enumerate()
    {
        if !types_equal(&p1.x.typ, &p2.x.typ) {
            return Err(error(
                &function.span,
                format!(
                    "'if_trait_bound_then_redirect_to': the functions `{:}` and `{:}` must have the same argument types (different in parameter {i})",
                    fun_as_friendly_rust_name(&function.x.name),
                    fun_as_friendly_rust_name(&redirect_function.x.name),
                )).secondary_label(
                    &p1.span,
                    format!("expected type {:}", typ_to_diagnostic_str(&p1.x.typ)),
                ).secondary_label(
                    &p2.span,
                    format!("got type {:}", typ_to_diagnostic_str(&p2.x.typ)),
                )
            );
        }
    }
    if !types_equal(&function.x.ret.x.typ, &redirect_function.x.ret.x.typ) {
        return Err(error(
            &function.span,
            format!(
                "'if_trait_bound_then_redirect_to': the functions `{:}` and `{:}` must have the same return types",
                fun_as_friendly_rust_name(&function.x.name),
                fun_as_friendly_rust_name(&redirect_function.x.name),
            )).secondary_label(
                &function.x.ret.span,
                format!("expected type {:}", typ_to_diagnostic_str(&function.x.ret.x.typ)),
            ).secondary_label(
                &redirect_function.x.ret.span,
                format!("got type {:}", typ_to_diagnostic_str(&redirect_function.x.ret.x.typ)),
            )
        );
    }

    if !matches!(redirect_function.x.kind, FunctionKind::Static) {
        return Err(error(
            &function.span,
            format!(
                "'if_trait_bound_then_redirect_to': the redirected function should be a normal function, not a trait function",
            ),
        ));
    }

    let span = crate::spans::from_raw_span(&redirect_function.span.raw_span)
        .expect("redirect_function should have a span from this crate");

    let condition = vir::traits::trait_bounds_to_ast(
        tr_map,
        &redirect_function.span,
        &redirect_function.x.typ_bounds,
    );
    let condition = vir::ast_util::conjoin(&redirect_function.span, &condition);
    let condition = crate::automatic_derive::cleanup_span_ids(ctxt, span, &condition);

    let typ_args: Vec<Typ> =
        function.x.typ_params.iter().map(|t| Arc::new(TypX::TypParam(t.clone()))).collect();
    let args: Vec<Expr> = function
        .x
        .params
        .iter()
        .map(|p| ctxt.spanned_typed_new(span, &p.x.typ, ExprX::Var(p.x.name.clone())))
        .collect();
    let redirect_call = ctxt.spanned_typed_new(
        span,
        &old_body.typ,
        ExprX::Call(
            CallTarget::Fun(
                CallTargetKind::Static,
                redirect_function.x.name.clone(),
                Arc::new(typ_args),
                // ImplPaths is empty since trait bounds are assumed to be satisfied by being
                // under the conditional
                Arc::new(vec![]),
                CallTargetAttrs {
                    autospec: AutospecUsage::Final,
                    const_var: false,
                    assume_external_allowed: false,
                },
            ),
            Arc::new(args),
            None,
        ),
    );
    let redirect_call = crate::automatic_derive::cleanup_span_ids(ctxt, span, &redirect_call);

    let new_body = ctxt.spanned_typed_new(
        span,
        &old_body.typ,
        ExprX::If(condition, redirect_call, Some(old_body.clone())),
    );

    Arc::make_mut(function).x.body = Some(new_body);

    Ok(())
}
