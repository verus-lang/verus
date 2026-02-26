use crate::ast::{
    Expr, ExprX, Fun, Function, FunctionKind, Krate, MaskSpec, Mode, Path, Quant, SpannedTyped,
    StmtX, Trait, TypX, UnwindSpec, VarBinderX, VirErr,
};
use crate::ast_util::fun_as_friendly_rust_name;
use crate::context::Ctx;
use crate::def::Spanned;
use crate::messages::Span;
use crate::messages::error;
use crate::sst::{BndX, CallFun, Exp, ExpX};
use std::collections::HashMap;
use std::sync::Arc;

pub fn check_safe_api(krate: &Krate) -> Result<(), VirErr> {
    let mut trait_map = HashMap::<Path, Trait>::new();
    for t in krate.traits.iter() {
        trait_map.insert(t.x.name.clone(), t.clone());
    }
    let mut function_map = HashMap::<Fun, Function>::new();
    for f in krate.functions.iter() {
        function_map.insert(f.x.name.clone(), f.clone());
    }

    for function in krate.functions.iter() {
        if matches!(*function.x.ret.x.typ, TypX::Opaque { .. }) {
            return Err(error(
                &function.span,
                &format!(
                    "The verifier does not support opaque types together with the check-api-safety flag: `{:}`. Unverified, safe client code may be able to call this function without satisfying the precondition.",
                    fun_as_friendly_rust_name(&function.x.name),
                ),
            ));
        }

        if function.x.mode == Mode::Exec
            && function.x.visibility.is_public()
            && !function.x.attrs.is_unsafe
            && matches!(&function.x.kind, FunctionKind::Static)
            && function.x.require.len() > 0
        {
            return Err(error(
                &function.span,
                &format!(
                    "Safe API violation: 'requires' clause is nontrivial for function `{:}`. Unverified, safe client code may be able to call this function without satisfying the precondition.",
                    fun_as_friendly_rust_name(&function.x.name),
                ),
            ));
        }

        if let FunctionKind::TraitMethodImpl { trait_path, method, .. } = &function.x.kind {
            if function.x.mode == Mode::Exec && !function.x.attrs.is_unsafe {
                let trait_fn = function_map.get(method).unwrap();
                let t = trait_map.get(trait_path).unwrap();
                if t.x.visibility.is_public() && trait_fn.x.require.len() > 0 {
                    return Err(error(
                        &function.span,
                        &format!(
                            "Safe API violation: 'requires' clause is nontrivial for function `{:}`. Unverified, safe client code may be able to call this function without satisfying the precondition.",
                            fun_as_friendly_rust_name(&function.x.name),
                        ),
                    ));
                }
            }
        }

        if (function.x.mode == Mode::Exec || function.x.mode == Mode::Proof)
            && is_decl_in_safe_public_trait(&trait_map, function)
        {
            // We don't check ensures here, because we generate a proof obligation instead

            if function.x.mode == Mode::Exec
                && !matches!(function.x.unwind_spec_or_default(), UnwindSpec::MayUnwind)
            {
                return Err(error(
                    &function.span,
                    &format!(
                        "Safe API violation: 'unwind' clause is nontrivial for trait function `{:}`. Unverified, safe client code may be able to implement this trait without meeting these unwinding requirements.",
                        fun_as_friendly_rust_name(&function.x.name),
                    ),
                ));
            }
            if function.x.mode == Mode::Exec
                && mask_spec_restricts_implementation(
                    &function.x.mask_spec_or_default(&function.span),
                )
            {
                return Err(error(
                    &function.span,
                    &format!(
                        "Safe API violation: 'invariant' clause is nontrivial for trait function `{:}`. Unverified, safe client code may be able to implement this trait without obeying invariant-reentrancy requirements.",
                        fun_as_friendly_rust_name(&function.x.name),
                    ),
                ));
            }
        }
    }

    Ok(())
}

/// Error used when the SMT obligation fails
pub(crate) fn err_for_trait_ensures(span: &Span, fun: &Fun) -> VirErr {
    return error(
        span,
        &format!(
            "Safe API violation: 'ensures' clause is nontrivial for trait function `{:}`. Unverified, safe client code may be able to implement this trait without satisfying the postcondition.",
            fun_as_friendly_rust_name(fun),
        ),
    );
}

pub(crate) fn is_decl_in_safe_public_trait(
    trait_map: &HashMap<Path, Trait>,
    function: &Function,
) -> bool {
    if let FunctionKind::TraitMethodDecl { trait_path, has_default: _ } = &function.x.kind {
        let t = trait_map.get(trait_path).unwrap();
        t.x.visibility.is_public() && !t.x.is_unsafe
    } else {
        false
    }
}

fn mask_spec_restricts_implementation(mask_spec: &MaskSpec) -> bool {
    match mask_spec {
        MaskSpec::InvariantOpens(_span, _es) => true,
        MaskSpec::InvariantOpensExcept(_span, es) => es.len() > 0,
        MaskSpec::InvariantOpensSet(_e) => true,
    }
}

// To check that a trait is safe, we need to ensure that:
//  - For all possible (safe) exec code implementations,
//  - There exists an implementation for all spec and proof functions,
//  - Such that the implementation would be correct according to Verus.
// To check this condition, we will instantiate all spec functions with their default
// implementations, then check that the ensures clauses of proof/exec functions are
// satisfied.

/// Does check-api-safety need an extra proof obligation for this function?
///
/// For proof functions, the 'normal' generic check for proof fns with default bodies
/// is already stronger than what we need to to do.
/// Specifically: the normal check interprets all the trait's spec
/// functions as completely unspecified, whereas the check we need to do for
/// safe-api-check would allow us to assume the defaults. Thus the normal check already
/// subsumes what we need to for safe-api-check.
///
/// Therefore we always handle exec functions, and only handle proof functions if
/// they don't have a body.
pub fn function_has_obligation(ctx: &Ctx, function: &Function) -> bool {
    ctx.global.check_api_safety
        && is_decl_in_safe_public_trait(&ctx.trait_map, function)
        && (function.x.mode == Mode::Exec
            || (function.x.mode == Mode::Proof && function.x.body.is_none()))
}

/// Create a body where all outputs are havoced, this represents "any safe implementation".
pub fn body_that_havocs_all_outputs(function: &Function) -> Expr {
    // For each mut param, output:
    //  let tmp;
    //  *arg = tmp;

    let span = &function.span;
    let mut stmts = vec![];
    for param in function.x.params.iter() {
        if param.x.is_mut {
            stmts.push(Spanned::new(
                span.clone(),
                StmtX::Expr(SpannedTyped::new(
                    span,
                    &crate::ast_util::unit_typ(),
                    ExprX::Assign {
                        lhs: SpannedTyped::new(
                            span,
                            &param.x.typ,
                            ExprX::Loc(SpannedTyped::new(
                                span,
                                &param.x.typ,
                                ExprX::VarLoc(param.x.name.clone()),
                            )),
                        ),
                        rhs: SpannedTyped::new(span, &param.x.typ, ExprX::Nondeterministic),
                        op: None,
                    },
                )),
            ));
        }
    }

    let ret = &function.x.ret;
    let ret_expr = SpannedTyped::new(span, &ret.x.typ, ExprX::Nondeterministic);

    SpannedTyped::new(span, &ret.x.typ, ExprX::Block(Arc::new(stmts), Some(ret_expr)))
}

/// When emitting a proof obligation, we need axioms that the trait spec fns are given
/// their default bodies.
pub fn axioms_for_default_spec_fns(
    ctx: &Ctx,
    diagnostics: &impl air::messages::Diagnostics,
    cur_function: &Function,
) -> Result<Vec<Exp>, VirErr> {
    let traitt = if let FunctionKind::TraitMethodDecl { trait_path, has_default: _ } =
        &cur_function.x.kind
    {
        ctx.trait_map.get(trait_path).unwrap()
    } else {
        panic!("axioms_for_default_spec_fns called for non-trait fn");
    };

    if cur_function.x.decrease.len() > 0 {
        return Err(error(
            &cur_function.span,
            "Internal Verus Error (check-api-safety): decreases clause in trait function",
        ));
    }

    let mut exps = vec![];

    for method in traitt.x.methods.iter() {
        let function = &ctx.func_map[method];
        if function.x.mode == Mode::Spec {
            if let Some(body) = &function.x.body {
                // Only quantify over normal params, NOT type params
                // For type params we use the skolems introduced for this function

                let mut state = crate::ast_to_sst::State::new(diagnostics);

                state.push_scope();
                let var_binders = Arc::new(
                    function
                        .x
                        .params
                        .iter()
                        .map(|param| {
                            Arc::new(VarBinderX {
                                name: param.x.name.clone(),
                                a: param.x.typ.clone(),
                            })
                        })
                        .collect::<Vec<_>>(),
                );
                let var_binders = state.rename_binders_exp(&var_binders);

                let body_exp =
                    crate::ast_to_sst::expr_to_pure_exp_skip_checks(&ctx, &mut state, &body)?;

                let typ_args = Arc::new(
                    function
                        .x
                        .typ_params
                        .iter()
                        .map(|typ_param| Arc::new(TypX::TypParam(typ_param.clone())))
                        .collect::<Vec<_>>(),
                );
                let args = Arc::new(
                    function
                        .x
                        .params
                        .iter()
                        .map(|param| {
                            let unique_id = state.get_var_unique_id(&param.x.name);
                            SpannedTyped::new(&param.span, &param.x.typ, ExpX::Var(unique_id))
                        })
                        .collect::<Vec<_>>(),
                );

                state.pop_scope();
                state.finalize()?;

                let call_exp = SpannedTyped::new(
                    &function.span,
                    &function.x.ret.x.typ,
                    ExpX::Call(CallFun::Fun(function.x.name.clone(), None), typ_args, args),
                );

                let call_trig_exp = SpannedTyped::new(
                    &call_exp.span,
                    &call_exp.typ,
                    ExpX::Unary(
                        crate::ast::UnaryOp::Trigger(crate::ast::TriggerAnnotation::Trigger(None)),
                        call_exp.clone(),
                    ),
                );

                let eq_exp = crate::sst_util::sst_equal(&function.span, &call_trig_exp, &body_exp);

                let quantified_exp = if var_binders.len() > 0 {
                    let trigs = Arc::new(vec![]);
                    let quant = Quant { quant: air::ast::Quant::Forall };
                    let bnd = Spanned::new(
                        function.span.clone(),
                        BndX::Quant(quant, var_binders, trigs, None),
                    );
                    SpannedTyped::new(
                        &function.span,
                        &Arc::new(TypX::Bool),
                        ExpX::Bind(bnd, eq_exp),
                    )
                } else {
                    eq_exp
                };

                exps.push(quantified_exp);
            }
        }
    }

    Ok(exps)
}
