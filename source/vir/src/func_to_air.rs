use crate::ast::{
    Fun, Function, FunctionKind, Ident, Idents, Mode, Param, ParamX, Params, SpannedTyped, Typ,
    TypX, Typs, VirErr,
};
use crate::ast_util::QUANT_FORALL;
use crate::context::Ctx;
use crate::def::{
    new_internal_qid, prefix_ensures, prefix_fuel_id, prefix_fuel_nat, prefix_pre_var,
    prefix_recursive_fun, prefix_requires, suffix_global_id, suffix_local_stmt_id,
    suffix_typ_param_id, suffix_typ_param_ids, unique_local, CommandsWithContext, SnapPos, Spanned,
    FUEL_BOOL, FUEL_BOOL_DEFAULT, FUEL_LOCAL, FUEL_TYPE, SUCC, THIS_PRE_FAILED, ZERO,
};
use crate::sst::{BndX, Exp, ExpX, Par, ParPurpose, ParX, Pars, Stm, StmX};
use crate::sst_to_air::{
    exp_to_expr, fun_to_air_ident, typ_invariant, typ_to_air, typ_to_ids, ExprCtxt, ExprMode,
};
use crate::update_cell::UpdateCell;
use crate::util::vec_map;
use air::ast::{
    BinaryOp, Bind, BindX, Binder, BinderX, Command, CommandX, Commands, DeclX, Expr, ExprX, Quant,
    Span, Trigger, Triggers,
};
use air::ast_util::{
    bool_typ, ident_apply, ident_binder, ident_var, mk_and, mk_bind_expr, mk_eq, mk_implies,
    str_apply, str_ident, str_typ, str_var, string_apply,
};
use air::messages::{error_with_label, Diagnostics, MessageLabel};
use std::collections::HashMap;
use std::sync::Arc;

pub struct SstInline {
    pub(crate) typ_params: Idents,
    pub do_inline: bool,
}
use crate::sst_to_air::PostConditionKind;

pub struct SstInfo {
    pub(crate) inline: SstInline,
    pub(crate) params: Params,
    pub(crate) memoize: bool,
    pub(crate) body: Exp,
}

pub type SstMap = UpdateCell<HashMap<Fun, SstInfo>>;

// binder for forall (typ_params params)
pub(crate) fn func_bind_trig_dec(
    ctx: &Ctx,
    name: String,
    typ_params: &Idents,
    params: &Pars,
    trig_exprs: &Vec<Expr>,
    add_fuel: bool,
    decorated: bool,
    decorated_single: bool,
) -> Bind {
    let mut binders: Vec<air::ast::Binder<air::ast::Typ>> = Vec::new();
    for typ_param in typ_params.iter() {
        let ids = if decorated && !decorated_single {
            suffix_typ_param_ids(&typ_param)
        } else if decorated && crate::context::DECORATE {
            vec![crate::def::suffix_decorate_typ_param_id(&typ_param)]
        } else {
            vec![suffix_typ_param_id(&typ_param)]
        };
        binders.extend(ids.iter().map(|x| ident_binder(x, &str_typ(crate::def::TYPE))));
    }
    for param in params.iter() {
        let name = if matches!(param.x.purpose, ParPurpose::MutPre) {
            prefix_pre_var(&param.x.name)
        } else {
            param.x.name.clone()
        };
        binders.push(ident_binder(&suffix_local_stmt_id(&name), &typ_to_air(ctx, &param.x.typ)));
    }
    if add_fuel {
        binders.push(ident_binder(&str_ident(FUEL_LOCAL), &str_typ(FUEL_TYPE)));
    }
    let trigger: Trigger = Arc::new(trig_exprs.clone());
    let triggers: Triggers = Arc::new(vec![trigger]);
    let qid = new_internal_qid(name);
    Arc::new(BindX::Quant(Quant::Forall, Arc::new(binders), triggers, qid))
}

// binder for forall (typ_params params)
pub(crate) fn func_bind_trig(
    ctx: &Ctx,
    name: String,
    typ_params: &Idents,
    params: &Pars,
    trig_exprs: &Vec<Expr>,
    add_fuel: bool,
    decorated: bool,
) -> Bind {
    func_bind_trig_dec(ctx, name, typ_params, params, trig_exprs, add_fuel, decorated, false)
}

// binder for forall (typ_params params)
pub(crate) fn func_bind(
    ctx: &Ctx,
    name: String,
    typ_params: &Idents,
    params: &Pars,
    trig_expr: &Expr,
    add_fuel: bool,
    decorated: bool,
) -> Bind {
    func_bind_trig(ctx, name, typ_params, params, &vec![trig_expr.clone()], add_fuel, decorated)
}

// arguments for function call f(typ_args, params)
pub(crate) fn func_def_typs_args(typ_args: &Typs, params: &Pars) -> Vec<Expr> {
    let mut f_args: Vec<Expr> = typ_args.iter().map(typ_to_ids).flatten().collect();
    for param in params.iter() {
        let name = if matches!(param.x.purpose, ParPurpose::MutPre) {
            prefix_pre_var(&param.x.name)
        } else {
            param.x.name.clone()
        };
        f_args.push(ident_var(&suffix_local_stmt_id(&name)));
    }
    f_args
}

// arguments for function call f(typ_params, params)
pub(crate) fn func_def_args(typ_params: &Idents, params: &Pars) -> Vec<Expr> {
    let typ_args = Arc::new(vec_map(&typ_params, |x| Arc::new(TypX::TypParam(x.clone()))));
    func_def_typs_args(&typ_args, params)
}

// (forall (...) (=> cond (= (f ...) body)))
fn func_def_quant(
    ctx: &Ctx,
    name: &Ident,
    typ_params: &Idents,
    typ_args: &Typs,
    params: &Pars,
    pre: &Vec<Expr>,
    body: Expr,
) -> Result<Expr, VirErr> {
    let f_args = func_def_typs_args(typ_args, params);
    let f_app = string_apply(name, &Arc::new(f_args));
    let f_eq = Arc::new(ExprX::Binary(BinaryOp::Eq, f_app.clone(), body));
    let f_imply = mk_implies(&mk_and(pre), &f_eq);
    Ok(mk_bind_expr(
        &func_bind(ctx, name.to_string(), typ_params, params, &f_app, false, true),
        &f_imply,
    ))
}

fn func_body_to_air(
    ctx: &Ctx,
    diagnostics: &impl Diagnostics,
    fun_ssts: SstMap,
    decl_commands: &mut Vec<Command>,
    check_commands: &mut Vec<Command>,
    function: &Function,
    body: &crate::ast::Expr,
    not_verifying_owning_module: bool,
) -> Result<SstMap, VirErr> {
    let id_fuel = prefix_fuel_id(&fun_to_air_ident(&function.x.name));

    let pars = params_to_pars(&function.x.params, false);

    // ast --> sst
    let mut state = crate::ast_to_sst::State::new(diagnostics);
    state.declare_params(&pars);
    state.view_as_spec = true;
    state.fun_ssts = fun_ssts;
    let body_exp = crate::ast_to_sst::expr_to_pure_exp(&ctx, &mut state, &body)?;
    let body_exp = state.finalize_exp(ctx, &state.fun_ssts, &body_exp)?;
    let inline =
        SstInline { typ_params: function.x.typ_params.clone(), do_inline: function.x.attrs.inline };
    let info = SstInfo {
        inline,
        params: function.x.params.clone(),
        memoize: function.x.attrs.memoize,
        body: body_exp.clone(),
    };
    assert!(!state.fun_ssts.borrow().contains_key(&function.x.name));
    state.fun_ssts.borrow_mut().insert(function.x.name.clone(), info);

    let mut decrease_by_stms: Vec<Stm> = Vec::new();
    let decrease_by_reqs = if let Some(req) = &function.x.decrease_when {
        let exp = crate::ast_to_sst::expr_to_exp(ctx, diagnostics, &state.fun_ssts, &pars, req)?;
        let expr = exp_to_expr(ctx, &exp, &ExprCtxt::new_mode(ExprMode::Spec))?;
        decrease_by_stms.push(Spanned::new(req.span.clone(), StmX::Assume(exp)));
        vec![expr]
    } else {
        vec![]
    };
    if let Some(fun) = &function.x.decrease_by {
        state.view_as_spec = false;
        if let Some(decrease_by_fun) = ctx.func_map.get(fun) {
            let body_stm = crate::ast_to_sst::expr_to_one_stm_with_post(
                &ctx,
                &mut state,
                decrease_by_fun.x.body.as_ref().expect("decreases_by has body"),
            )?;
            let body_stm = state.finalize_stm(
                ctx,
                diagnostics,
                &state.fun_ssts,
                &body_stm,
                // note: these arguments are just for splitting, and (unless we support
                // special splitting for decrease_by lemmas) they shouldn't matter.
                // passing in an empty vec![] will cause splitting to just skip over this
                &Arc::new(vec![]),
                &Arc::new(vec![]),
                None,
            )?;

            decrease_by_stms.push(body_stm);
        } else {
            assert!(not_verifying_owning_module);
        }
    } else {
        let base_error = error_with_label(
            "could not prove termination".to_string(),
            &body_exp.span,
            "of this function body".to_string(),
        );

        // In this case, the user hasn't provided a proof body, so we just need to make
        // our own trivial proof body. A trivial proof body is just a single
        // Return statement.
        // check_termination_exp will set the "ensures clause" to be the
        // termination conditions.
        decrease_by_stms.push(Spanned::new(
            body_exp.span.clone(),
            StmX::Return { base_error, ret_exp: None, inside_body: false },
        ));
    }
    state.finalize();

    // Check termination
    let (is_recursive, termination_commands, body_exp) = crate::recursion::check_termination_exp(
        ctx,
        diagnostics,
        &state.fun_ssts,
        function,
        state.local_decls,
        &body_exp,
        decrease_by_stms,
        function.x.decrease_by.is_some(),
    )?;
    check_commands.extend(termination_commands.iter().cloned());

    // non-recursive:
    //   (axiom (fuel_bool_default fuel%f))
    if function.x.fuel > 0 {
        let axiom_expr = str_apply(&FUEL_BOOL_DEFAULT, &vec![ident_var(&id_fuel)]);
        let fuel_axiom = Arc::new(DeclX::Axiom(axiom_expr));
        decl_commands.push(Arc::new(CommandX::Global(fuel_axiom)));
    }

    // For trait method implementations, use trait method function name and add Self type argument
    let (name, typ_args) =
        if let FunctionKind::TraitMethodImpl { method, trait_typ_args, .. } = &function.x.kind {
            (method.clone(), trait_typ_args.clone())
        } else {
            let typ_args = vec_map(&function.x.typ_params, |x| Arc::new(TypX::TypParam(x.clone())));
            (function.x.name.clone(), Arc::new(typ_args))
        };

    // non-recursive:
    //   (axiom (=> (fuel_bool fuel%f) (forall (...) (= (f ...) body))))
    // recursive:
    //   (declare-const fuel_nat%f Fuel)
    //   (axiom (forall (... fuel) (= (rec%f ... fuel) (rec%f ... zero) )))
    //   (axiom (forall (... fuel) (= (rec%f ... (succ fuel)) body[rec%f ... fuel] )))
    //   (axiom (=> (fuel_bool fuel%f) (forall (...) (= (f ...) (rec%f ... (succ fuel_nat%f))))))
    let body_expr = exp_to_expr(&ctx, &body_exp, &ExprCtxt::new())?;
    let def_body = if !is_recursive {
        body_expr
    } else {
        // Compute shortest path from function back to itself
        // Example: f calls g, g calls f, so shortest cycle f --> g --> f has len 2
        // We use this as the minimum default fuel for f
        let fun_node = crate::recursion::Node::Fun(function.x.name.clone());
        let cycle_len = ctx.global.func_call_graph.shortest_cycle_back_to_self(&fun_node);
        assert!(cycle_len >= 1);

        let rec_f = suffix_global_id(&fun_to_air_ident(&prefix_recursive_fun(&name)));
        let fuel_nat_f = prefix_fuel_nat(&fun_to_air_ident(&name));
        let args = func_def_args(&function.x.typ_params, &pars);
        let mut args_zero = args.clone();
        let mut args_fuel = args.clone();
        let mut args_succ = args.clone();
        let mut args_def = args;
        args_zero.push(str_var(ZERO));
        args_fuel.push(str_var(FUEL_LOCAL));
        args_succ.push(str_apply(SUCC, &vec![str_var(FUEL_LOCAL)]));
        let mut succ_fuel_nat_f = ident_var(&fuel_nat_f);
        for _ in 0..cycle_len {
            succ_fuel_nat_f = str_apply(SUCC, &vec![succ_fuel_nat_f]);
        }
        args_def.push(succ_fuel_nat_f);
        let rec_f_zero = ident_apply(&rec_f, &args_zero);
        let rec_f_fuel = ident_apply(&rec_f, &args_fuel);
        let rec_f_succ = ident_apply(&rec_f, &args_succ);
        let rec_f_def = ident_apply(&rec_f, &args_def);
        let eq_zero = mk_eq(&rec_f_fuel, &rec_f_zero);
        let eq_body = mk_eq(&rec_f_succ, &body_expr);
        let name_zero = format!("{}_fuel_to_zero", &fun_to_air_ident(&name));
        let name_body = format!("{}_fuel_to_body", &fun_to_air_ident(&name));
        let bind_zero =
            func_bind(ctx, name_zero, &function.x.typ_params, &pars, &rec_f_fuel, true, true);
        let bind_body =
            func_bind(ctx, name_body, &function.x.typ_params, &pars, &rec_f_succ, true, true);
        let implies_body = mk_implies(&mk_and(&decrease_by_reqs), &eq_body);
        let forall_zero = mk_bind_expr(&bind_zero, &eq_zero);
        let forall_body = mk_bind_expr(&bind_body, &implies_body);
        let fuel_nat_decl = Arc::new(DeclX::Const(fuel_nat_f, str_typ(FUEL_TYPE)));
        let axiom_zero = Arc::new(DeclX::Axiom(forall_zero));
        let axiom_body = Arc::new(DeclX::Axiom(forall_body));
        decl_commands.push(Arc::new(CommandX::Global(fuel_nat_decl)));
        decl_commands.push(Arc::new(CommandX::Global(axiom_zero)));
        decl_commands.push(Arc::new(CommandX::Global(axiom_body)));
        rec_f_def
    };

    let e_forall = func_def_quant(
        ctx,
        &suffix_global_id(&fun_to_air_ident(&name)),
        &function.x.typ_params,
        &typ_args,
        &pars,
        &decrease_by_reqs,
        def_body,
    )?;
    let fuel_bool = str_apply(FUEL_BOOL, &vec![ident_var(&id_fuel)]);
    let def_axiom = Arc::new(DeclX::Axiom(mk_implies(&fuel_bool, &e_forall)));
    decl_commands.push(Arc::new(CommandX::Global(def_axiom)));
    Ok(state.fun_ssts)
}

pub fn req_ens_to_air(
    ctx: &Ctx,
    diagnostics: &impl Diagnostics,
    fun_ssts: &SstMap,
    commands: &mut Vec<Command>,
    params: &Pars,
    typing_invs: &Vec<Expr>,
    specs: &Vec<crate::ast::Expr>,
    typ_params: &Idents,
    typs: &air::ast::Typs,
    name: &Ident,
    msg: &Option<String>,
) -> Result<bool, VirErr> {
    if specs.len() + typing_invs.len() > 0 {
        let mut all_typs = (**typs).clone();
        for _ in typ_params.iter() {
            for x in crate::def::types() {
                all_typs.insert(0, str_typ(x));
            }
        }
        let decl = Arc::new(DeclX::Fun(name.clone(), Arc::new(all_typs), bool_typ()));
        commands.push(Arc::new(CommandX::Global(decl)));
        let mut exprs: Vec<Expr> = Vec::new();
        for e in typing_invs {
            exprs.push(e.clone());
        }
        for e in specs.iter() {
            let exp = crate::ast_to_sst::expr_to_exp(ctx, diagnostics, fun_ssts, params, e)?;
            let expr = exp_to_expr(ctx, &exp, &ExprCtxt::new_mode(ExprMode::Spec))?;
            let loc_expr = match msg {
                None => expr,
                Some(msg) => {
                    let l = MessageLabel { span: e.span.clone(), note: msg.clone() };
                    let ls = Arc::new(vec![l]);
                    Arc::new(ExprX::LabeledAxiom(ls, expr))
                }
            };
            exprs.push(loc_expr);
        }
        let body = mk_and(&exprs);
        let typ_args = Arc::new(vec_map(&typ_params, |x| Arc::new(TypX::TypParam(x.clone()))));
        let e_forall = func_def_quant(ctx, &name, &typ_params, &typ_args, &params, &vec![], body)?;
        let req_ens_axiom = Arc::new(DeclX::Axiom(e_forall));
        commands.push(Arc::new(CommandX::Global(req_ens_axiom)));
        Ok(true)
    } else {
        Ok(false)
    }
}

/// Returns vector of commands that declare the function symbol itself,
/// as well as any related functions symbols (e.g., recursive versions),
/// if the function is a spec function.
pub fn func_name_to_air(
    ctx: &Ctx,
    diagnostics: &impl Diagnostics,
    function: &Function,
) -> Result<Commands, VirErr> {
    let mut commands: Vec<Command> = Vec::new();
    if function.x.mode == Mode::Spec {
        if let FunctionKind::TraitMethodImpl { .. } = &function.x.kind {
            // Implementations of trait methods use the trait method declaration's function,
            // so there's no need to declare another function.
            return Ok(Arc::new(vec![]));
        }

        let mut all_typs = vec_map(&function.x.params, |param| typ_to_air(ctx, &param.x.typ));
        for _ in function.x.typ_params.iter() {
            for x in crate::def::types() {
                all_typs.insert(0, str_typ(x));
            }
        }

        // Declare the function symbol itself
        let typ = typ_to_air(ctx, &function.x.ret.x.typ);
        let name = suffix_global_id(&fun_to_air_ident(&function.x.name));
        let decl = Arc::new(DeclX::Fun(name, Arc::new(all_typs), typ.clone()));
        commands.push(Arc::new(CommandX::Global(decl)));

        // Check whether we need to declare the recursive version too
        if let Some(body) = &function.x.body {
            let body_exp = crate::ast_to_sst::expr_to_exp_as_spec(
                &ctx,
                diagnostics,
                &UpdateCell::new(HashMap::new()),
                &params_to_pars(&function.x.params, false),
                &body,
            )?;
            if crate::recursion::is_recursive_exp(ctx, &function.x.name, &body_exp) {
                let rec_f =
                    suffix_global_id(&fun_to_air_ident(&prefix_recursive_fun(&function.x.name)));
                let mut rec_typs =
                    vec_map(&*function.x.params, |param| typ_to_air(ctx, &param.x.typ));
                for _ in function.x.typ_params.iter() {
                    for x in crate::def::types() {
                        rec_typs.insert(0, str_typ(x));
                    }
                }
                rec_typs.push(str_typ(FUEL_TYPE));
                let rec_decl = Arc::new(DeclX::Fun(rec_f, Arc::new(rec_typs), typ));
                commands.push(Arc::new(CommandX::Global(rec_decl)));
            }
        }
    }
    Ok(Arc::new(commands))
}

pub(crate) fn param_to_par(param: &Param, allow_is_mut: bool) -> Par {
    param.map_x(|p| {
        let ParamX { name, typ, mode, is_mut, unwrapped_info: _ } = p;
        if *is_mut && !allow_is_mut {
            panic!("mut unexpected here");
        }
        ParX { name: name.clone(), typ: typ.clone(), mode: *mode, purpose: ParPurpose::Regular }
    })
}

pub(crate) fn params_to_pars(params: &Params, allow_is_mut: bool) -> Pars {
    Arc::new(vec_map(params, |p| param_to_par(p, allow_is_mut)))
}

fn params_to_pre_post_pars(params: &Params, pre: bool) -> Pars {
    Arc::new(
        params
            .iter()
            .flat_map(|param| {
                let mut res = Vec::new();
                if param.x.is_mut {
                    res.push(param.map_x(|p| ParX {
                        name: p.name.clone(),
                        typ: p.typ.clone(),
                        mode: p.mode,
                        purpose: ParPurpose::MutPre,
                    }));
                }
                if !(param.x.is_mut && pre) {
                    res.push(param.map_x(|p| ParX {
                        name: p.name.clone(),
                        typ: p.typ.clone(),
                        mode: p.mode,
                        purpose: if param.x.is_mut {
                            ParPurpose::MutPost
                        } else {
                            ParPurpose::Regular
                        },
                    }));
                }
                res
            })
            .collect::<Vec<_>>(),
    )
}

pub fn func_decl_to_air(
    ctx: &mut Ctx,
    diagnostics: &impl Diagnostics,
    fun_ssts: &SstMap,
    function: &Function,
) -> Result<Commands, VirErr> {
    let req_typs: Arc<Vec<_>> =
        Arc::new(function.x.params.iter().map(|param| typ_to_air(ctx, &param.x.typ)).collect());
    let mut decl_commands: Vec<Command> = Vec::new();
    if function.x.require.len() > 0 {
        let msg = match (function.x.mode, &function.x.attrs.custom_req_err) {
            // We don't highlight the failed precondition if the programmer supplied their own msg
            (_, Some(_)) => None,
            // Standard message
            (Mode::Spec, None) => Some("recommendation not met".to_string()),
            (_, None) => Some(THIS_PRE_FAILED.to_string()),
        };
        let req_params = params_to_pre_post_pars(&function.x.params, true);
        let _ = req_ens_to_air(
            ctx,
            diagnostics,
            fun_ssts,
            &mut decl_commands,
            &req_params,
            &vec![],
            &function.x.require,
            &function.x.typ_params,
            &req_typs,
            &prefix_requires(&fun_to_air_ident(&function.x.name)),
            &msg,
        )?;
    }
    Ok(Arc::new(decl_commands))
}

pub fn func_axioms_to_air(
    ctx: &mut Ctx,
    diagnostics: &impl Diagnostics,
    fun_ssts: SstMap,
    function: &Function,
    public_body: bool,
    not_verifying_owning_module: bool,
) -> Result<(Commands, Commands, SstMap), VirErr> {
    let mut ens_typs: Vec<_> = function
        .x
        .params
        .iter()
        .flat_map(|param| {
            let air_typ = typ_to_air(ctx, &param.x.typ);
            if !param.x.is_mut { vec![air_typ] } else { vec![air_typ.clone(), air_typ] }
        })
        .collect();
    let mut decl_commands: Vec<Command> = Vec::new();
    let mut check_commands: Vec<Command> = Vec::new();
    let mut new_fun_ssts = fun_ssts;
    match function.x.mode {
        Mode::Spec => {
            // Body
            if public_body {
                if let Some(body) = &function.x.body {
                    new_fun_ssts = func_body_to_air(
                        ctx,
                        diagnostics,
                        new_fun_ssts,
                        &mut decl_commands,
                        &mut check_commands,
                        function,
                        body,
                        not_verifying_owning_module,
                    )?;
                }
            }

            if let FunctionKind::TraitMethodImpl { .. } = &function.x.kind {
                // For a trait method implementation, we just need to supply a body axiom
                // for the existing trait method declaration function, so we can return here.
                return Ok((Arc::new(decl_commands), Arc::new(check_commands), new_fun_ssts));
            }

            let name = suffix_global_id(&fun_to_air_ident(&function.x.name));

            // Return typing invariant
            let mut f_args: Vec<Expr> = Vec::new();
            let mut f_pre: Vec<Expr> = Vec::new();
            for typ_param in function.x.typ_params.iter() {
                let ids = suffix_typ_param_ids(&typ_param);
                f_args.extend(ids.iter().map(|x| ident_var(x)));
            }
            for param in function.x.params.iter() {
                let arg = ident_var(&suffix_local_stmt_id(&param.x.name.clone()));
                f_args.push(arg.clone());
                if let Some(pre) = typ_invariant(ctx, &param.x.typ, &arg) {
                    f_pre.push(pre.clone());
                }
            }
            let f_app = ident_apply(&name, &Arc::new(f_args));
            if let Some(post) = typ_invariant(ctx, &function.x.ret.x.typ, &f_app) {
                // (axiom (forall (...) (=> pre post)))
                let name = format!("{}_pre_post", name);
                let e_forall = mk_bind_expr(
                    &func_bind(
                        ctx,
                        name,
                        &function.x.typ_params,
                        &params_to_pars(&function.x.params, false),
                        &f_app,
                        false,
                        true,
                    ),
                    &mk_implies(&mk_and(&f_pre), &post),
                );
                let inv_axiom = Arc::new(DeclX::Axiom(e_forall));
                decl_commands.push(Arc::new(CommandX::Global(inv_axiom)));
            }
        }
        Mode::Exec | Mode::Proof => {
            assert!(!function.x.attrs.is_decrease_by);

            if let FunctionKind::TraitMethodImpl { .. } = &function.x.kind {
                // For a trait method implementation, we inherit the trait requires/ensures,
                // so we can just return here.
                return Ok((Arc::new(decl_commands), Arc::new(check_commands), new_fun_ssts));
            }

            let params = params_to_pre_post_pars(&function.x.params, false);
            let mut ens_params = (*params).clone();
            let mut ens_typing_invs: Vec<Expr> = Vec::new();
            if function.x.has_return() {
                let ParamX { name, typ, .. } = &function.x.ret.x;
                ens_typs.push(typ_to_air(ctx, &typ));
                ens_params.push(param_to_par(&function.x.ret, false));
                if let Some(expr) =
                    typ_invariant(ctx, &typ, &ident_var(&suffix_local_stmt_id(&name)))
                {
                    ens_typing_invs.push(expr);
                }
            }
            // typing invariants for synthetic out-params for &mut params
            for param in params.iter().filter(|p| matches!(p.x.purpose, ParPurpose::MutPost)) {
                if let Some(expr) = typ_invariant(
                    ctx,
                    &param.x.typ,
                    &ident_var(&suffix_local_stmt_id(&param.x.name)),
                ) {
                    ens_typing_invs.push(expr);
                }
            }
            let has_ens_pred = req_ens_to_air(
                ctx,
                diagnostics,
                &new_fun_ssts,
                &mut decl_commands,
                &Arc::new(ens_params),
                &ens_typing_invs,
                &function.x.ensure,
                &function.x.typ_params,
                &Arc::new(ens_typs),
                &prefix_ensures(&fun_to_air_ident(&function.x.name)),
                &None,
            )?;
            if has_ens_pred {
                ctx.funcs_with_ensure_predicate.insert(function.x.name.clone());
            }
            if let Some((params, req_ens)) = &function.x.broadcast_forall {
                let span = &function.span;
                let params = params_to_pre_post_pars(params, false);
                let exp = crate::ast_to_sst::expr_to_bind_decls_exp(
                    ctx,
                    diagnostics,
                    &new_fun_ssts,
                    &params,
                    req_ens,
                )?;
                let mut vars: Vec<Ident> = Vec::new();
                let mut binders: Vec<Binder<Typ>> = Vec::new();
                if function.x.typ_bounds.len() != 0 {
                    todo!()
                }
                for name in function.x.typ_params.iter() {
                    vars.push(suffix_typ_param_id(&name));
                    let typ = Arc::new(TypX::TypeId);
                    let bind = BinderX { name: name.clone(), a: typ };
                    binders.push(Arc::new(bind));
                }
                for param in params.iter() {
                    vars.push(param.x.name.clone());
                    binders.push(crate::ast_util::par_to_binder(&param));
                }
                let triggers =
                    crate::triggers::build_triggers(ctx, span, &vars, &exp, true, false)?;
                let bndx = BndX::Quant(QUANT_FORALL, Arc::new(binders), triggers);
                let forallx = ExpX::Bind(Spanned::new(span.clone(), bndx), exp);
                let forall = SpannedTyped::new(&span, &Arc::new(TypX::Bool), forallx);
                let expr = exp_to_expr(ctx, &forall, &ExprCtxt::new_mode(ExprMode::Spec))?;
                let axiom = Arc::new(DeclX::Axiom(expr));
                decl_commands.push(Arc::new(CommandX::Global(axiom)));
            }
        }
    }
    Ok((Arc::new(decl_commands), Arc::new(check_commands), new_fun_ssts))
}

pub enum FuncDefPhase {
    CheckingSpecs,
    CheckingProofExec,
}

pub fn func_def_to_air(
    ctx: &Ctx,
    diagnostics: &impl Diagnostics,
    fun_ssts: SstMap,
    function: &Function,
    phase: FuncDefPhase,
    checking_recommends: bool,
) -> Result<(Arc<Vec<CommandsWithContext>>, Vec<(Span, SnapPos)>, SstMap), VirErr> {
    let erasure_mode = match (function.x.mode, function.x.is_const) {
        (Mode::Spec, true) => Mode::Exec,
        (mode, _) => mode,
    };
    match (phase, erasure_mode, checking_recommends, &function.x.body) {
        (_, _, _, None)
        | (FuncDefPhase::CheckingSpecs, Mode::Proof | Mode::Exec, _, Some(_))
        | (FuncDefPhase::CheckingSpecs, Mode::Spec, false, Some(_))
        | (FuncDefPhase::CheckingProofExec, Mode::Spec, _, Some(_)) => {
            Ok((Arc::new(vec![]), vec![], fun_ssts))
        }
        (FuncDefPhase::CheckingSpecs, Mode::Spec, true, Some(body))
        | (FuncDefPhase::CheckingProofExec, Mode::Proof | Mode::Exec, _, Some(body)) => {
            // Note: since is_const functions serve double duty as exec and spec,
            // we generate an exec check for them here to catch any arithmetic overflows.
            let (trait_typ_substs, req_ens_function) = if let FunctionKind::TraitMethodImpl {
                method,
                impl_path: _,
                trait_path,
                trait_typ_args,
            } = &function.x.kind
            {
                // Inherit requires/ensures from trait method declaration
                let tr = &ctx.trait_map[trait_path];
                let mut typ_params = vec![crate::def::trait_self_type_param()];
                for (x, _) in tr.x.typ_params.iter() {
                    typ_params.push(x.clone());
                }
                let mut trait_typ_substs: HashMap<Ident, Typ> = HashMap::new();
                assert!(typ_params.len() == trait_typ_args.len());
                for (x, t) in typ_params.iter().zip(trait_typ_args.iter()) {
                    let t = crate::poly::coerce_typ_to_poly(ctx, t);
                    trait_typ_substs.insert(x.clone(), t);
                }
                (trait_typ_substs, &ctx.func_map[method])
            } else {
                (HashMap::new(), function)
            };

            let mut state = crate::ast_to_sst::State::new(diagnostics);
            state.fun_ssts = fun_ssts;

            let mut ens_params = (*function.x.params).clone();
            let dest = if function.x.has_return() {
                let ParamX { name, typ, .. } = &function.x.ret.x;
                ens_params.push(function.x.ret.clone());
                state.declare_new_var(name, typ, false, false);
                Some(unique_local(name))
            } else {
                None
            };

            let ens_params = Arc::new(ens_params);
            let req_pars = params_to_pars(&function.x.params, true);
            let ens_pars = params_to_pars(&ens_params, true);

            for param in function.x.params.iter() {
                state.declare_new_var(&param.x.name, &param.x.typ, param.x.is_mut, false);
            }

            let mut req_stms: Vec<Stm> = Vec::new();
            let mut reqs: Vec<Exp> = Vec::new();
            for e in req_ens_function.x.require.iter() {
                if ctx.checking_recommends() {
                    let (stms, exp) =
                        crate::ast_to_sst::expr_to_pure_exp_check(ctx, &mut state, e)?;
                    req_stms.extend(stms);
                    req_stms.push(Spanned::new(exp.span.clone(), StmX::Assume(exp)));
                } else {
                    reqs.push(crate::ast_to_sst::expr_to_exp(
                        ctx,
                        diagnostics,
                        &state.fun_ssts,
                        &req_pars,
                        e,
                    )?);
                }
            }
            let mut ens_recommend_stms: Vec<Stm> = Vec::new();
            let mut enss: Vec<Exp> = Vec::new();
            for e in req_ens_function.x.ensure.iter() {
                if ctx.checking_recommends() {
                    ens_recommend_stms
                        .extend(crate::ast_to_sst::check_pure_expr(ctx, &mut state, e)?);
                } else {
                    enss.push(crate::ast_to_sst::expr_to_exp(
                        ctx,
                        diagnostics,
                        &state.fun_ssts,
                        &ens_pars,
                        e,
                    )?);
                }
            }
            let enss = Arc::new(enss);

            // AST --> SST
            let mut stm = crate::ast_to_sst::expr_to_one_stm_with_post(&ctx, &mut state, &body)?;
            if ctx.checking_recommends() && trait_typ_substs.len() == 0 {
                if let Some(fun) = &function.x.decrease_by {
                    let decrease_by_fun = &ctx.func_map[fun];
                    let (body_stms, _exp) = crate::ast_to_sst::expr_to_stm_or_error(
                        &ctx,
                        &mut state,
                        decrease_by_fun.x.body.as_ref().expect("decreases_by has body"),
                    )?;
                    req_stms.extend(body_stms);
                }
                req_stms.push(stm);
                stm = crate::ast_to_sst::stms_to_one_stm(&body.span, req_stms);
            }

            let stm = state.finalize_stm(
                &ctx,
                diagnostics,
                &state.fun_ssts,
                &stm,
                &req_ens_function.x.ensure,
                &ens_pars,
                dest.clone(),
            )?;
            let ens_recommend_stms: Result<Vec<_>, _> = ens_recommend_stms
                .iter()
                .map(|s| {
                    state.finalize_stm(
                        &ctx,
                        diagnostics,
                        &state.fun_ssts,
                        &s,
                        &req_ens_function.x.ensure,
                        &ens_pars,
                        dest.clone(),
                    )
                })
                .collect();
            let ens_recommend_stms = ens_recommend_stms?;

            // Check termination
            //
            let no_termination_check =
                function.x.mode == Mode::Exec && function.x.decrease.len() == 0;
            let (decls, stm) = if no_termination_check || ctx.checking_recommends() {
                (vec![], stm)
            } else {
                crate::recursion::check_termination_stm(
                    ctx,
                    diagnostics,
                    &state.fun_ssts,
                    function,
                    &stm,
                )?
            };

            // SST --> AIR
            for decl in decls {
                state.new_statement_var(&decl.ident.name);
                state.local_decls.push(decl.clone());
            }

            let (commands, snap_map) = crate::sst_to_air::body_stm_to_air(
                ctx,
                &function.span,
                &trait_typ_substs,
                &function.x.typ_params,
                &function.x.params,
                &state.local_decls,
                &function.x.attrs.hidden,
                &reqs,
                &enss,
                &ens_recommend_stms,
                &function.x.mask_spec,
                function.x.mode,
                &stm,
                function.x.attrs.integer_ring,
                function.x.attrs.bit_vector,
                function.x.attrs.nonlinear,
                function.x.attrs.spinoff_prover,
                dest,
                PostConditionKind::Ensures,
            )?;

            state.finalize();
            Ok((Arc::new(commands), snap_map, state.fun_ssts))
        }
    }
}
