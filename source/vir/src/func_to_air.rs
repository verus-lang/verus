use crate::ast::{
    Fun, Function, FunctionKind, Ident, Idents, ItemKind, MaskSpec, Mode, Param, ParamX, Params,
    SpannedTyped, Typ, TypX, Typs, VarBinder, VarBinderX, VarIdent, VirErr,
};
use crate::ast_util::{LowerUniqueVar, QUANT_FORALL};
use crate::ast_visitor;
use crate::context::Ctx;
use crate::def::{
    new_internal_qid, prefix_ensures, prefix_fuel_id, prefix_fuel_nat, prefix_open_inv,
    prefix_pre_var, prefix_recursive_fun, prefix_requires, static_name, suffix_global_id,
    suffix_typ_param_id, suffix_typ_param_ids, unique_local, CommandsWithContext, SnapPos, Spanned,
    FUEL_BOOL, FUEL_BOOL_DEFAULT, FUEL_PARAM, FUEL_TYPE, SUCC, THIS_PRE_FAILED, ZERO,
};
use crate::inv_masks::MaskSet;
use crate::messages::{error, Message, MessageLabel, Span};
use crate::sst::{BndX, Exp, ExpX, Par, ParPurpose, ParX, Pars, Stm, StmX};
use crate::sst::{FunctionSst, PostConditionKind, PostConditionSst};
use crate::sst_to_air::{
    exp_to_expr, fun_to_air_ident, typ_invariant, typ_to_air, typ_to_ids, ExprCtxt, ExprMode,
};
use crate::sst_util::{subst_exp, subst_stm};
use crate::update_cell::UpdateCell;
use crate::util::vec_map;
use air::ast::{
    BinaryOp, Bind, BindX, Command, CommandX, Commands, DeclX, Expr, ExprX, Quant, Trigger,
    Triggers,
};
use air::ast_util::{
    bool_typ, ident_apply, ident_binder, ident_var, int_typ, mk_and, mk_bind_expr, mk_eq,
    mk_implies, str_apply, str_ident, str_typ, str_var, string_apply,
};
use air::messages::ArcDynMessageLabel;
use std::collections::HashMap;
use std::sync::Arc;

pub struct SstInline {
    pub(crate) typ_params: Idents,
    pub do_inline: bool,
}

pub struct SstInfo {
    pub(crate) inline: SstInline,
    pub(crate) params: Params,
    pub(crate) memoize: bool,
    pub(crate) body: Exp,
}

pub type SstMap = UpdateCell<HashMap<Fun, SstInfo>>;

// binder for forall (typ_params params)
pub(crate) fn func_bind_trig(
    ctx: &Ctx,
    name: String,
    typ_params: &Idents,
    params: &Pars,
    trig_exprs: &Vec<Expr>,
    add_fuel: bool,
) -> Bind {
    let mut binders: Vec<air::ast::Binder<air::ast::Typ>> = Vec::new();
    for typ_param in typ_params.iter() {
        for (x, t) in crate::def::suffix_typ_param_ids_types(&typ_param) {
            binders.push(ident_binder(&x.lower(), &str_typ(t)));
        }
    }
    for param in params.iter() {
        let name = if matches!(param.x.purpose, ParPurpose::MutPre) {
            prefix_pre_var(&param.x.name.lower())
        } else {
            param.x.name.lower()
        };
        binders.push(ident_binder(&name, &typ_to_air(ctx, &param.x.typ)));
    }
    if add_fuel {
        binders.push(ident_binder(&str_ident(FUEL_PARAM), &str_typ(FUEL_TYPE)));
    }
    let trigger: Trigger = Arc::new(trig_exprs.clone());
    let triggers: Triggers = Arc::new(vec![trigger]);
    let qid = new_internal_qid(ctx, name);
    Arc::new(BindX::Quant(Quant::Forall, Arc::new(binders), triggers, qid))
}

// binder for forall (typ_params params)
pub(crate) fn func_bind(
    ctx: &Ctx,
    name: String,
    typ_params: &Idents,
    params: &Pars,
    trig_expr: &Expr,
    add_fuel: bool,
) -> Bind {
    func_bind_trig(ctx, name, typ_params, params, &vec![trig_expr.clone()], add_fuel)
}

// arguments for function call f(typ_args, params)
pub(crate) fn func_def_typs_args(typ_args: &Typs, params: &Pars) -> Vec<Expr> {
    let mut f_args: Vec<Expr> = typ_args.iter().map(typ_to_ids).flatten().collect();
    for param in params.iter() {
        let name = if matches!(param.x.purpose, ParPurpose::MutPre) {
            prefix_pre_var(&param.x.name.lower())
        } else {
            param.x.name.lower()
        };
        f_args.push(ident_var(&name));
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
    Ok(mk_bind_expr(&func_bind(ctx, name.to_string(), typ_params, params, &f_app, false), &f_imply))
}

pub(crate) fn module_reveal_axioms(
    _ctx: &Ctx,
    decl_commands: &mut Vec<Command>,
    module_reveals: &Option<crate::ast::ModuleReveals>,
) {
    if let Some(module_reveals) = module_reveals {
        let revealed_fuels = mk_and(
            &module_reveals
                .x
                .iter()
                .map(|member: &Fun| {
                    let fuel_id = prefix_fuel_id(&fun_to_air_ident(member));
                    str_apply(&FUEL_BOOL_DEFAULT, &vec![ident_var(&fuel_id)])
                })
                .collect::<Vec<Expr>>(),
        );

        let axiom = Arc::new(DeclX::Axiom(revealed_fuels));
        decl_commands.push(Arc::new(CommandX::Global(axiom)));
    }
}

pub(crate) fn broadcast_forall_group_axioms(
    ctx: &Ctx,
    decl_commands: &mut Vec<Command>,
    group: &crate::ast::RevealGroup,
    crate_name: &Ident,
) {
    let id_group = prefix_fuel_id(&fun_to_air_ident(&group.x.name));
    let fuel_group = str_apply(&FUEL_BOOL_DEFAULT, &vec![ident_var(&id_group)]);
    if let Some(group_crate) = &group.x.broadcast_use_by_default_when_this_crate_is_imported {
        let is_imported = crate_name != group_crate;
        if is_imported {
            // (axiom (fuel_bool_default fuel%group))
            let group_axiom = Arc::new(DeclX::Axiom(fuel_group.clone()));
            decl_commands.push(Arc::new(CommandX::Global(group_axiom)));
        }
    }
    let mut member_fuels: Vec<Expr> = Vec::new();
    for member in group.x.members.iter() {
        if ctx.reveal_group_set.contains(member) || ctx.func_map.contains_key(member) {
            let id_member = prefix_fuel_id(&fun_to_air_ident(member));
            member_fuels.push(str_apply(&FUEL_BOOL_DEFAULT, &vec![ident_var(&id_member)]));
        }
    }
    if member_fuels.len() > 0 {
        // (axiom (=> (fuel_bool_default fuel%group) (and ... (fuel_bool_default fuel%member) ...)))
        let imply = mk_implies(&fuel_group, &mk_and(&member_fuels));
        let axiom = Arc::new(DeclX::Axiom(imply));
        decl_commands.push(Arc::new(CommandX::Global(axiom)));
    }
}

fn func_body_to_air(
    ctx: &Ctx,
    diagnostics: &impl air::messages::Diagnostics,
    fun_ssts: SstMap,
    decl_commands: &mut Vec<Command>,
    check_commands: &mut Vec<CommandsWithContext>,
    function: &Function,
    body: &crate::ast::Expr,
    not_verifying_owning_bucket: bool,
) -> Result<SstMap, VirErr> {
    let id_fuel = prefix_fuel_id(&fun_to_air_ident(&function.x.name));

    let pars = params_to_pars(&function.x.params, false);

    // ast --> sst
    let mut state = crate::ast_to_sst::State::new(diagnostics);
    state.declare_params(&pars);
    state.view_as_spec = true;
    state.fun_ssts = fun_ssts;
    // Use expr_to_pure_exp_skip_checks here
    // because spec precondition checking is performed as a separate query
    let body_exp = crate::ast_to_sst::expr_to_pure_exp_skip_checks(&ctx, &mut state, &body)?;
    let body_exp = state.finalize_exp(ctx, diagnostics, &state.fun_ssts, &body_exp)?;
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
    state.finalize();

    // Rewrite recursive calls to use fuel
    let (is_recursive, body_exp, scc_rep) =
        crate::recursion::rewrite_recursive_fun_with_fueled_rec_call(
            ctx, function, &body_exp, None,
        )?;

    // Check termination and/or recommends
    let mut check_state = crate::ast_to_sst::State::new(diagnostics);
    // don't check recommends during decreases checking; these are separate passes:
    check_state.disable_recommends = 1;
    check_state.declare_params(&pars);
    check_state.view_as_spec = true;
    check_state.fun_ssts = state.fun_ssts;
    check_state.check_spec_decreases = Some((function.x.name.clone(), scc_rep));
    let check_body_stm =
        crate::ast_to_sst::expr_to_one_stm_with_post(&ctx, &mut check_state, &body)?;
    let check_body_stm =
        check_state.finalize_stm(ctx, diagnostics, &check_state.fun_ssts, &check_body_stm)?;

    let mut proof_body: Vec<crate::ast::Expr> = Vec::new();
    let mut def_reqs: Vec<Expr> = Vec::new();
    // Non-recursive function definitions are unconditional axioms that hold
    // for all type arguments and value arguments
    // (conceptually, they aren't axioms at all, but are simply abbreviations).
    // Recursive function definitions, on the other hand, only hold conditionally for
    // type arguments and value arguments for which termination can be proved.
    // Collect the conditions on type arguments and value arguments in def_reqs.
    if function.x.decrease.len() > 0 {
        // conditions on type arguments:
        def_reqs.extend(crate::traits::trait_bounds_to_air(ctx, &function.x.typ_bounds));
    }
    if let Some(req) = &function.x.decrease_when {
        // "when" means the function is only defined if the requirements hold

        // first, set up proof_body
        let mut reqs = crate::traits::trait_bounds_to_ast(ctx, &req.span, &function.x.typ_bounds);
        reqs.push(req.clone());
        for expr in reqs {
            let assumex = crate::ast::ExprX::AssertAssume { is_assume: true, expr: expr.clone() };
            proof_body.push(SpannedTyped::new(
                &req.span,
                &Arc::new(TypX::Tuple(Arc::new(vec![]))),
                assumex,
            ));
        }
        proof_body.push(req.clone()); // check spec preconditions

        // Skip checks because we check decrease_when below
        let exp = crate::ast_to_sst::expr_to_pure_exp_skip_checks(ctx, &mut check_state, req)?;
        let exp = check_state.finalize_exp(ctx, diagnostics, &check_state.fun_ssts, &exp)?;
        let expr = exp_to_expr(ctx, &exp, &ExprCtxt::new_mode(ExprMode::Spec))?;
        // conditions on value arguments:
        def_reqs.push(expr);
    }
    if let Some(fun) = &function.x.decrease_by {
        check_state.view_as_spec = false;
        if let Some(decrease_by_fun) = ctx.func_map.get(fun) {
            let decrease_by_fun_body =
                decrease_by_fun.x.body.as_ref().expect("decreases_by has body").clone();
            ast_visitor::expr_visitor_check(&decrease_by_fun_body, &mut |_scope_map, expr| {
                match &expr.x {
                    crate::ast::ExprX::Return(_) => Err(error(
                        &expr.span,
                        "explicit returns are not allowed in decreases_by function",
                    )),
                    _ => Ok(()),
                }
            })?;
            proof_body.push(decrease_by_fun_body);
        } else {
            assert!(not_verifying_owning_bucket);
        }
    }
    let mut proof_body_stms: Vec<Stm> = Vec::new();
    for expr in proof_body {
        let (mut stms, exp) = crate::ast_to_sst::expr_to_stm_opt(ctx, &mut check_state, &expr)?;
        assert!(!matches!(exp, crate::ast_to_sst::ReturnValue::Never));
        proof_body_stms.append(&mut stms);
    }
    let proof_body_stm = crate::ast_to_sst::stms_to_one_stm(&body.span, proof_body_stms);
    let proof_body_stm =
        check_state.finalize_stm(ctx, diagnostics, &check_state.fun_ssts, &proof_body_stm)?;
    check_state.finalize();

    let termination_commands = crate::recursion::check_termination_commands(
        ctx,
        diagnostics,
        &check_state.fun_ssts,
        function,
        check_state.local_decls,
        proof_body_stm,
        &check_body_stm,
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
        } else if let FunctionKind::TraitMethodDecl { .. } = &function.x.kind {
            let typ_args = vec_map(&function.x.typ_params, |x| Arc::new(TypX::TypParam(x.clone())));
            (crate::def::trait_default_name(&function.x.name), Arc::new(typ_args))
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
        let cycle_len = ctx.global.func_call_graph.shortest_cycle_back_to_self(&fun_node).len();
        assert!(cycle_len >= 1);

        let rec_f = suffix_global_id(&fun_to_air_ident(&prefix_recursive_fun(&name)));
        let fuel_nat_f = prefix_fuel_nat(&fun_to_air_ident(&name));
        let args = func_def_args(&function.x.typ_params, &pars);
        let mut args_zero = args.clone();
        let mut args_fuel = args.clone();
        let mut args_succ = args.clone();
        let mut args_def = args;
        args_zero.push(str_var(ZERO));
        args_fuel.push(str_var(FUEL_PARAM));
        args_succ.push(str_apply(SUCC, &vec![str_var(FUEL_PARAM)]));
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
        let bind_zero = func_bind(ctx, name_zero, &function.x.typ_params, &pars, &rec_f_fuel, true);
        let bind_body = func_bind(ctx, name_body, &function.x.typ_params, &pars, &rec_f_succ, true);
        let implies_body = mk_implies(&mk_and(&def_reqs), &eq_body);
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
        &def_reqs,
        def_body,
    )?;
    let fuel_bool = str_apply(FUEL_BOOL, &vec![ident_var(&id_fuel)]);
    let def_axiom = Arc::new(DeclX::Axiom(mk_implies(&fuel_bool, &e_forall)));
    decl_commands.push(Arc::new(CommandX::Global(def_axiom)));
    Ok(check_state.fun_ssts)
}

pub fn req_ens_to_air(
    ctx: &Ctx,
    diagnostics: &impl air::messages::Diagnostics,
    fun_ssts: &SstMap,
    commands: &mut Vec<Command>,
    params: &Pars,
    typing_invs: &Vec<Expr>,
    specs: &Vec<crate::ast::Expr>,
    typ_params: &Idents,
    typs: &air::ast::Typs,
    name: &Ident,
    msg: &Option<String>,
    is_singular: bool,
    typ: air::ast::Typ,
    inherit_from: Option<(Ident, Typs)>,
    filter: Option<Ident>,
) -> Result<bool, VirErr> {
    if specs.len() + typing_invs.len() > 0 {
        let mut all_typs = (**typs).clone();
        for _ in typ_params.iter() {
            for x in crate::def::types().iter().rev() {
                all_typs.insert(0, str_typ(x));
            }
        }
        let decl = Arc::new(DeclX::Fun(name.clone(), Arc::new(all_typs), typ));
        commands.push(Arc::new(CommandX::Global(decl)));

        let typ_args = Arc::new(vec_map(&typ_params, |x| Arc::new(TypX::TypParam(x.clone()))));

        let mut exprs: Vec<Expr> = Vec::new();
        match inherit_from {
            None => {}
            Some((name, trait_typ_args)) => {
                let args = func_def_typs_args(&trait_typ_args, params);
                let f_app = string_apply(&name, &Arc::new(args));
                exprs.push(f_app);
            }
        }
        for e in typing_invs {
            exprs.push(e.clone());
        }
        for e in specs.iter() {
            // Use expr_to_exp_skip_checks because we check req/ens in body
            let exp =
                crate::ast_to_sst::expr_to_exp_skip_checks(ctx, diagnostics, fun_ssts, params, e)?;
            let expr_ctxt = if is_singular {
                ExprCtxt::new_mode_singular(ExprMode::Spec, true)
            } else {
                ExprCtxt::new_mode(ExprMode::Spec)
            };
            let expr = exp_to_expr(ctx, &exp, &expr_ctxt)?;
            let loc_expr = match msg {
                None => expr,
                Some(msg) => {
                    let l = MessageLabel { span: e.span.clone(), note: msg.clone() };
                    let ls: Vec<ArcDynMessageLabel> = vec![Arc::new(l)];
                    Arc::new(ExprX::LabeledAxiom(ls, filter.clone(), expr))
                }
            };
            exprs.push(loc_expr);
        }
        let body = mk_and(&exprs);
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
    _diagnostics: &impl air::messages::Diagnostics,
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
            for x in crate::def::types().iter().rev() {
                all_typs.insert(0, str_typ(x));
            }
        }
        let all_typs = Arc::new(all_typs);

        // Declare the function symbol itself
        let typ = typ_to_air(ctx, &function.x.ret.x.typ);
        let mut names = vec![function.x.name.clone()];
        if let FunctionKind::TraitMethodDecl { .. } = &function.x.kind {
            names.push(crate::def::trait_default_name(&function.x.name));
        }
        for name in names {
            let name = suffix_global_id(&fun_to_air_ident(&name));
            let decl = Arc::new(DeclX::Fun(name, all_typs.clone(), typ.clone()));
            commands.push(Arc::new(CommandX::Global(decl)));
        }

        // Check whether we need to declare the recursive version too
        if function.x.body.is_some() {
            if crate::recursion::fun_is_recursive(ctx, &function) {
                let rec_f =
                    suffix_global_id(&fun_to_air_ident(&prefix_recursive_fun(&function.x.name)));
                let mut rec_typs =
                    vec_map(&*function.x.params, |param| typ_to_air(ctx, &param.x.typ));
                for _ in function.x.typ_params.iter() {
                    for x in crate::def::types().iter().rev() {
                        rec_typs.insert(0, str_typ(x));
                    }
                }
                rec_typs.push(str_typ(FUEL_TYPE));
                let rec_decl = Arc::new(DeclX::Fun(rec_f, Arc::new(rec_typs), typ));
                commands.push(Arc::new(CommandX::Global(rec_decl)));
            }
        }
    }

    if matches!(function.x.item_kind, ItemKind::Static) {
        // Declare static%foo, which represents the result of 'foo()' when executed
        // at the beginning of a program (here, `foo` is a 'static' item which we
        // represent as 0-argument function)
        commands.push(Arc::new(CommandX::Global(Arc::new(DeclX::Const(
            static_name(&function.x.name),
            typ_to_air(ctx, &function.x.ret.x.typ),
        )))));
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
    diagnostics: &impl air::messages::Diagnostics,
    fun_ssts: &SstMap,
    function: &Function,
) -> Result<Commands, VirErr> {
    let (is_trait_method_impl, inherit_fn_ens) = match &function.x.kind {
        FunctionKind::TraitMethodImpl { method, trait_typ_args, .. } => {
            if ctx.funcs_with_ensure_predicate[method] {
                let ens = prefix_ensures(&fun_to_air_ident(&method));
                let mut typ_args = (**trait_typ_args).clone();
                let num_trait_and_method_typ_params = ctx.func_map[method].x.typ_params.len();
                let num_method_typ_params = num_trait_and_method_typ_params - trait_typ_args.len();
                let num_our_total_typ_params = function.x.typ_params.len();
                let skip_to_our_method_typ_params =
                    num_our_total_typ_params - num_method_typ_params;
                // Add the arguments for the method's type parameters, skipping over our impl params
                for method_typ_param in
                    function.x.typ_params.iter().skip(skip_to_our_method_typ_params)
                {
                    typ_args.push(Arc::new(TypX::TypParam(method_typ_param.clone())));
                }
                (true, Some((ens, Arc::new(typ_args))))
            } else {
                (true, None)
            }
        }
        _ => (false, None),
    };

    let req_typs: Arc<Vec<_>> =
        Arc::new(function.x.params.iter().map(|param| typ_to_air(ctx, &param.x.typ)).collect());
    let mut decl_commands: Vec<Command> = Vec::new();

    // Requires
    if function.x.require.len() > 0 {
        assert!(!is_trait_method_impl);

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
            function.x.attrs.integer_ring,
            bool_typ(),
            None,
            Some(fun_to_air_ident(&function.x.name)),
        )?;
    }

    // Inv mask
    match &function.x.mask_spec {
        MaskSpec::NoSpec => {}
        MaskSpec::InvariantOpens(es) | MaskSpec::InvariantOpensExcept(es) => {
            for (i, e) in es.iter().enumerate() {
                let req_params = params_to_pre_post_pars(&function.x.params, true);
                let _ = req_ens_to_air(
                    ctx,
                    diagnostics,
                    fun_ssts,
                    &mut decl_commands,
                    &req_params,
                    &vec![],
                    &vec![e.clone()],
                    &function.x.typ_params,
                    &req_typs,
                    &prefix_open_inv(&fun_to_air_ident(&function.x.name), i),
                    &None,
                    function.x.attrs.integer_ring,
                    int_typ(),
                    None,
                    None,
                );
            }
        }
    }

    // Ensures
    let mut ens_typs: Vec<_> = function
        .x
        .params
        .iter()
        .flat_map(|param| {
            let air_typ = typ_to_air(ctx, &param.x.typ);
            if !param.x.is_mut { vec![air_typ] } else { vec![air_typ.clone(), air_typ] }
        })
        .collect();
    let post_params = params_to_pre_post_pars(&function.x.params, false);
    let mut ens_params = (*post_params).clone();
    let mut ens_typing_invs: Vec<Expr> = Vec::new();
    if matches!(function.x.mode, Mode::Exec | Mode::Proof) {
        if function.x.has_return_name() {
            let ParamX { name, typ, .. } = &function.x.ret.x;
            ens_typs.push(typ_to_air(ctx, &typ));
            ens_params.push(param_to_par(&function.x.ret, false));
            if let Some(expr) = typ_invariant(ctx, &typ, &ident_var(&name.lower())) {
                ens_typing_invs.push(expr);
            }
        }
        // typing invariants for synthetic out-params for &mut params
        for param in post_params.iter().filter(|p| matches!(p.x.purpose, ParPurpose::MutPost)) {
            if let Some(expr) = typ_invariant(ctx, &param.x.typ, &ident_var(&param.x.name.lower()))
            {
                ens_typing_invs.push(expr);
            }
        }
    } else {
        assert!(function.x.ensure.len() == 0); // no ensures allowed on spec functions yet
    }

    if is_trait_method_impl {
        // For a trait method impl, we can skip the type invariants because we'll
        // be inheriting them from the trait function.
        ens_typing_invs = vec![];
    }

    let has_ens_pred = req_ens_to_air(
        ctx,
        diagnostics,
        fun_ssts,
        &mut decl_commands,
        &Arc::new(ens_params),
        &ens_typing_invs,
        &function.x.ensure,
        &function.x.typ_params,
        &Arc::new(ens_typs),
        &prefix_ensures(&fun_to_air_ident(&function.x.name)),
        &None,
        function.x.attrs.integer_ring,
        bool_typ(),
        inherit_fn_ens,
        None,
    )?;
    ctx.funcs_with_ensure_predicate.insert(function.x.name.clone(), has_ens_pred);

    if crate::ast_simplify::need_fndef_axiom(&ctx.fndef_type_set, function) {
        let fndef_axioms = function
            .x
            .fndef_axioms
            .as_ref()
            .expect("expected FnDef axioms to have been generated in ast_simplify");
        for fndef_axiom in fndef_axioms.iter() {
            let mut state = crate::ast_to_sst::State::new(diagnostics);
            let exp =
                crate::ast_to_sst::expr_to_pure_exp_skip_checks(ctx, &mut state, fndef_axiom)?;
            let exp = state.finalize_exp(ctx, diagnostics, &fun_ssts, &exp)?;
            state.finalize();

            // Add forall-binders for each type param
            // The fndef_axiom shoudld already be a 'forall' statement
            // so we can add them to the existing forall node

            let mut binders: Vec<VarBinder<Typ>> = Vec::new();
            for name in function.x.typ_params.iter() {
                let typ = Arc::new(TypX::TypeId);
                let bind = VarBinderX { name: crate::ast_util::typ_unique_var(name), a: typ };
                binders.push(Arc::new(bind));
            }

            let exp = match &exp.x {
                ExpX::Bind(bnd, e) => match &bnd.x {
                    BndX::Quant(quant, qbinders, trigs) => {
                        let mut qbinders = (&**qbinders).clone();
                        qbinders.append(&mut binders);
                        let bndx = BndX::Quant(*quant, Arc::new(qbinders), trigs.clone());
                        let bnd = Spanned::new(bnd.span.clone(), bndx);
                        let expx = ExpX::Bind(bnd, e.clone());
                        SpannedTyped::new(&exp.span, &exp.typ, expx)
                    }
                    _ => {
                        panic!("fndef_axiom should be forall");
                    }
                },
                _ => {
                    panic!("fndef_axiom should be forall");
                }
            };

            let expr = exp_to_expr(ctx, &exp, &ExprCtxt::new_mode(ExprMode::Spec))?;
            let axiom = Arc::new(DeclX::Axiom(expr));
            decl_commands.push(Arc::new(CommandX::Global(axiom)));
        }
    }

    Ok(Arc::new(decl_commands))
}

/// Returns axioms for function definition
/// For spec functions this is like `forall input . f(input) == body`
/// For proof/exec function this contains the req/ens functions.
/// For broadcast_forall this contains the broadcasted axiom.
///
/// The second 'Commands' contains additional things that need proving at this point
/// For a spec function, it may also output the proof obligations related to decreases-ness
/// (This may include the proof content of a decreases_by function.)
/// (Note: this means that you shouldn't call func_axioms_to_air with a decreases_by function
/// on its own.)

pub fn func_axioms_to_air(
    ctx: &mut Ctx,
    diagnostics: &impl air::messages::Diagnostics,
    fun_ssts: SstMap,
    function: &Function,
    public_body: bool,
    not_verifying_owning_bucket: bool,
) -> Result<(Commands, Vec<CommandsWithContext>, SstMap), VirErr> {
    let mut decl_commands: Vec<Command> = Vec::new();
    let mut check_commands: Vec<CommandsWithContext> = Vec::new();
    let mut new_fun_ssts = fun_ssts;
    let is_singular = function.x.attrs.integer_ring;
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
                        not_verifying_owning_bucket,
                    )?;
                }
                if let FunctionKind::TraitMethodImpl {
                    trait_typ_args,
                    inherit_body_from: Some(f_trait),
                    ..
                } = &function.x.kind
                {
                    // Emit axiom that says our method equals the default method we inherit from
                    let mut args: Vec<Expr> =
                        trait_typ_args.iter().map(typ_to_ids).flatten().collect();
                    for p in function.x.params.iter() {
                        args.push(ident_var(&p.x.name.lower()));
                    }
                    let default_name = crate::def::trait_default_name(f_trait);
                    let default_name = &suffix_global_id(&fun_to_air_ident(&default_name));
                    let body = ident_apply(&default_name, &args);
                    let pars = params_to_pars(&function.x.params, false);
                    let e_forall = func_def_quant(
                        ctx,
                        &suffix_global_id(&fun_to_air_ident(&f_trait)),
                        &function.x.typ_params,
                        &trait_typ_args,
                        &pars,
                        &vec![],
                        body,
                    )?;
                    let def_axiom = Arc::new(DeclX::Axiom(e_forall));
                    decl_commands.push(Arc::new(CommandX::Global(def_axiom)));
                }
            }

            if let FunctionKind::TraitMethodImpl { .. } = &function.x.kind {
                // For a trait method implementation, we just need to supply a body axiom
                // for the existing trait method declaration function, so we can return here.
                return Ok((Arc::new(decl_commands), check_commands, new_fun_ssts));
            }

            let name = suffix_global_id(&fun_to_air_ident(&function.x.name));

            // Return typing invariant
            let mut f_args: Vec<Expr> = Vec::new();
            let mut f_pre: Vec<Expr> = Vec::new();
            for typ_param in function.x.typ_params.iter() {
                let ids = suffix_typ_param_ids(&typ_param);
                f_args.extend(ids.iter().map(|x| ident_var(&x.lower())));
            }
            for param in function.x.params.iter() {
                let arg = ident_var(&param.x.name.lower());
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
                return Ok((Arc::new(decl_commands), check_commands, new_fun_ssts));
            }
            if let Some((params, req_ens)) = &function.x.broadcast_forall {
                let span = &function.span;
                let params = params_to_pre_post_pars(params, false);
                // Use expr_to_bind_decls_exp_skip_checks, skipping checks on req_ens,
                // because the requires/ensures are checked when the function itself is checked
                let exp = crate::ast_to_sst::expr_to_bind_decls_exp_skip_checks(
                    ctx,
                    diagnostics,
                    &new_fun_ssts,
                    &params,
                    req_ens,
                )?;
                use crate::triggers::{typ_boxing, TriggerBoxing};
                let mut vars: Vec<(VarIdent, TriggerBoxing)> = Vec::new();
                let mut binders: Vec<VarBinder<Typ>> = Vec::new();
                for name in function.x.typ_params.iter() {
                    vars.push((suffix_typ_param_id(&name), TriggerBoxing::TypeId));
                    let typ = Arc::new(TypX::TypeId);
                    let bind = VarBinderX { name: crate::ast_util::typ_unique_var(name), a: typ };
                    binders.push(Arc::new(bind));
                }
                for param in params.iter() {
                    vars.push((param.x.name.clone(), typ_boxing(ctx, &param.x.typ)));
                    binders.push(crate::ast_util::par_to_binder(&param));
                }
                let triggers = crate::triggers::build_triggers(ctx, span, &vars, &exp, false)?;
                let bndx = BndX::Quant(QUANT_FORALL, Arc::new(binders), triggers);
                let forallx = ExpX::Bind(Spanned::new(span.clone(), bndx), exp);
                let forall: Arc<SpannedTyped<ExpX>> =
                    SpannedTyped::new(&span, &Arc::new(TypX::Bool), forallx);
                let expr_ctxt = if is_singular {
                    ExprCtxt::new_mode_singular(ExprMode::Spec, true)
                } else {
                    ExprCtxt::new_mode(ExprMode::Spec)
                };
                let expr = exp_to_expr(ctx, &forall, &expr_ctxt)?;
                let fuel_imply = if !function.x.attrs.external_body {
                    let id_fuel = prefix_fuel_id(&fun_to_air_ident(&function.x.name));
                    let fuel_bool = str_apply(FUEL_BOOL, &vec![ident_var(&id_fuel)]);
                    mk_implies(&fuel_bool, &expr)
                } else {
                    // a broadcast_forall, external_body function

                    // TODO: eventually, all broadcast_forall should be controlled by fuel
                    // TODO: remove external_body from FunctionAttrsX; it was only needed here
                    expr
                };
                let axiom = Arc::new(DeclX::Axiom(fuel_imply));
                decl_commands.push(Arc::new(CommandX::Global(axiom)));
            }
        }
    }
    Ok((Arc::new(decl_commands), check_commands, new_fun_ssts))
}

pub fn func_def_to_sst(
    ctx: &Ctx,
    diagnostics: &impl air::messages::Diagnostics,
    fun_ssts: SstMap,
    function: &Function,
) -> Result<(SstMap, FunctionSst), VirErr> {
    let body = match &function.x.body {
        Some(body) => body,
        _ => {
            panic!("func_def_to_air should only be called for function with a body");
        }
    };

    // Note: since is_const functions serve double duty as exec and spec,
    // we generate an exec check for them here to catch any arithmetic overflows.
    let (trait_typ_substs, req_ens_function, inherit) =
        if let FunctionKind::TraitMethodImpl { method, trait_path, trait_typ_args, .. } =
            &function.x.kind
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
            (trait_typ_substs, &ctx.func_map[method], true)
        } else {
            (HashMap::new(), function, false)
        };

    let mut state = crate::ast_to_sst::State::new(diagnostics);
    state.fun_ssts = fun_ssts;

    let mut ens_params = (*function.x.params).clone();
    let dest = if function.x.has_return_name() {
        let ParamX { name, typ, .. } = &function.x.ret.x;
        ens_params.push(function.x.ret.clone());
        state.declare_var_stm(name, typ, false, false);
        Some(unique_local(name))
    } else {
        None
    };

    let ens_params = Arc::new(ens_params);
    let req_pars = params_to_pars(&function.x.params, true);
    let ens_pars = params_to_pars(&ens_params, true);

    for param in function.x.params.iter() {
        state.declare_var_stm(&param.x.name, &param.x.typ, param.x.is_mut, false);
    }

    let mut req_ens_e_rename: HashMap<_, _> = req_ens_function
        .x
        .params
        .iter()
        .zip(function.x.params.iter())
        .map(|(p1, p2)| (p1.x.name.clone(), p2.x.name.clone()))
        .collect();
    req_ens_e_rename.insert(req_ens_function.x.ret.x.name.clone(), function.x.ret.x.name.clone());

    let mut req_stms: Vec<Stm> = Vec::new();
    let mut reqs: Vec<Exp> = Vec::new();
    reqs.extend(crate::traits::trait_bounds_to_sst(ctx, &function.span, &function.x.typ_bounds));
    for e in req_ens_function.x.require.iter() {
        let e_with_req_ens_params = map_expr_rename_vars(e, &req_ens_e_rename)?;
        if ctx.checking_spec_preconditions() {
            // TODO: apply trait_typs_substs here?
            let (stms, exp) =
                crate::ast_to_sst::expr_to_pure_exp_check(ctx, &mut state, &e_with_req_ens_params)?;
            req_stms.extend(stms);
            req_stms.push(Spanned::new(exp.span.clone(), StmX::Assume(exp)));
        } else {
            // skip checks because we call expr_to_pure_exp_check above
            let exp = crate::ast_to_sst::expr_to_exp_skip_checks(
                ctx,
                diagnostics,
                &state.fun_ssts,
                &req_pars,
                &e_with_req_ens_params,
            )?;
            let exp = subst_exp(&trait_typ_substs, &HashMap::new(), &exp);
            reqs.push(exp);
        }
    }

    let inv_spec_exprs = match &req_ens_function.x.mask_spec {
        MaskSpec::NoSpec => Arc::new(vec![]),
        MaskSpec::InvariantOpens(exprs) | MaskSpec::InvariantOpensExcept(exprs) => exprs.clone(),
    };
    let mut inv_spec_air_exprs = vec![];
    for e in inv_spec_exprs.iter() {
        let e_with_req_ens_params = map_expr_rename_vars(e, &req_ens_e_rename)?;
        let exp = if ctx.checking_spec_preconditions() {
            let (stms, exp) =
                crate::ast_to_sst::expr_to_pure_exp_check(ctx, &mut state, &e_with_req_ens_params)?;
            req_stms.extend(stms);
            exp
        } else {
            crate::ast_to_sst::expr_to_exp_skip_checks(
                ctx,
                diagnostics,
                &state.fun_ssts,
                &req_pars,
                &e_with_req_ens_params,
            )?
        };

        let is_singular = function.x.attrs.integer_ring;
        let expr_ctxt = ExprCtxt::new_mode_singular(ExprMode::Body, is_singular);
        let exp = state.finalize_exp(ctx, diagnostics, &state.fun_ssts, &exp)?;
        let air_expr = exp_to_expr(ctx, &exp, &expr_ctxt)?;
        inv_spec_air_exprs
            .push(crate::inv_masks::MaskSingleton { expr: air_expr, span: e.span.clone() });
    }
    let mask_set = match &req_ens_function.x.mask_spec {
        MaskSpec::NoSpec => crate::sst_to_air::default_mask_set_for_mode(req_ens_function.x.mode),
        MaskSpec::InvariantOpens(_exprs) => MaskSet::from_list(inv_spec_air_exprs),
        MaskSpec::InvariantOpensExcept(_exprs) => MaskSet::from_list_complement(inv_spec_air_exprs),
    };

    for e in function.x.decrease.iter() {
        if ctx.checking_spec_preconditions() {
            let stms = crate::ast_to_sst::check_pure_expr(ctx, &mut state, &e)?;
            req_stms.extend(stms);
        }
    }
    let mut ens_spec_precondition_stms: Vec<Stm> = Vec::new();
    let mut enss: Vec<Exp> = Vec::new();
    if inherit {
        for e in req_ens_function.x.ensure.iter() {
            let e_with_req_ens_params = map_expr_rename_vars(e, &req_ens_e_rename)?;
            if ctx.checking_spec_preconditions() {
                let stms =
                    crate::ast_to_sst::check_pure_expr(ctx, &mut state, &e_with_req_ens_params)?;
                let stms: Vec<_> = stms
                    .iter()
                    .map(|stm| subst_stm(&trait_typ_substs, &HashMap::new(), &stm))
                    .collect();
                ens_spec_precondition_stms.extend(stms);
            } else {
                // skip checks because we call expr_to_pure_exp_check above
                let exp = crate::ast_to_sst::expr_to_exp_skip_checks(
                    ctx,
                    diagnostics,
                    &state.fun_ssts,
                    &ens_pars,
                    &e_with_req_ens_params,
                )?;
                let exp = subst_exp(&trait_typ_substs, &HashMap::new(), &exp);
                enss.push(exp);
            }
        }
    }
    for e in function.x.ensure.iter() {
        if ctx.checking_spec_preconditions() {
            ens_spec_precondition_stms
                .extend(crate::ast_to_sst::check_pure_expr(ctx, &mut state, &e)?);
        } else {
            // skip checks because we call expr_to_pure_exp_check above
            enss.push(crate::ast_to_sst::expr_to_exp_skip_checks(
                ctx,
                diagnostics,
                &state.fun_ssts,
                &ens_pars,
                &e,
            )?);
        }
    }

    // AST --> SST
    let mut stm = crate::ast_to_sst::expr_to_one_stm_with_post(&ctx, &mut state, &body)?;
    if ctx.checking_spec_preconditions() && trait_typ_substs.len() == 0 {
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

    let stm = state.finalize_stm(&ctx, diagnostics, &state.fun_ssts, &stm)?;
    let ens_spec_precondition_stms: Result<Vec<_>, _> = ens_spec_precondition_stms
        .iter()
        .map(|s| state.finalize_stm(&ctx, diagnostics, &state.fun_ssts, &s))
        .collect();
    let ens_spec_precondition_stms = ens_spec_precondition_stms?;

    // Check termination
    //
    let no_termination_check = function.x.mode == Mode::Exec && function.x.decrease.len() == 0;
    let (decls, stm) = if no_termination_check || ctx.checking_spec_preconditions() {
        (vec![], stm)
    } else {
        crate::recursion::check_termination_stm(ctx, diagnostics, &state.fun_ssts, function, &stm)?
    };

    // SST --> AIR
    for decl in decls {
        state.local_decls.push(decl.clone());
    }

    state.finalize();
    let crate::ast_to_sst::State { local_decls, statics, fun_ssts, .. } = state;

    Ok((
        fun_ssts,
        FunctionSst {
            reqs: Arc::new(reqs),
            post_condition: PostConditionSst {
                dest,
                ens_exps: enss,
                ens_spec_precondition_stms,
                kind: PostConditionKind::Ensures,
            },
            mask_set,
            body: stm,
            local_decls: local_decls,
            statics: statics.into_iter().collect(),
        },
    ))
}

pub fn func_sst_to_air(
    ctx: &Ctx,
    function: &Function,
    function_sst: &FunctionSst,
) -> Result<(Arc<Vec<CommandsWithContext>>, Vec<(Span, SnapPos)>), VirErr> {
    let (commands, snap_map) = crate::sst_to_air::body_stm_to_air(
        ctx,
        &function.span,
        &function.x.typ_params,
        &function.x.params,
        function_sst,
        &function.x.attrs.hidden,
        function.x.attrs.integer_ring,
        function.x.attrs.bit_vector,
        function.x.attrs.nonlinear,
    )?;

    Ok((Arc::new(commands), snap_map))
}

fn map_expr_rename_vars(
    e: &Arc<SpannedTyped<crate::ast::ExprX>>,
    req_ens_e_rename: &HashMap<VarIdent, VarIdent>,
) -> Result<Arc<SpannedTyped<crate::ast::ExprX>>, Message> {
    ast_visitor::map_expr_visitor(e, &|expr| {
        use crate::ast::ExprX;
        Ok(match &expr.x {
            ExprX::Var(i) => expr.new_x(ExprX::Var(req_ens_e_rename.get(i).unwrap_or(i).clone())),
            ExprX::VarLoc(i) => {
                expr.new_x(ExprX::VarLoc(req_ens_e_rename.get(i).unwrap_or(i).clone()))
            }
            ExprX::VarAt(i, at) => {
                expr.new_x(ExprX::VarAt(req_ens_e_rename.get(i).unwrap_or(i).clone(), *at))
            }
            _ => expr.clone(),
        })
    })
}
