use crate::ast::{
    Fun, FunctionKind, Ident, Idents, ItemKind, Mode, SpannedTyped, Typ, TypX, Typs, VarBinder,
    VarBinderX, VirErr,
};
use crate::ast_util::{LowerUniqueVar, QUANT_FORALL};
use crate::context::Ctx;
use crate::def::{
    new_internal_qid, prefix_ensures, prefix_fuel_id, prefix_fuel_nat, prefix_no_unwind_when,
    prefix_open_inv, prefix_pre_var, prefix_recursive_fun, prefix_requires, static_name,
    suffix_global_id, suffix_typ_param_ids, CommandsWithContext, SnapPos, Spanned, FUEL_BOOL,
    FUEL_BOOL_DEFAULT, FUEL_PARAM, FUEL_TYPE, SUCC, THIS_PRE_FAILED, ZERO,
};
use crate::messages::{MessageLabel, Span};
use crate::sst::FuncCheckSst;
use crate::sst::{BndX, ExpX, Exps, FunctionSst, ParPurpose, ParX, Pars};
use crate::sst_to_air::{
    exp_to_expr, fun_to_air_ident, typ_invariant, typ_to_air, typ_to_ids, ExprCtxt, ExprMode,
};
use crate::util::vec_map;
use air::ast::{
    Axiom, BinaryOp, Bind, BindX, Command, CommandX, Commands, DeclX, Expr, ExprX, Quant, Trigger,
    Triggers,
};
use air::ast_util::{
    bool_typ, ident_apply, ident_binder, ident_var, int_typ, mk_and, mk_bind_expr, mk_eq,
    mk_implies, mk_unnamed_axiom, str_apply, str_ident, str_typ, str_var, string_apply,
};
use air::messages::ArcDynMessageLabel;
use std::sync::Arc;

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

pub(crate) fn hide_projections_air(
    typ_params: &Idents,
    holes: Vec<(Ident, Typ)>,
) -> (Idents, Vec<Expr>) {
    let mut typ_params: Vec<Ident> = (**typ_params).clone();
    let mut eqs: Vec<Expr> = Vec::new();
    for (x, t) in holes {
        let xids = crate::def::suffix_typ_param_ids_types(&x);
        let tids = typ_to_ids(&t);
        assert!(xids.len() == tids.len());
        for ((xa, _ta), tid) in xids.into_iter().zip(tids.into_iter()) {
            eqs.push(mk_eq(&ident_var(&xa.lower()), &tid));
        }
        typ_params.push(x);
    }
    (Arc::new(typ_params), eqs)
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

        let axiom = mk_unnamed_axiom(revealed_fuels);
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
            let group_axiom = mk_unnamed_axiom(fuel_group.clone());
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
        let axiom = Arc::new(DeclX::Axiom(Axiom {
            named: if cfg!(feature = "axiom-usage-info") {
                Some(fun_to_air_ident(&group.x.name))
            } else {
                None
            },
            expr: imply,
        }));

        decl_commands.push(Arc::new(CommandX::Global(axiom)));
    }
}

fn func_body_to_air(
    ctx: &Ctx,
    decl_commands: &mut Vec<Command>,
    check_commands: &mut Vec<CommandsWithContext>,
    function: &FunctionSst,
    func_body_sst: &crate::sst::FuncSpecBodySst,
) -> Result<(), VirErr> {
    let crate::sst::FuncSpecBodySst { decrease_when, termination_check, body_exp } = func_body_sst;
    let pars = &function.x.pars;

    let id_fuel = prefix_fuel_id(&fun_to_air_ident(&function.x.name));
    let mut def_reqs: Vec<Expr> = Vec::new();
    // Non-recursive function definitions are unconditional axioms that hold
    // for all type arguments and value arguments
    // (conceptually, they aren't axioms at all, but are simply abbreviations).
    // Recursive function definitions, on the other hand, only hold conditionally for
    // type arguments and value arguments for which termination can be proved.
    // Collect the conditions on type arguments and value arguments in def_reqs.
    let function_kind_needs_trait_bounds = match &function.x.kind {
        FunctionKind::Static => false,
        FunctionKind::TraitMethodDecl { .. } => {
            // default method: trait bounds are applied to impls that inherit this,
            // rather than applying trait bounds here
            false
        }
        FunctionKind::TraitMethodImpl { .. } => true,
        FunctionKind::ForeignTraitMethodImpl { .. } => true,
    };
    if function.x.has.has_decrease || function_kind_needs_trait_bounds {
        // conditions on type arguments:
        // (*always* needed in trait dispatch to make sure different implementations of the same
        // trait don't conflict and contradict each other)
        def_reqs.extend(crate::traits::trait_bounds_to_air(ctx, &function.x.typ_bounds));
    }
    if function.x.has.has_decrease {
        for param in pars.iter() {
            let arg = ident_var(&param.x.name.lower());
            if let Some(pre) = typ_invariant(ctx, &param.x.typ, &arg) {
                def_reqs.push(pre.clone());
            }
        }
    }

    if let Some(exp) = decrease_when {
        let expr = exp_to_expr(ctx, &exp, &ExprCtxt::new_mode(ExprMode::Spec))?;
        // conditions on value arguments:
        def_reqs.push(expr);
    }

    if let Some(termination_check) = termination_check {
        let (termination_commands, _snap_map) = crate::sst_to_air::body_stm_to_air(
            ctx,
            &function.span,
            &function.x.typ_params,
            &function.x.typ_bounds,
            pars,
            &termination_check,
            &vec![],
            false,
            false,
            false,
        )?;
        check_commands.extend(termination_commands.iter().cloned());
    }

    // non-recursive:
    //   (axiom (fuel_bool_default fuel%f))
    if function.x.fuel > 0 {
        let axiom_expr = str_apply(&FUEL_BOOL_DEFAULT, &vec![ident_var(&id_fuel)]);
        let fuel_axiom = mk_unnamed_axiom(axiom_expr);
        decl_commands.push(Arc::new(CommandX::Global(fuel_axiom)));
    }

    // For trait method implementations, use trait method function name and add Self type argument
    let mut impl_typ_params = function.x.typ_params.clone();
    let mut impl_def_reqs: Vec<Expr> = Vec::new();
    let (name, rec_name, typ_args) =
        if let FunctionKind::TraitMethodImpl { method, trait_typ_args, .. } = &function.x.kind {
            let (trait_typ_args, holes) = crate::traits::hide_projections(trait_typ_args);
            let (typ_params, eqs) = hide_projections_air(&function.x.typ_params, holes);
            impl_typ_params = typ_params;
            impl_def_reqs.extend(eqs);
            (method.clone(), function.x.name.clone(), trait_typ_args.clone())
        } else if let FunctionKind::TraitMethodDecl { .. } = &function.x.kind {
            let typ_args = vec_map(&function.x.typ_params, |x| Arc::new(TypX::TypParam(x.clone())));
            let name = crate::def::trait_default_name(&function.x.name);
            (name.clone(), name, Arc::new(typ_args))
        } else {
            let typ_args = vec_map(&function.x.typ_params, |x| Arc::new(TypX::TypParam(x.clone())));
            (function.x.name.clone(), function.x.name.clone(), Arc::new(typ_args))
        };

    // non-recursive:
    //   (axiom (=> (fuel_bool fuel%f) (forall (...) (= (f ...) body))))
    // recursive:
    //   (declare-const fuel_nat%f Fuel)
    //   (axiom (forall (... fuel) (= (rec%f ... fuel) (rec%f ... zero) )))
    //   (axiom (forall (... fuel) (= (rec%f ... (succ fuel)) body[rec%f ... fuel] )))
    //   (axiom (=> (fuel_bool fuel%f) (forall (...) (= (f ...) (rec%f ... (succ fuel_nat%f))))))
    let body_expr = exp_to_expr(&ctx, &body_exp, &ExprCtxt::new())?;
    let def_body = if !function.x.has.is_recursive {
        body_expr
    } else {
        // Compute shortest path from function back to itself
        // Example: f calls g, g calls f, so shortest cycle f --> g --> f has len 2
        // We use this as the minimum default fuel for f
        let fun_node = crate::recursion::Node::Fun(function.x.name.clone());
        let cycle_len = ctx.global.func_call_graph.shortest_cycle_back_to_self(&fun_node).len();
        assert!(cycle_len >= 1);

        let rec_f = suffix_global_id(&fun_to_air_ident(&prefix_recursive_fun(&rec_name)));
        let fuel_nat_f = prefix_fuel_nat(&fun_to_air_ident(&rec_name));
        let args = func_def_args(&function.x.typ_params, pars);
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
        let bind_zero = func_bind(ctx, name_zero, &function.x.typ_params, pars, &rec_f_fuel, true);
        let bind_body = func_bind(ctx, name_body, &function.x.typ_params, pars, &rec_f_succ, true);
        let implies_body = mk_implies(&mk_and(&def_reqs), &eq_body);
        let forall_zero = mk_bind_expr(&bind_zero, &eq_zero);
        let forall_body = mk_bind_expr(&bind_body, &implies_body);
        let fuel_nat_decl = Arc::new(DeclX::Const(fuel_nat_f, str_typ(FUEL_TYPE)));
        let axiom_zero = mk_unnamed_axiom(forall_zero);
        let axiom_body = mk_unnamed_axiom(forall_body);
        decl_commands.push(Arc::new(CommandX::Global(fuel_nat_decl)));
        decl_commands.push(Arc::new(CommandX::Global(axiom_zero)));
        decl_commands.push(Arc::new(CommandX::Global(axiom_body)));
        rec_f_def
    };

    def_reqs.extend(impl_def_reqs);
    let e_forall = func_def_quant(
        ctx,
        &suffix_global_id(&fun_to_air_ident(&name)),
        &impl_typ_params,
        &typ_args,
        pars,
        &def_reqs,
        def_body,
    )?;
    let fuel_bool = str_apply(FUEL_BOOL, &vec![ident_var(&id_fuel)]);
    let def_axiom = mk_unnamed_axiom(mk_implies(&fuel_bool, &e_forall));
    decl_commands.push(Arc::new(CommandX::Global(def_axiom)));
    Ok(())
}

fn req_ens_to_air(
    ctx: &Ctx,
    commands: &mut Vec<Command>,
    params: &Pars,
    typing_invs: &Vec<Expr>,
    specs: &Exps,
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
        for exp in specs.iter() {
            let expr_ctxt = if is_singular {
                ExprCtxt::new_mode_singular(ExprMode::Spec, true)
            } else {
                ExprCtxt::new_mode(ExprMode::Spec)
            };
            let expr = exp_to_expr(ctx, exp, &expr_ctxt)?;
            let loc_expr = match msg {
                None => expr,
                Some(msg) => {
                    let l = MessageLabel { span: exp.span.clone(), note: msg.clone() };
                    let ls: Vec<ArcDynMessageLabel> = vec![Arc::new(l)];
                    Arc::new(ExprX::LabeledAxiom(ls, filter.clone(), expr))
                }
            };
            exprs.push(loc_expr);
        }
        let body = mk_and(&exprs);
        let e_forall = func_def_quant(ctx, &name, &typ_params, &typ_args, &params, &vec![], body)?;
        let req_ens_axiom = mk_unnamed_axiom(e_forall);
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
    function: &FunctionSst,
) -> Result<Commands, VirErr> {
    let mut commands: Vec<Command> = Vec::new();
    let declare_rec = |commands: &mut Vec<Command>| {
        // Check whether we need to declare the recursive version too
        if function.x.has.has_body {
            if function.x.has.is_recursive {
                let rec_f =
                    suffix_global_id(&fun_to_air_ident(&prefix_recursive_fun(&function.x.name)));
                let mut rec_typs =
                    vec_map(&*function.x.pars, |param| typ_to_air(ctx, &param.x.typ));
                for _ in function.x.typ_params.iter() {
                    for x in crate::def::types().iter().rev() {
                        rec_typs.insert(0, str_typ(x));
                    }
                }
                rec_typs.push(str_typ(FUEL_TYPE));
                let typ = typ_to_air(ctx, &function.x.ret.x.typ);
                let rec_decl = Arc::new(DeclX::Fun(rec_f, Arc::new(rec_typs), typ));
                commands.push(Arc::new(CommandX::Global(rec_decl)));
            }
        }
    };

    if function.x.mode == Mode::Spec {
        if let FunctionKind::TraitMethodImpl { .. } = &function.x.kind {
            // Implementations of trait methods use the trait method declaration's function,
            // so there's no need to declare another function.
            declare_rec(&mut commands);
            return Ok(Arc::new(commands));
        }

        let mut all_typs = vec_map(&function.x.pars, |param| typ_to_air(ctx, &param.x.typ));
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

        declare_rec(&mut commands);
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

pub fn func_decl_to_air(ctx: &mut Ctx, function: &FunctionSst) -> Result<Commands, VirErr> {
    let func_decl_sst = &function.x.decl;
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
        Arc::new(function.x.pars.iter().map(|param| typ_to_air(ctx, &param.x.typ)).collect());
    let mut decl_commands: Vec<Command> = Vec::new();

    // Requires
    if function.x.has.has_requires && !function.x.attrs.broadcast_forall_only {
        assert!(!is_trait_method_impl);

        let msg = match (function.x.mode, &function.x.attrs.custom_req_err) {
            // We don't highlight the failed precondition if the programmer supplied their own msg
            (_, Some(_)) => None,
            // Standard message
            (Mode::Spec, None) => Some("recommendation not met".to_string()),
            (_, None) => Some(THIS_PRE_FAILED.to_string()),
        };
        let _ = req_ens_to_air(
            ctx,
            &mut decl_commands,
            &func_decl_sst.req_inv_pars,
            &vec![],
            &func_decl_sst.reqs,
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
    if function.x.has.has_mask_spec {
        for (i, e) in func_decl_sst.inv_masks.iter().enumerate() {
            let _ = req_ens_to_air(
                ctx,
                &mut decl_commands,
                &func_decl_sst.req_inv_pars,
                &vec![],
                &e,
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

    // Unwind spec
    if let Some(e) = &func_decl_sst.unwind_condition {
        let _ = req_ens_to_air(
            ctx,
            &mut decl_commands,
            &func_decl_sst.req_inv_pars,
            &vec![],
            &Arc::new(vec![e.clone()]),
            &function.x.typ_params,
            &req_typs,
            &prefix_no_unwind_when(&fun_to_air_ident(&function.x.name)),
            &None,
            function.x.attrs.integer_ring,
            bool_typ(),
            None,
            None,
        );
    }

    // Ensures
    let mut ens_typs: Vec<_> = function
        .x
        .pars
        .iter()
        .flat_map(|param| {
            let air_typ = typ_to_air(ctx, &param.x.typ);
            if !param.x.is_mut { vec![air_typ] } else { vec![air_typ.clone(), air_typ] }
        })
        .collect();
    let mut ens_typing_invs: Vec<Expr> = Vec::new();
    if matches!(function.x.mode, Mode::Exec | Mode::Proof) {
        if function.x.has.has_return_name {
            let ParX { name, typ, .. } = &function.x.ret.x;
            ens_typs.push(typ_to_air(ctx, &typ));
            if let Some(expr) = typ_invariant(ctx, &typ, &ident_var(&name.lower())) {
                ens_typing_invs.push(expr);
            }
        }
        // typing invariants for synthetic out-params for &mut params
        for param in
            func_decl_sst.post_pars.iter().filter(|p| matches!(p.x.purpose, ParPurpose::MutPost))
        {
            if let Some(expr) = typ_invariant(ctx, &param.x.typ, &ident_var(&param.x.name.lower()))
            {
                ens_typing_invs.push(expr);
            }
        }
    } else {
        assert!(!function.x.has.has_ensures); // no ensures allowed on spec functions yet
    }

    if is_trait_method_impl {
        // For a trait method impl, we can skip the type invariants because we'll
        // be inheriting them from the trait function.
        ens_typing_invs = vec![];
    }

    let has_ens_pred = if function.x.attrs.broadcast_forall_only {
        false
    } else {
        req_ens_to_air(
            ctx,
            &mut decl_commands,
            &func_decl_sst.ens_pars,
            &ens_typing_invs,
            &func_decl_sst.enss,
            &function.x.typ_params,
            &Arc::new(ens_typs),
            &prefix_ensures(&fun_to_air_ident(&function.x.name)),
            &None,
            function.x.attrs.integer_ring,
            bool_typ(),
            inherit_fn_ens,
            None,
        )?
    };
    ctx.funcs_with_ensure_predicate.insert(function.x.name.clone(), has_ens_pred);

    for exp in func_decl_sst.fndef_axioms.iter() {
        let expr = exp_to_expr(ctx, exp, &ExprCtxt::new_mode(ExprMode::Spec))?;
        let axiom = mk_unnamed_axiom(expr);
        decl_commands.push(Arc::new(CommandX::Global(axiom)));
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
    function: &FunctionSst,
    public_body: bool,
) -> Result<(Commands, Vec<CommandsWithContext>), VirErr> {
    let func_axioms_sst = &function.x.axioms;
    let mut decl_commands: Vec<Command> = Vec::new();
    let mut check_commands: Vec<CommandsWithContext> = Vec::new();
    let is_singular = function.x.attrs.integer_ring;
    match function.x.mode {
        Mode::Spec => {
            // Body
            if public_body {
                if let Some(func_body_sst) = &func_axioms_sst.spec_axioms {
                    func_body_to_air(
                        ctx,
                        &mut decl_commands,
                        &mut check_commands,
                        function,
                        func_body_sst,
                    )?;
                }
                if let FunctionKind::TraitMethodImpl {
                    trait_typ_args,
                    inherit_body_from: Some(f_trait),
                    ..
                } = &function.x.kind
                {
                    // Emit axiom that says our method equals the default method we inherit from
                    // (if trait bounds are satisfied)
                    let (trait_typ_args, holes) = crate::traits::hide_projections(trait_typ_args);
                    let (typ_params, eqs) = hide_projections_air(&function.x.typ_params, holes);
                    let mut args: Vec<Expr> =
                        trait_typ_args.iter().map(typ_to_ids).flatten().collect();
                    for p in function.x.pars.iter() {
                        args.push(ident_var(&p.x.name.lower()));
                    }
                    let default_name = crate::def::trait_default_name(f_trait);
                    let default_name = &suffix_global_id(&fun_to_air_ident(&default_name));
                    let body = ident_apply(&default_name, &args);
                    let mut pre = crate::traits::trait_bounds_to_air(ctx, &function.x.typ_bounds);
                    pre.extend(eqs);
                    let e_forall = func_def_quant(
                        ctx,
                        &suffix_global_id(&fun_to_air_ident(&f_trait)),
                        &typ_params,
                        &trait_typ_args,
                        &function.x.pars,
                        &pre,
                        body,
                    )?;
                    let def_axiom = mk_unnamed_axiom(e_forall);
                    decl_commands.push(Arc::new(CommandX::Global(def_axiom)));
                }
            }

            if let FunctionKind::TraitMethodImpl { .. } = &function.x.kind {
                // For a trait method implementation, we just need to supply a body axiom
                // for the existing trait method declaration function, so we can return here.
                return Ok((Arc::new(decl_commands), check_commands));
            }

            let name = suffix_global_id(&fun_to_air_ident(&function.x.name));

            // Return typing invariant
            let mut f_args: Vec<Expr> = Vec::new();
            let mut f_pre: Vec<Expr> = Vec::new();
            for typ_param in function.x.typ_params.iter() {
                let ids = suffix_typ_param_ids(&typ_param);
                f_args.extend(ids.iter().map(|x| ident_var(&x.lower())));
            }
            for param in function.x.pars.iter() {
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
                    &func_bind(ctx, name, &function.x.typ_params, &function.x.pars, &f_app, false),
                    &mk_implies(&mk_and(&f_pre), &post),
                );
                let inv_axiom = mk_unnamed_axiom(e_forall);
                decl_commands.push(Arc::new(CommandX::Global(inv_axiom)));
            }
        }
        Mode::Exec | Mode::Proof => {
            assert!(!function.x.attrs.is_decrease_by);

            if let FunctionKind::TraitMethodImpl { .. } = &function.x.kind {
                // For a trait method implementation, we inherit the trait requires/ensures,
                // so we can just return here.
                return Ok((Arc::new(decl_commands), check_commands));
            }
            if let Some((params, exp, triggers)) = &func_axioms_sst.proof_exec_axioms {
                let span = &function.span;
                let mut binders: Vec<VarBinder<Typ>> = Vec::new();
                for name in function.x.typ_params.iter() {
                    let typ = Arc::new(TypX::TypeId);
                    let bind = VarBinderX { name: crate::ast_util::typ_unique_var(name), a: typ };
                    binders.push(Arc::new(bind));
                }
                for param in params.iter() {
                    binders.push(crate::ast_util::par_to_binder(&param));
                }
                let bndx = BndX::Quant(QUANT_FORALL, Arc::new(binders), triggers.clone());
                let forallx = ExpX::Bind(Spanned::new(span.clone(), bndx), exp.clone());
                let forall: Arc<SpannedTyped<ExpX>> =
                    SpannedTyped::new(&span, &Arc::new(TypX::Bool), forallx);
                let expr_ctxt = if is_singular {
                    ExprCtxt::new_mode_singular(ExprMode::Spec, true)
                } else {
                    ExprCtxt::new_mode(ExprMode::Spec)
                };
                let expr = exp_to_expr(ctx, &forall, &expr_ctxt)?;
                let fuel_imply = if function.x.attrs.size_of_broadcast_proof {
                    // special broadcast lemma for size_of global
                    expr
                } else {
                    let id_fuel = prefix_fuel_id(&fun_to_air_ident(&function.x.name));
                    let fuel_bool = str_apply(FUEL_BOOL, &vec![ident_var(&id_fuel)]);
                    mk_implies(&fuel_bool, &expr)
                };
                // let axiom = mk_unnamed_axiom(fuel_imply);
                let axiom = Arc::new(DeclX::Axiom(Axiom {
                    named: if cfg!(feature = "axiom-usage-info") {
                        Some(fun_to_air_ident(&function.x.name))
                    } else {
                        None
                    },
                    expr: fuel_imply,
                }));
                decl_commands.push(Arc::new(CommandX::Global(axiom)));
            }
        }
    }
    Ok((Arc::new(decl_commands), check_commands))
}

pub fn func_sst_to_air(
    ctx: &Ctx,
    function: &FunctionSst,
    func_check_sst: &FuncCheckSst,
) -> Result<(Arc<Vec<CommandsWithContext>>, Vec<(Span, SnapPos)>), VirErr> {
    let (commands, snap_map) = crate::sst_to_air::body_stm_to_air(
        ctx,
        &function.span,
        &function.x.typ_params,
        &function.x.typ_bounds,
        &function.x.pars,
        func_check_sst,
        &function.x.attrs.hidden,
        function.x.attrs.integer_ring,
        function.x.attrs.bit_vector,
        function.x.attrs.nonlinear,
    )?;

    Ok((Arc::new(commands), snap_map))
}
