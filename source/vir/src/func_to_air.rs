use crate::ast::{
    Function, FunctionKind, GenericBoundX, Ident, Idents, Mode, Param, ParamX, Params,
    SpannedTyped, Typ, TypX, Typs, VirErr,
};
use crate::context::Ctx;
use crate::def::{
    prefix_ensures, prefix_fuel_id, prefix_fuel_nat, prefix_pre_var, prefix_recursive_fun,
    prefix_requires, suffix_global_id, suffix_local_stmt_id, suffix_typ_param_id, SnapPos, Spanned,
    FUEL_BOOL, FUEL_BOOL_DEFAULT, FUEL_LOCAL, FUEL_TYPE, SUCC, ZERO,
};
use crate::sst::{BndX, Exp, ExpX, Par, ParPurpose, ParX, Pars, Stm, StmX};
use crate::sst_to_air::{
    exp_to_expr, fun_to_air_ident, typ_invariant, typ_to_air, ExprCtxt, ExprMode,
};
use crate::util::vec_map;
use air::ast::{
    BinaryOp, Bind, BindX, Binder, BinderX, Command, CommandX, Commands, DeclX, Expr, ExprX, Quant,
    Span, Trigger, Triggers,
};
use air::ast_util::{
    bool_typ, ident_apply, ident_binder, ident_var, mk_and, mk_bind_expr, mk_eq, mk_implies,
    str_apply, str_ident, str_typ, str_var, string_apply,
};
use air::errors::ErrorLabel;
use std::sync::Arc;

// binder for forall (typ_params params)
pub(crate) fn func_bind_trig(
    ctx: &Ctx,
    typ_params: &Idents,
    params: &Pars,
    trig_exprs: &Vec<Expr>,
    add_fuel: bool,
) -> Bind {
    let mut binders: Vec<air::ast::Binder<air::ast::Typ>> = Vec::new();
    for typ_param in typ_params.iter() {
        binders.push(ident_binder(&suffix_typ_param_id(&typ_param), &str_typ(crate::def::TYPE)));
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
    Arc::new(BindX::Quant(Quant::Forall, Arc::new(binders), triggers))
}

// binder for forall (typ_params params)
pub(crate) fn func_bind(
    ctx: &Ctx,
    typ_params: &Idents,
    params: &Pars,
    trig_expr: &Expr,
    add_fuel: bool,
) -> Bind {
    func_bind_trig(ctx, typ_params, params, &vec![trig_expr.clone()], add_fuel)
}

// arguments for function call f(typ_args, params)
pub(crate) fn func_def_typs_args(typ_args: &Typs, params: &Pars) -> Vec<Expr> {
    let mut f_args: Vec<Expr> = Vec::new();
    for typ_arg in typ_args.iter() {
        f_args.push(crate::sst_to_air::typ_to_id(typ_arg));
    }
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
    Ok(mk_bind_expr(&func_bind(ctx, typ_params, params, &f_app, false), &f_imply))
}

fn func_body_to_air(
    ctx: &Ctx,
    decl_commands: &mut Vec<Command>,
    check_commands: &mut Vec<Command>,
    function: &Function,
    body: &crate::ast::Expr,
) -> Result<(), VirErr> {
    let id_fuel = prefix_fuel_id(&fun_to_air_ident(&function.x.name));

    let pars = params_to_pars(&function.x.params, false);

    // ast --> sst
    let mut state = crate::ast_to_sst::State::new();
    state.declare_params(&pars);
    state.view_as_spec = true;
    let body_exp = crate::ast_to_sst::expr_to_pure_exp(&ctx, &mut state, &body)?;
    let body_exp = state.finalize_exp(&body_exp);

    let mut decrease_by_stms: Vec<Stm> = Vec::new();
    let decrease_by_reqs = if let Some(req) = &function.x.decrease_when {
        let exp = crate::ast_to_sst::expr_to_exp(ctx, &pars, req)?;
        let expr = exp_to_expr(ctx, &exp, ExprCtxt { mode: ExprMode::Spec, is_bit_vector: false });
        decrease_by_stms.push(Spanned::new(req.span.clone(), StmX::Assume(exp)));
        vec![expr]
    } else {
        vec![]
    };
    if let Some(fun) = &function.x.decrease_by {
        let decrease_by_fun = &ctx.func_map[fun];
        state.view_as_spec = false;
        let (body_stms, _exp) = crate::ast_to_sst::expr_to_stm_or_error(
            &ctx,
            &mut state,
            decrease_by_fun.x.body.as_ref().expect("decreases_by has body"),
        )?;
        decrease_by_stms.extend(body_stms);
    }
    state.finalize();

    // Check termination
    let (is_recursive, termination_commands, body_exp) = crate::recursion::check_termination_exp(
        ctx,
        function,
        state.local_decls,
        &body_exp,
        decrease_by_stms,
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
    let (name, typ_args) = if let FunctionKind::TraitMethodImpl {
        method,
        trait_typ_args,
        datatype,
        datatype_typ_args,
        ..
    } = &function.x.kind
    {
        let self_typ = Arc::new(TypX::Datatype(datatype.clone(), datatype_typ_args.clone()));
        let mut typ_args = vec![self_typ];
        typ_args.append(&mut (**trait_typ_args).clone());
        (method.clone(), typ_args)
    } else {
        let typ_args = vec_map(&function.x.typ_params(), |x| Arc::new(TypX::TypParam(x.clone())));
        (function.x.name.clone(), typ_args)
    };

    // non-recursive:
    //   (axiom (=> (fuel_bool fuel%f) (forall (...) (= (f ...) body))))
    // recursive:
    //   (declare-const fuel_nat%f Fuel)
    //   (axiom (forall (... fuel) (= (rec%f ... fuel) (rec%f ... zero) )))
    //   (axiom (forall (... fuel) (= (rec%f ... (succ fuel)) body[rec%f ... fuel] )))
    //   (axiom (=> (fuel_bool fuel%f) (forall (...) (= (f ...) (rec%f ... (succ fuel_nat%f))))))
    let body_expr =
        exp_to_expr(&ctx, &body_exp, ExprCtxt { mode: ExprMode::Body, is_bit_vector: false });
    let def_body = if !is_recursive {
        body_expr
    } else {
        let rec_f = suffix_global_id(&fun_to_air_ident(&prefix_recursive_fun(&name)));
        let fuel_nat_f = prefix_fuel_nat(&fun_to_air_ident(&name));
        let args = func_def_args(&function.x.typ_params(), &pars);
        let mut args_zero = args.clone();
        let mut args_fuel = args.clone();
        let mut args_succ = args.clone();
        let mut args_def = args;
        args_zero.push(str_var(ZERO));
        args_fuel.push(str_var(FUEL_LOCAL));
        args_succ.push(str_apply(SUCC, &vec![str_var(FUEL_LOCAL)]));
        args_def.push(str_apply(SUCC, &vec![ident_var(&fuel_nat_f)]));
        let rec_f_zero = ident_apply(&rec_f, &args_zero);
        let rec_f_fuel = ident_apply(&rec_f, &args_fuel);
        let rec_f_succ = ident_apply(&rec_f, &args_succ);
        let rec_f_def = ident_apply(&rec_f, &args_def);
        let eq_zero = mk_eq(&rec_f_fuel, &rec_f_zero);
        let eq_body = mk_eq(&rec_f_succ, &body_expr);
        let bind_zero = func_bind(ctx, &function.x.typ_params(), &pars, &rec_f_fuel, true);
        let bind_body = func_bind(ctx, &function.x.typ_params(), &pars, &rec_f_succ, true);
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
        &function.x.typ_params(),
        &Arc::new(typ_args),
        &pars,
        &decrease_by_reqs,
        def_body,
    )?;
    let fuel_bool = str_apply(FUEL_BOOL, &vec![ident_var(&id_fuel)]);
    let def_axiom = Arc::new(DeclX::Axiom(mk_implies(&fuel_bool, &e_forall)));
    decl_commands.push(Arc::new(CommandX::Global(def_axiom)));
    Ok(())
}

pub fn req_ens_to_air(
    ctx: &Ctx,
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
            all_typs.insert(0, str_typ(crate::def::TYPE));
        }
        let decl = Arc::new(DeclX::Fun(name.clone(), Arc::new(all_typs), bool_typ()));
        commands.push(Arc::new(CommandX::Global(decl)));
        let mut exprs: Vec<Expr> = Vec::new();
        for e in typing_invs {
            exprs.push(e.clone());
        }
        for e in specs.iter() {
            let exp = crate::ast_to_sst::expr_to_exp(ctx, params, e)?;
            let expr =
                exp_to_expr(ctx, &exp, ExprCtxt { mode: ExprMode::Spec, is_bit_vector: false });
            let loc_expr = match msg {
                None => expr,
                Some(msg) => {
                    let l = ErrorLabel { span: e.span.clone(), msg: msg.clone() };
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
pub fn func_name_to_air(ctx: &Ctx, function: &Function) -> Result<Commands, VirErr> {
    let mut commands: Vec<Command> = Vec::new();
    if function.x.mode == Mode::Spec {
        if let FunctionKind::TraitMethodImpl { .. } = &function.x.kind {
            // Implementations of trait methods use the trait method declaration's function,
            // so there's no need to declare another function.
            return Ok(Arc::new(vec![]));
        }

        let mut all_typs = vec_map(&function.x.params, |param| typ_to_air(ctx, &param.x.typ));
        for _ in function.x.typ_bounds.iter() {
            all_typs.insert(0, str_typ(crate::def::TYPE));
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
                &params_to_pars(&function.x.params, false),
                &body,
            )?;
            if crate::recursion::is_recursive_exp(ctx, &function.x.name, &body_exp) {
                let rec_f =
                    suffix_global_id(&fun_to_air_ident(&prefix_recursive_fun(&function.x.name)));
                let mut rec_typs =
                    vec_map(&*function.x.params, |param| typ_to_air(ctx, &param.x.typ));
                for _ in function.x.typ_bounds.iter() {
                    rec_typs.insert(0, str_typ(crate::def::TYPE));
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
        let ParamX { name, typ, mode, is_mut } = p;
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
    function: &Function,
    public_body: bool,
) -> Result<(Commands, Commands), VirErr> {
    // let typ_params: Vec<_> = funxtion.x.typ_bounds.iter().map(|_| str_typ(crate::def::TYPE)).collect();
    let req_typs: Arc<Vec<_>> =
        Arc::new(function.x.params.iter().map(|param| typ_to_air(ctx, &param.x.typ)).collect());
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
    if function.x.require.len() > 0 {
        let msg = match (function.x.mode, &function.x.attrs.custom_req_err) {
            // We don't highlight the failed precondition if the programmer supplied their own msg
            (_, Some(_)) => None,
            // Standard message
            (Mode::Spec, None) => Some("recommendation not met".to_string()),
            (_, None) => Some("failed precondition".to_string()),
        };
        let req_params = params_to_pre_post_pars(&function.x.params, true);
        let _ = req_ens_to_air(
            ctx,
            &mut decl_commands,
            &req_params,
            &vec![],
            &function.x.require,
            &function.x.typ_params(),
            &req_typs,
            &prefix_requires(&fun_to_air_ident(&function.x.name)),
            &msg,
        )?;
    }
    match function.x.mode {
        Mode::Spec => {
            // Body
            if public_body {
                if let Some(body) = &function.x.body {
                    func_body_to_air(ctx, &mut decl_commands, &mut check_commands, function, body)?;
                }
            }

            if let FunctionKind::TraitMethodImpl { .. } = &function.x.kind {
                // For a trait method implementation, we just need to supply a body axiom
                // for the existing trait method declaration function, so we can return here.
                return Ok((Arc::new(decl_commands), Arc::new(check_commands)));
            }

            let name = suffix_global_id(&fun_to_air_ident(&function.x.name));

            // Return typing invariant
            let mut f_args: Vec<Expr> = Vec::new();
            let mut f_pre: Vec<Expr> = Vec::new();
            for typ_param in function.x.typ_params().iter() {
                f_args.push(ident_var(&suffix_typ_param_id(&typ_param.clone())));
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
                let e_forall = mk_bind_expr(
                    &func_bind(
                        ctx,
                        &function.x.typ_params(),
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
                return Ok((Arc::new(decl_commands), Arc::new(check_commands)));
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
                &mut decl_commands,
                &Arc::new(ens_params),
                &ens_typing_invs,
                &function.x.ensure,
                &function.x.typ_params(),
                &Arc::new(ens_typs),
                &prefix_ensures(&fun_to_air_ident(&function.x.name)),
                &None,
            )?;
            if has_ens_pred {
                ctx.funcs_with_ensure_predicate.insert(function.x.name.clone());
            }
            if function.x.attrs.broadcast_forall {
                let span = &function.span;
                let req = crate::ast_util::conjoin(span, &*function.x.require);
                let ens = crate::ast_util::conjoin(span, &*function.x.ensure);
                let req_ens = crate::ast_util::mk_implies(span, &req, &ens);
                let exp = crate::ast_to_sst::expr_to_bind_decls_exp(ctx, &params, &req_ens)?;
                let mut vars: Vec<Ident> = Vec::new();
                let mut binders: Vec<Binder<Typ>> = Vec::new();
                for (name, bound) in function.x.typ_bounds.iter() {
                    match &**bound {
                        GenericBoundX::Traits(ts) if ts.len() == 0 => {
                            vars.push(crate::def::suffix_typ_param_id(&name));
                            let typ = Arc::new(TypX::TypeId);
                            let bind = BinderX { name: name.clone(), a: typ };
                            binders.push(Arc::new(bind));
                        }
                        GenericBoundX::Traits(_) => {
                            todo!()
                        }
                        GenericBoundX::FnSpec(..) => {}
                    }
                }
                for param in params.iter() {
                    vars.push(param.x.name.clone());
                    binders.push(crate::ast_util::par_to_binder(&param));
                }
                let triggers = crate::triggers::build_triggers(ctx, span, &vars, &exp)?;
                let bndx = BndX::Quant(Quant::Forall, Arc::new(binders), triggers);
                let forallx = ExpX::Bind(Spanned::new(span.clone(), bndx), exp);
                let forall = SpannedTyped::new(&span, &Arc::new(TypX::Bool), forallx);
                let expr = exp_to_expr(
                    ctx,
                    &forall,
                    ExprCtxt { mode: ExprMode::Spec, is_bit_vector: false },
                );
                let axiom = Arc::new(DeclX::Axiom(expr));
                decl_commands.push(Arc::new(CommandX::Global(axiom)));
            }
        }
    }
    Ok((Arc::new(decl_commands), Arc::new(check_commands)))
}

pub fn func_def_to_air(
    ctx: &Ctx,
    function: &Function,
) -> Result<(Commands, Vec<(Span, SnapPos)>), VirErr> {
    match (
        function.x.mode,
        function.x.is_const || function.x.attrs.check_recommends,
        function.x.body.as_ref(),
    ) {
        (Mode::Spec, true, Some(body))
        | (Mode::Proof, _, Some(body))
        | (Mode::Exec, _, Some(body)) => {
            // Note: since is_const functions serve double duty as exec and spec,
            // we generate an exec check for them here to catch any arithmetic overflows.
            let (trait_typ_substs, req_ens_function) = if let FunctionKind::TraitMethodImpl {
                method,
                trait_path,
                trait_typ_args,
                datatype,
                datatype_typ_args,
            } = &function.x.kind
            {
                // Inherit requires/ensures from trait method declaration
                let self_typ =
                    Arc::new(TypX::Datatype(datatype.clone(), datatype_typ_args.clone()));
                let mut trait_typ_substs: Vec<(Ident, Typ)> =
                    vec![(crate::def::trait_self_type_param(), self_typ)];
                let tr = &ctx.trait_map[trait_path];
                assert!(tr.x.typ_params.len() == trait_typ_args.len());
                for ((x, _, _), t) in tr.x.typ_params.iter().zip(trait_typ_args.iter()) {
                    trait_typ_substs.push((x.clone(), t.clone()));
                }
                (trait_typ_substs, &ctx.func_map[method])
            } else {
                (vec![], function)
            };

            let mut state = crate::ast_to_sst::State::new();
            let mut ens_params = (*function.x.params).clone();
            let dest = if function.x.has_return() {
                let ParamX { name, typ, .. } = &function.x.ret.x;
                ens_params.push(function.x.ret.clone());
                state.declare_new_var(name, typ, false, false);
                Some((name.clone(), Some(0)))
            } else {
                None
            };
            let ens_params = Arc::new(ens_params);
            let req_pars = params_to_pars(&function.x.params, true);
            let ens_pars = params_to_pars(&ens_params, true);

            for param in function.x.params.iter() {
                state.declare_new_var(&param.x.name, &param.x.typ, param.x.is_mut, false);
            }

            let mut req_stmts: Vec<Stm> = Vec::new();
            let mut reqs: Vec<Exp> = Vec::new();
            for e in req_ens_function.x.require.iter() {
                if ctx.checking_recommends() {
                    let (stms, exp) =
                        crate::ast_to_sst::expr_to_pure_exp_check(ctx, &mut state, e)?;
                    req_stmts.extend(stms);
                    req_stmts.push(Spanned::new(exp.span.clone(), StmX::Assume(exp)));
                } else {
                    reqs.push(crate::ast_to_sst::expr_to_exp(ctx, &req_pars, e)?);
                }
            }
            let mut ens_stmts: Vec<Stm> = Vec::new();
            let mut enss: Vec<Exp> = Vec::new();
            for e in req_ens_function.x.ensure.iter() {
                if ctx.checking_recommends() {
                    ens_stmts.extend(crate::ast_to_sst::check_pure_expr(ctx, &mut state, e)?);
                } else {
                    enss.push(crate::ast_to_sst::expr_to_exp(ctx, &ens_pars, e)?);
                }
            }
            let enss = Arc::new(enss);

            // AST --> SST
            state.ret_post = Some((dest.clone(), ens_stmts.clone(), enss.clone()));
            let (mut stm, skip_ensures) =
                crate::ast_to_sst::expr_to_one_stm_dest(&ctx, &mut state, &body, &dest)?;
            if ctx.checking_recommends() && trait_typ_substs.len() == 0 {
                req_stmts.push(stm);
                if !skip_ensures {
                    req_stmts.extend(ens_stmts);
                }
                stm = crate::ast_to_sst::stms_to_one_stm(&body.span, req_stmts);
            }
            let stm = state.finalize_stm(&stm);
            state.ret_post = None;

            // Check termination
            let (decls, stm) = if ctx.checking_recommends() {
                (vec![], stm)
            } else {
                crate::recursion::check_termination_stm(ctx, function, &stm)?
            };

            // SST --> AIR
            for decl in decls {
                state.new_statement_var(&decl.ident.0);
                state.local_decls.push(decl.clone());
            }

            let (commands, snap_map) = crate::sst_to_air::body_stm_to_air(
                ctx,
                &trait_typ_substs,
                &function.x.typ_params(),
                &function.x.params,
                &state.local_decls,
                &function.x.attrs.hidden,
                &reqs,
                &enss,
                &function.x.mask_spec,
                function.x.mode,
                &stm,
                function.x.attrs.bit_vector,
                skip_ensures,
                function.x.attrs.nonlinear,
            );

            state.finalize();
            Ok((commands, snap_map))
        }
        _ => Ok((Arc::new(vec![]), vec![])),
    }
}
