use crate::ast::{
    Function, GenericBoundX, Ident, Idents, Mode, ParamX, Params, SpannedTyped, Typ, TypX, VirErr,
};
use crate::context::Ctx;
use crate::def::{
    prefix_ensures, prefix_fuel_id, prefix_fuel_nat, prefix_recursive_fun, prefix_requires,
    suffix_global_id, suffix_local_stmt_id, suffix_typ_param_id, SnapPos, Spanned, FUEL_BOOL,
    FUEL_BOOL_DEFAULT, FUEL_LOCAL, FUEL_TYPE, SUCC, ZERO,
};
use crate::sst::{BndX, ExpX};
use crate::sst_to_air::{exp_to_expr, fun_to_air_ident, typ_invariant, typ_to_air};
use crate::util::{vec_map, vec_map_result};
use air::ast::{
    BinaryOp, Bind, BindX, Binder, BinderX, Command, CommandX, Commands, DeclX, Expr, ExprX,
    MultiOp, Quant, Span, Trigger, Triggers,
};
use air::ast_util::{
    bool_typ, ident_apply, ident_binder, ident_var, mk_and, mk_bind_expr, mk_eq, mk_implies,
    str_apply, str_ident, str_typ, str_var, string_apply,
};
use std::sync::Arc;

// binder for forall (typ_params params)
pub(crate) fn func_bind_trig(
    ctx: &Ctx,
    typ_params: &Idents,
    params: &Params,
    trig_exprs: &Vec<Expr>,
    add_fuel: bool,
) -> Bind {
    let mut binders: Vec<air::ast::Binder<air::ast::Typ>> = Vec::new();
    for typ_param in typ_params.iter() {
        binders.push(ident_binder(&suffix_typ_param_id(&typ_param), &str_typ(crate::def::TYPE)));
    }
    for param in params.iter() {
        binders.push(ident_binder(
            &suffix_local_stmt_id(&param.x.name.clone()),
            &typ_to_air(ctx, &param.x.typ),
        ));
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
    params: &Params,
    trig_expr: &Expr,
    add_fuel: bool,
) -> Bind {
    func_bind_trig(ctx, typ_params, params, &vec![trig_expr.clone()], add_fuel)
}

// arguments for function call f(typ_params, params)
pub(crate) fn func_def_args(typ_params: &Idents, params: &Params) -> Vec<Expr> {
    let mut f_args: Vec<Expr> = Vec::new();
    for typ_param in typ_params.iter() {
        f_args.push(ident_var(&suffix_typ_param_id(&typ_param)));
    }
    for param in params.iter() {
        f_args.push(ident_var(&suffix_local_stmt_id(&param.x.name.clone())));
    }
    f_args
}

// (forall (...) (= (f ...) body))
fn func_def_quant(
    ctx: &Ctx,
    name: &Ident,
    typ_params: &Idents,
    params: &Params,
    body: Expr,
) -> Result<Expr, VirErr> {
    let f_args = func_def_args(typ_params, params);
    let f_app = string_apply(name, &Arc::new(f_args));
    let f_eq = Arc::new(ExprX::Binary(BinaryOp::Eq, f_app.clone(), body));
    Ok(mk_bind_expr(&func_bind(ctx, typ_params, params, &f_app, false), &f_eq))
}

fn func_body_to_air(
    ctx: &Ctx,
    decl_commands: &mut Vec<Command>,
    check_commands: &mut Vec<Command>,
    function: &Function,
    body: &crate::ast::Expr,
) -> Result<(), VirErr> {
    let id_fuel = prefix_fuel_id(&fun_to_air_ident(&function.x.name));

    // ast --> sst
    let (local_decls, body_exp) =
        crate::ast_to_sst::expr_to_decls_exp(&ctx, &function.x.params, &body)?;

    // Check termination
    let (is_recursive, termination_commands, body_exp) =
        crate::recursion::check_termination_exp(ctx, function, local_decls, &body_exp)?;
    check_commands.extend(termination_commands.iter().cloned());

    // non-recursive:
    //   (axiom (fuel_bool_default fuel%f))
    if function.x.fuel > 0 {
        let axiom_expr = str_apply(&FUEL_BOOL_DEFAULT, &vec![ident_var(&id_fuel)]);
        let fuel_axiom = Arc::new(DeclX::Axiom(axiom_expr));
        decl_commands.push(Arc::new(CommandX::Global(fuel_axiom)));
    }

    // non-recursive:
    //   (axiom (=> (fuel_bool fuel%f) (forall (...) (= (f ...) body))))
    // recursive:
    //   (declare-const fuel_nat%f Fuel)
    //   (axiom (forall (... fuel) (= (rec%f ... fuel) (rec%f ... zero) )))
    //   (axiom (forall (... fuel) (= (rec%f ... (succ fuel)) body[rec%f ... fuel] )))
    //   (axiom (=> (fuel_bool fuel%f) (forall (...) (= (f ...) (rec%f ... (succ fuel_nat%f))))))
    let body_expr = exp_to_expr(&ctx, &body_exp);
    let def_body = if !is_recursive {
        body_expr
    } else {
        let rec_f = suffix_global_id(&fun_to_air_ident(&prefix_recursive_fun(&function.x.name)));
        let fuel_nat_f = prefix_fuel_nat(&fun_to_air_ident(&function.x.name));
        let args = func_def_args(&function.x.typ_params(), &function.x.params);
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
        let bind_zero =
            func_bind(ctx, &function.x.typ_params(), &function.x.params, &rec_f_fuel, true);
        let bind_body =
            func_bind(ctx, &function.x.typ_params(), &function.x.params, &rec_f_succ, true);
        let forall_zero = mk_bind_expr(&bind_zero, &eq_zero);
        let forall_body = mk_bind_expr(&bind_body, &eq_body);
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
        &suffix_global_id(&fun_to_air_ident(&function.x.name)),
        &function.x.typ_params(),
        &function.x.params,
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
    params: &Params,
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
            let expr = exp_to_expr(ctx, &exp);
            let loc_expr = match msg {
                None => expr,
                Some(msg) => {
                    let description = Some(msg.clone());
                    let spans = Arc::new(vec![Span { description, ..e.span.clone() }]);
                    Arc::new(ExprX::LabeledAssertion(spans, expr))
                }
            };
            exprs.push(loc_expr);
        }
        let body = Arc::new(ExprX::Multi(MultiOp::And, Arc::new(exprs)));
        let e_forall = func_def_quant(ctx, &name, &typ_params, &params, body)?;
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
    let mut all_typs = vec_map(&function.x.params, |param| typ_to_air(ctx, &param.x.typ));
    for _ in function.x.typ_bounds.iter() {
        all_typs.insert(0, str_typ(crate::def::TYPE));
    }
    let mut commands: Vec<Command> = Vec::new();
    if function.x.mode == Mode::Spec {
        // Declare the function symbol itself
        let typ = typ_to_air(ctx, &function.x.ret.x.typ);
        let name = suffix_global_id(&fun_to_air_ident(&function.x.name));
        let decl = Arc::new(DeclX::Fun(name, Arc::new(all_typs), typ.clone()));
        commands.push(Arc::new(CommandX::Global(decl)));

        // Check whether we need to declare the recursive version too
        if let Some(body) = &function.x.body {
            let body_exp = crate::ast_to_sst::expr_to_exp(&ctx, &function.x.params, &body)?;
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

pub fn func_decl_to_air(
    ctx: &mut Ctx,
    function: &Function,
    public_body: bool,
) -> Result<(Commands, Commands), VirErr> {
    let mut all_typs = vec_map(&function.x.params, |param| typ_to_air(ctx, &param.x.typ));
    let param_typs = Arc::new(all_typs.clone());
    for _ in function.x.typ_bounds.iter() {
        all_typs.insert(0, str_typ(crate::def::TYPE));
    }
    let mut decl_commands: Vec<Command> = Vec::new();
    let mut check_commands: Vec<Command> = Vec::new();
    match function.x.mode {
        Mode::Spec => {
            let name = suffix_global_id(&fun_to_air_ident(&function.x.name));

            // Body
            if public_body {
                if let Some(body) = &function.x.body {
                    func_body_to_air(ctx, &mut decl_commands, &mut check_commands, function, body)?;
                }
            }

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
                    &func_bind(ctx, &function.x.typ_params(), &function.x.params, &f_app, false),
                    &mk_implies(&mk_and(&f_pre), &post),
                );
                let inv_axiom = Arc::new(DeclX::Axiom(e_forall));
                decl_commands.push(Arc::new(CommandX::Global(inv_axiom)));
            }
        }
        Mode::Exec | Mode::Proof => {
            let msg = match &function.x.attrs.custom_req_err {
                // Standard message
                None => Some("failed precondition".to_string()),
                // We don't highlight the failed precondition if the programmer supplied their own msg
                Some(_) => None,
            };
            let _ = req_ens_to_air(
                ctx,
                &mut decl_commands,
                &function.x.params,
                &vec![],
                &function.x.require,
                &function.x.typ_params(),
                &param_typs,
                &prefix_requires(&fun_to_air_ident(&function.x.name)),
                &msg,
            )?;
            let mut ens_typs = (*param_typs).clone();
            let mut ens_params = (*function.x.params).clone();
            let mut ens_typing_invs: Vec<Expr> = Vec::new();
            if function.x.has_return() {
                let ParamX { name, typ, .. } = &function.x.ret.x;
                ens_typs.push(typ_to_air(ctx, &typ));
                ens_params.push(function.x.ret.clone());
                if let Some(expr) =
                    typ_invariant(ctx, &typ, &ident_var(&suffix_local_stmt_id(&name)))
                {
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
            if function.x.attrs.export_as_global_forall {
                let span = &function.span;
                let req = crate::ast_util::conjoin(span, &*function.x.require);
                let ens = crate::ast_util::conjoin(span, &*function.x.ensure);
                let req_ens = crate::ast_util::mk_implies(span, &req, &ens);
                let exp =
                    crate::ast_to_sst::expr_to_bind_decls_exp(ctx, &function.x.params, &req_ens)?;
                let mut vars: Vec<Ident> = Vec::new();
                let mut binders: Vec<Binder<Typ>> = Vec::new();
                for (name, bound) in function.x.typ_bounds.iter() {
                    match &**bound {
                        GenericBoundX::None => {
                            vars.push(crate::def::suffix_typ_param_id(&name));
                            let typ = Arc::new(TypX::TypeId);
                            let bind = BinderX { name: name.clone(), a: typ };
                            binders.push(Arc::new(bind));
                        }
                        GenericBoundX::FnSpec(..) => {}
                    }
                }
                for param in function.x.params.iter() {
                    vars.push(param.x.name.clone());
                    binders.push(crate::ast_util::param_to_binder(&param));
                }
                let triggers = crate::triggers::build_triggers(ctx, span, &vars, &exp)?;
                let bndx = BndX::Quant(Quant::Forall, Arc::new(binders), triggers);
                let forallx = ExpX::Bind(Spanned::new(span.clone(), bndx), exp);
                let forall = SpannedTyped::new(&span, &Arc::new(TypX::Bool), forallx);
                let expr = exp_to_expr(ctx, &forall);
                let axiom = Arc::new(DeclX::Axiom(expr));
                decl_commands.push(Arc::new(CommandX::Global(axiom)));
            }
            if function.x.attrs.bit_vector {
                // TODO: function level bitvector mode
                unimplemented!("function level bitvector mode");
            }
        }
    }
    Ok((Arc::new(decl_commands), Arc::new(check_commands)))
}

pub fn func_def_to_air(
    ctx: &Ctx,
    function: &Function,
) -> Result<(Commands, Vec<(Span, SnapPos)>), VirErr> {
    match (function.x.mode, function.x.ret.as_ref(), function.x.body.as_ref()) {
        (Mode::Exec, _, Some(body)) | (Mode::Proof, _, Some(body)) => {
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
            let reqs = vec_map_result(&*function.x.require, |e| {
                crate::ast_to_sst::expr_to_exp(ctx, &function.x.params, e)
            })?;
            let enss = vec_map_result(&*function.x.ensure, |e| {
                crate::ast_to_sst::expr_to_exp(ctx, &ens_params, e)
            })?;
            let enss = Arc::new(enss);
            for param in function.x.params.iter() {
                state.declare_new_var(&param.x.name, &param.x.typ, false, false);
            }

            // AST --> SST
            state.ret_post = Some((dest.clone(), enss.clone()));
            let stm = crate::ast_to_sst::expr_to_one_stm_dest(&ctx, &mut state, &body, &dest)?;
            let stm = state.finalize_stm(&stm);
            state.ret_post = None;

            // Check termination
            let (decls, stm) = crate::recursion::check_termination_stm(ctx, function, &stm)?;

            // SST --> AIR
            for decl in decls {
                state.new_statement_var(&decl.ident.0);
                state.local_decls.push(decl.clone());
            }
            let (commands, snap_map) = crate::sst_to_air::body_stm_to_air(
                ctx,
                &function.x.typ_params(),
                &function.x.params,
                &state.local_decls,
                &function.x.attrs.hidden,
                &reqs,
                &*enss,
                &stm,
            );
            state.finalize();
            Ok((commands, snap_map))
        }
        _ => Ok((Arc::new(vec![]), vec![])),
    }
}
