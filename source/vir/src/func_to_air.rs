use crate::ast::{Function, Ident, Mode, ParamX, Params, VirErr};
use crate::context::Ctx;
use crate::def::{
    prefix_ensures, prefix_fuel_id, prefix_requires, suffix_global_id, suffix_local_id, Spanned,
    FUEL_BOOL, FUEL_BOOL_DEFAULT,
};
use crate::sst_to_air::{exp_to_expr, typ_invariant, typ_to_air};
use crate::util::{vec_map, vec_map_result};
use air::ast::{
    BinaryOp, Bind, BindX, Command, CommandX, Commands, DeclX, Expr, ExprX, MultiOp, Quant, Span,
    Trigger, Triggers,
};
use air::ast_util::{bool_typ, ident_apply, ident_binder, ident_var, str_apply, string_apply};
use std::rc::Rc;

fn func_bind(params: &Params, trig_expr: &Expr) -> Bind {
    let binders = Rc::new(vec_map(params, |param| {
        ident_binder(&suffix_local_id(&param.x.name.clone()), &typ_to_air(&param.x.typ))
    }));
    let trigger: Trigger = Rc::new(vec![trig_expr.clone()]);
    let triggers: Triggers = Rc::new(vec![trigger]);
    Rc::new(BindX::Quant(Quant::Forall, binders, triggers))
}

// (forall (...) (= (f ...) body))
fn func_def_quant(name: &Ident, params: &Params, body: Expr) -> Result<Expr, VirErr> {
    let f_args =
        Rc::new(vec_map(params, |param| ident_var(&suffix_local_id(&param.x.name.clone()))));
    let f_app = string_apply(name, &f_args);
    let f_eq = Rc::new(ExprX::Binary(BinaryOp::Eq, f_app.clone(), body));
    Ok(Rc::new(ExprX::Bind(func_bind(params, &f_app), f_eq)))
}

fn func_body_to_air(
    ctx: &Ctx,
    commands: &mut Vec<Command>,
    function: &Function,
    body: &crate::ast::Expr,
) -> Result<(), VirErr> {
    let id_fuel = prefix_fuel_id(&function.x.name);

    // (axiom (fuel_bool_default fuel%f))
    if function.x.fuel > 0 {
        let expr_fuel_default = str_apply(&FUEL_BOOL_DEFAULT, &vec![ident_var(&id_fuel)]);
        let fuel_assert = Rc::new(DeclX::Axiom(expr_fuel_default));
        commands.push(Rc::new(CommandX::Global(fuel_assert)));
    }

    // (axiom (=> (fuel_bool fuel%f) (forall (...) (= (f ...) ...)))
    let body_exp = crate::ast_to_sst::expr_to_exp(&ctx, &body)?;
    let body_expr = exp_to_expr(&body_exp);
    let e_forall =
        func_def_quant(&suffix_global_id(&function.x.name), &function.x.params, body_expr)?;
    let fuel_bool = str_apply(FUEL_BOOL, &vec![ident_var(&id_fuel)]);
    let imply = Rc::new(ExprX::Binary(BinaryOp::Implies, fuel_bool, e_forall));
    let def_axiom = Rc::new(DeclX::Axiom(imply));
    commands.push(Rc::new(CommandX::Global(def_axiom)));
    Ok(())
}

pub fn req_ens_to_air(
    ctx: &Ctx,
    commands: &mut Vec<Command>,
    params: &Params,
    typing_invs: &Vec<Expr>,
    specs: &Vec<crate::ast::Expr>,
    typs: &air::ast::Typs,
    name: &Ident,
    msg: &Option<String>,
) -> Result<(), VirErr> {
    if specs.len() + typing_invs.len() > 0 {
        let decl = Rc::new(DeclX::Fun(name.clone(), typs.clone(), bool_typ()));
        commands.push(Rc::new(CommandX::Global(decl)));
        let mut exprs: Vec<Expr> = Vec::new();
        for e in typing_invs {
            exprs.push(e.clone());
        }
        for e in specs.iter() {
            let exp = crate::ast_to_sst::expr_to_exp(ctx, e)?;
            let expr = exp_to_expr(&exp);
            let loc_expr = match msg {
                None => expr,
                Some(msg) => {
                    let description = Some(msg.clone());
                    let option_span = Rc::new(Some(Span { description, ..e.span.clone() }));
                    Rc::new(ExprX::LabeledAssertion(option_span, expr))
                }
            };
            exprs.push(loc_expr);
        }
        let body = Rc::new(ExprX::Multi(MultiOp::And, Rc::new(exprs)));
        let e_forall = func_def_quant(&name, params, body)?;
        let req_ens_axiom = Rc::new(DeclX::Axiom(e_forall));
        commands.push(Rc::new(CommandX::Global(req_ens_axiom)));
    }
    Ok(())
}

pub fn func_decl_to_air(ctx: &Ctx, function: &Function) -> Result<Commands, VirErr> {
    let typs = Rc::new(vec_map(&function.x.params, |param| typ_to_air(&param.x.typ)));
    let mut commands: Vec<Command> = Vec::new();
    match (function.x.mode, function.x.ret.as_ref()) {
        (Mode::Spec, Some((_, ret, _))) => {
            let typ = typ_to_air(&ret);

            // Declare function
            let name = suffix_global_id(&function.x.name);
            let decl = Rc::new(DeclX::Fun(name.clone(), typs.clone(), typ));
            commands.push(Rc::new(CommandX::Global(decl)));

            // Body
            if let Some(body) = &function.x.body {
                func_body_to_air(ctx, &mut commands, function, body)?;
            }

            // Return typing invariant
            let f_args = Rc::new(vec_map(&function.x.params, |param| {
                ident_var(&suffix_local_id(&param.x.name.clone()))
            }));
            let f_app = ident_apply(&name, &f_args);
            if let Some(expr) = typ_invariant(&ret, &f_app) {
                // (axiom (forall (...) expr))
                let e_forall = Rc::new(ExprX::Bind(func_bind(&function.x.params, &f_app), expr));
                let inv_axiom = Rc::new(DeclX::Axiom(e_forall));
                commands.push(Rc::new(CommandX::Global(inv_axiom)));
            }
        }
        (Mode::Exec, _) | (Mode::Proof, _) => {
            req_ens_to_air(
                ctx,
                &mut commands,
                &function.x.params,
                &vec![],
                &function.x.require,
                &typs,
                &prefix_requires(&function.x.name),
                &Some("failed precondition".to_string()),
            )?;
            let mut ens_typs = (*typs).clone();
            let mut ens_params = (*function.x.params).clone();
            let mut ens_typing_invs: Vec<Expr> = Vec::new();
            if let Some((name, typ, mode)) = &function.x.ret {
                let param = ParamX { name: name.clone(), typ: typ.clone(), mode: *mode };
                ens_typs.push(typ_to_air(&typ));
                ens_params.push(Spanned::new(function.span.clone(), param));
                if let Some(expr) = typ_invariant(&typ, &ident_var(&suffix_local_id(&name))) {
                    ens_typing_invs.push(expr.clone());
                }
            }
            req_ens_to_air(
                ctx,
                &mut commands,
                &Rc::new(ens_params),
                &ens_typing_invs,
                &function.x.ensure,
                &Rc::new(ens_typs),
                &prefix_ensures(&function.x.name),
                &None,
            )?;
        }
        _ => {}
    }
    Ok(Rc::new(commands))
}

pub fn func_def_to_air(ctx: &Ctx, function: &Function) -> Result<Commands, VirErr> {
    match (function.x.mode, function.x.ret.as_ref(), function.x.body.as_ref()) {
        (Mode::Exec, _, Some(body)) | (Mode::Proof, _, Some(body)) => {
            let dest = function.x.ret.as_ref().map(|(x, _, _)| x.clone());
            let reqs =
                vec_map_result(&*function.x.require, |e| crate::ast_to_sst::expr_to_exp(ctx, e))?;
            let enss =
                vec_map_result(&*function.x.ensure, |e| crate::ast_to_sst::expr_to_exp(ctx, e))?;
            let stm = crate::ast_to_sst::expr_to_stm(&ctx, &body, &dest)?;
            let commands = crate::sst_to_air::stm_to_air(
                ctx,
                &function.x.params,
                &function.x.ret,
                &function.x.hidden,
                &reqs,
                &enss,
                &stm,
            );
            Ok(commands)
        }
        _ => Ok(Rc::new(vec![])),
    }
}
