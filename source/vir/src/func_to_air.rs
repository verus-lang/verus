use crate::ast::{Function, Ident, Mode, Params, VirErr};
use crate::context::Ctx;
use crate::def::{
    prefix_fuel_id, prefix_requires, suffix_global_id, suffix_local_id, FUEL_BOOL,
    FUEL_BOOL_DEFAULT,
};
use crate::sst_to_air::{exp_to_expr, typ_to_air};
use crate::util::{vec_map, vec_map_result};
use air::ast::{
    BinaryOp, BindX, Command, CommandX, Commands, DeclX, Expr, ExprX, MultiOp, Quant, Span,
    Trigger, Triggers,
};
use air::ast_util::{bool_typ, ident_binder, ident_var, str_apply, string_apply};
use std::rc::Rc;

// (forall (...) (= (f ...) body))
fn func_def_quant(name: &Ident, params: &Params, body: Expr) -> Result<Expr, VirErr> {
    let f_args =
        Rc::new(vec_map(params, |param| ident_var(&suffix_local_id(&param.x.name.clone()))));
    let f_app = string_apply(name, &f_args);
    let f_eq = Rc::new(ExprX::Binary(BinaryOp::Eq, f_app.clone(), body));
    let binders = Rc::new(vec_map(params, |param| {
        ident_binder(&suffix_local_id(&param.x.name.clone()), &typ_to_air(&param.x.typ))
    }));
    let trigger: Trigger = Rc::new(vec![f_app.clone()]);
    let triggers: Triggers = Rc::new(vec![trigger]);
    let bind = Rc::new(BindX::Quant(Quant::Forall, binders, triggers));
    Ok(Rc::new(ExprX::Bind(bind, f_eq)))
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

pub fn func_decl_to_air(ctx: &Ctx, function: &Function) -> Result<Commands, VirErr> {
    let typs = Rc::new(vec_map(&function.x.params, |param| typ_to_air(&param.x.typ)));
    let mut commands: Vec<Command> = Vec::new();
    match (function.x.mode, function.x.ret.as_ref()) {
        (Mode::Spec, Some(ret)) => {
            let typ = typ_to_air(&ret);

            // Declare function
            let name = suffix_global_id(&function.x.name);
            let decl = Rc::new(DeclX::Fun(name, typs.clone(), typ));
            commands.push(Rc::new(CommandX::Global(decl)));

            // Body
            match &function.x.body {
                None => {}
                Some(body) => {
                    func_body_to_air(ctx, &mut commands, function, body)?;
                }
            }
        }
        (Mode::Exec, None) | (Mode::Proof, None) => {
            // Requires
            if function.x.require.len() > 0 {
                let name = prefix_requires(&function.x.name);
                let decl = Rc::new(DeclX::Fun(name.clone(), typs, bool_typ()));
                commands.push(Rc::new(CommandX::Global(decl)));
                let mut exprs: Vec<Expr> = Vec::new();
                for e in function.x.require.iter() {
                    let exp = crate::ast_to_sst::expr_to_exp(&ctx, &e)?;
                    let expr = exp_to_expr(&exp);
                    let description = Some("failed precondition".to_string());
                    let option_span = Rc::new(Some(Span { description, ..e.span.clone() }));
                    let loc_expr = Rc::new(ExprX::LabeledAssertion(option_span, expr));
                    exprs.push(loc_expr);
                }
                let body = Rc::new(ExprX::Multi(MultiOp::And, Rc::new(exprs)));
                let e_forall = func_def_quant(&name, &function.x.params, body)?;
                let req_axiom = Rc::new(DeclX::Axiom(e_forall));
                commands.push(Rc::new(CommandX::Global(req_axiom)));
            }
        }
        _ => {}
    }
    Ok(Rc::new(commands))
}

pub fn func_def_to_air(ctx: &Ctx, function: &Function) -> Result<Commands, VirErr> {
    match (function.x.mode, function.x.ret.as_ref(), function.x.body.as_ref()) {
        (Mode::Exec, _, Some(body)) | (Mode::Proof, _, Some(body)) => {
            let reqs =
                vec_map_result(&*function.x.require, |e| crate::ast_to_sst::expr_to_exp(ctx, e))?;
            let stm = crate::ast_to_sst::expr_to_stm(&ctx, &body)?;
            let commands = crate::sst_to_air::stm_to_air(
                ctx,
                &function.x.params,
                &function.x.hidden,
                &reqs,
                &stm,
            );
            Ok(commands)
        }
        _ => Ok(Rc::new(vec![])),
    }
}
