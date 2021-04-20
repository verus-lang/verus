use crate::ast::{Function, Ident, Mode, VirErr};
use crate::context::Ctx;
use crate::def::{prefix_fuel_id, suffix_global_id, suffix_local_id, FUEL_BOOL, FUEL_BOOL_DEFAULT};
use crate::sst::{Stm, StmX};
use crate::sst_to_air::{exp_to_expr, typ_to_air};
use crate::util::box_slice_map;
use air::ast::{
    BinaryOp, BindX, Command, CommandX, Commands, DeclX, ExprX, Quant, Trigger, Triggers,
};
use air::ast_util::{ident_binder, ident_var, str_apply_vec, string_apply};
use std::rc::Rc;

fn func_body_to_air(
    ctx: &Ctx,
    commands: &mut Vec<Command>,
    function: &Function,
    body: &crate::ast::Expr,
) -> Result<(), VirErr> {
    let id_fuel = prefix_fuel_id(&function.x.name);

    // (axiom (fuel_bool_default fuel%f))
    if function.x.fuel > 0 {
        let expr_fuel_default = str_apply_vec(&FUEL_BOOL_DEFAULT, &vec![ident_var(&id_fuel)]);
        let fuel_assert = Rc::new(DeclX::Axiom(expr_fuel_default));
        commands.push(Rc::new(CommandX::Global(fuel_assert)));
    }

    // (axiom (=> (fuel_bool fuel%f) (forall (...) (= (f ...) ...)))
    let body_exp = crate::ast_to_sst::expr_to_exp(&ctx, &body)?;
    let body_expr = exp_to_expr(&body_exp);
    let f_args = Rc::new(box_slice_map(&function.x.params, |param| {
        ident_var(&suffix_local_id(&param.x.name.clone()))
    }));
    let f_app = string_apply(&suffix_global_id(&function.x.name), &f_args);
    let f_eq = Rc::new(ExprX::Binary(BinaryOp::Eq, f_app.clone(), body_expr));
    let binders = Rc::new(box_slice_map(&function.x.params, |param| {
        ident_binder(&suffix_local_id(&param.x.name.clone()), &typ_to_air(&param.x.typ))
    }));
    let trigger: Trigger = Rc::new(Box::new([f_app.clone()]));
    let triggers: Triggers = Rc::new(Box::new([trigger]));
    let bind = Rc::new(BindX::Quant(Quant::Forall, binders, triggers));
    let e_forall = Rc::new(ExprX::Bind(bind, f_eq));
    let fuel_bool = str_apply_vec(FUEL_BOOL, &vec![ident_var(&id_fuel)]);
    let imply = Rc::new(ExprX::Binary(BinaryOp::Implies, fuel_bool, e_forall));
    let def_assert = Rc::new(DeclX::Axiom(imply));
    commands.push(Rc::new(CommandX::Global(def_assert)));
    Ok(())
}

pub fn func_decl_to_air(ctx: &Ctx, function: &Function) -> Result<Commands, VirErr> {
    match (function.x.mode, function.x.ret.as_ref()) {
        (Mode::Spec, Some(ret)) => {
            let mut commands: Vec<Command> = Vec::new();

            // Declare function
            let typ = typ_to_air(&ret);
            let typs = box_slice_map(&function.x.params, |param| typ_to_air(&param.x.typ));
            let name = suffix_global_id(&function.x.name);
            let decl = Rc::new(DeclX::Fun(name, Rc::new(typs), typ));
            commands.push(Rc::new(CommandX::Global(decl)));

            // Body
            match &function.x.body {
                None => {}
                Some(body) => {
                    func_body_to_air(ctx, &mut commands, function, body)?;
                }
            }

            Ok(Rc::new(commands.into_boxed_slice()))
        }
        _ => Ok(Rc::new(Box::new([]))),
    }
}

// Read "hide" declarations from function header
fn read_header(body: &Stm) -> Vec<Ident> {
    let mut hidden: Vec<Ident> = Vec::new();
    match &body.x {
        StmX::Block(stms) => {
            for stm in stms.iter() {
                match &stm.x {
                    StmX::Fuel(x, 0) => {
                        hidden.push(x.clone());
                    }
                    _ => break,
                }
            }
        }
        _ => {}
    }
    hidden
}

pub fn func_def_to_air(ctx: &Ctx, function: &Function) -> Result<Commands, VirErr> {
    match (function.x.mode, function.x.ret.as_ref(), function.x.body.as_ref()) {
        (Mode::Exec, _, Some(body)) | (Mode::Proof, _, Some(body)) => {
            let stm = crate::ast_to_sst::expr_to_stm(&ctx, &body)?;
            let hidden = read_header(&stm);
            let commands = crate::sst_to_air::stm_to_air(&function.x.params, &hidden, &stm);
            Ok(commands)
        }
        _ => Ok(Rc::new(Box::new([]))),
    }
}
