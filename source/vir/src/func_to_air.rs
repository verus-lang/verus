use crate::ast::{Function, Mode, VirErr};
use crate::context::Ctx;
use crate::sst_to_air::typ_to_air;
use crate::util::box_slice_map;
use air::ast::{CommandX, Commands, DeclX};
use std::rc::Rc;

pub fn func_decl_to_air(function: &Function) -> Result<Commands, VirErr> {
    match (function.x.mode, function.x.ret.as_ref()) {
        (Mode::Spec, Some(ret)) => {
            let typ = typ_to_air(&ret);
            let typs = box_slice_map(&function.x.params, |param| typ_to_air(&param.x.typ));
            let decl = Rc::new(DeclX::Fun(function.x.name.clone(), Rc::new(typs), typ));
            let global = Rc::new(CommandX::Global(decl));
            Ok(Rc::new(Box::new([global])))
        }
        _ => Ok(Rc::new(Box::new([]))),
    }
}

pub fn func_def_to_air(ctx: &Ctx, function: &Function) -> Result<Commands, VirErr> {
    match (function.x.mode, function.x.ret.as_ref(), function.x.body.as_ref()) {
        (Mode::Spec, Some(_ret), Some(_body)) => {
            todo!("#[spec] fn with body")
        }
        (Mode::Exec, _, Some(body)) | (Mode::Proof, _, Some(body)) => {
            let stm = crate::ast_to_sst::expr_to_stm(&ctx, &body)?;
            let commands = crate::sst_to_air::stm_to_air(&function.x.params, &stm);
            Ok(commands)
        }
        _ => Ok(Rc::new(Box::new([]))),
    }
}
