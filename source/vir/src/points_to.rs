use crate::ast::{CrateId, Dt, Primitive, SpannedTyped, Typ, TypX, UnaryOp};
use crate::ast_util::undecorate_typ;
use crate::sst::*;
use std::sync::Arc;

pub fn sst_get_contents(e: &Exp) -> Exp {
    SpannedTyped::new(
        &e.span,
        &get_points_to_typ_arg(&e.typ),
        ExpX::Unary(UnaryOp::PointsToContents, e.clone()),
    )
}

pub fn sst_get_ptr(e: &Exp) -> Exp {
    let f = CallFun::Fun(crate::fun!(CrateId::Vstd => "raw_ptr", "points_to_ptr"), None);
    let typ = get_points_to_typ_arg(&e.typ);
    let typ_args = Arc::new(vec![typ]);
    let args = Arc::new(vec![e.clone()]);
    let expx = ExpX::Call(f, typ_args.clone(), args);
    let ptr_typ = Arc::new(TypX::Primitive(Primitive::Ptr, typ_args));
    SpannedTyped::new(&e.span, &ptr_typ, expx)
}

pub fn sst_get_is_init(e: &Exp) -> Exp {
    let f = CallFun::Fun(crate::fun!(CrateId::Vstd => "raw_ptr", "points_to_init"), None);
    let typ = get_points_to_typ_arg(&e.typ);
    let typ_args = Arc::new(vec![typ]);
    let args = Arc::new(vec![e.clone()]);
    let expx = ExpX::Call(f, typ_args, args);
    SpannedTyped::new(&e.span, &Arc::new(TypX::Bool), expx)
}

pub fn get_points_to_typ_arg(t: &Typ) -> Typ {
    match &*undecorate_typ(t) {
        TypX::Datatype(Dt::Path(pt), args, _)
            if *pt == crate::path!(CrateId::Vstd => "raw_ptr", "PointsTo") =>
        {
            args[0].clone()
        }
        _ => panic!("get_points_to_typ_arg expected PointsTo type"),
    }
}
