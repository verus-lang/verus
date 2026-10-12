use crate::ast::{
    CrateId, Dt, Place, PlaceX, Primitive, SpannedTyped, Typ, TypDecoration, TypX, UnaryOp,
};
use crate::ast_util::undecorate_typ;
use crate::def::user_local_name;
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

pub fn permission_place_to_friendly_string(p: &Place) -> String {
    permission_place_to_friendly_string_rec(p, false)
}

fn permission_place_to_friendly_string_rec(p: &Place, has_suffix: bool) -> String {
    let mut stars = "".to_string();
    let mut inner_star = false;

    let mut typ = &p.typ;
    while let TypX::Decorate(TypDecoration::Ref | TypDecoration::Box, _, t) = &**typ {
        typ = t;
        stars += "*";
    }

    let inner: String = match &p.x {
        PlaceX::Local(x) => user_local_name(x).to_string(),
        PlaceX::Field(opr, p) => {
            format!("{:}.{:}", permission_place_to_friendly_string_rec(p, true), opr.field)
        }
        PlaceX::DerefMut(p) | PlaceX::ModeUnwrap(p, _) => {
            inner_star = true;
            format!("*{:}", permission_place_to_friendly_string_rec(p, false))
        }
        PlaceX::Index(..)
        | PlaceX::Temporary(..)
        | PlaceX::WithExpr(..)
        | PlaceX::UserDefinedTypInvariantObligation(..)
        | PlaceX::DerefRaw(..) => "[verus internal error: unexpected place]".to_string(),
    };

    let has_stars = stars.len() > 0 || inner_star;
    let res = stars + &inner;
    if has_suffix && has_stars { "(".to_string() + &res + ")" } else { res }
}
