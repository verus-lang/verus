use crate::ast::{BinaryOp, BinaryOpr, Mode, Typ, TypX, UnaryOp, UnaryOpr};
use crate::context::Ctx;
use crate::sst::{BndX, Exp, ExpX};
use std::sync::Arc;

fn auto_ext_equal_typ(ctx: &Ctx, typ: &Typ) -> bool {
    match &**typ {
        TypX::Int(_) => false,
        TypX::Bool => false,
        TypX::Tuple(_) => panic!("internal error: Tuple should have been removed by ast_simplify"),
        TypX::SpecFn(_, _) => true,
        TypX::AnonymousClosure(..) => {
            panic!("internal error: AnonymousClosure should have been removed by ast_simplify")
        }
        TypX::Datatype(path, _, _) => ctx.datatype_map[path].x.ext_equal,
        TypX::Decorate(_, _, t) => auto_ext_equal_typ(ctx, t),
        TypX::Boxed(typ) => auto_ext_equal_typ(ctx, typ),
        TypX::TypParam(_) => false,
        TypX::Projection { .. } => false,
        TypX::TypeId => panic!("internal error: uses_ext_equal of TypeId"),
        TypX::ConstInt(_) => false,
        TypX::Air(_) => panic!("internal error: uses_ext_equal of Air"),
        TypX::Primitive(crate::ast::Primitive::Array, _) => true,
        TypX::Primitive(crate::ast::Primitive::Slice, _) => true,
        TypX::Primitive(crate::ast::Primitive::StrSlice, _) => true,
        TypX::Primitive(crate::ast::Primitive::Ptr, _) => false,
        TypX::Primitive(crate::ast::Primitive::Global, _) => false,
        TypX::FnDef(..) => false,
    }
}

pub(crate) fn insert_ext_eq_in_assert(ctx: &Ctx, exp: &Exp) -> Exp {
    // In ordinary asserts,
    // in positive positions,
    // for == on types explicitly supporting ext_eq,
    // replace == with =~=
    // Example:
    //   assert(b ==> c && x == y); // x: S and y: S where S is ext_eq
    // -->
    //   assert(b ==> c && x =~= y);
    // Rationale: assert and assert-by are sort of tactics for various proof techniques
    // (e.g. nonlinear_arith, bit_vector, compute),
    // and in this spirit,
    // the ordinary assert can supply a default "tactic" with some basic heuristics.
    // (To opt out of such heuristics, we could support something like "assert(expr) by()"
    // with an empty by().)
    match &exp.x {
        ExpX::Unary(op, e) => match op {
            UnaryOp::Not | UnaryOp::BitNot(_) | UnaryOp::Clip { .. } => exp.clone(),
            UnaryOp::StrLen | UnaryOp::StrIsAscii => exp.clone(),
            UnaryOp::InferSpecForLoopIter { .. } => exp.clone(),
            UnaryOp::Trigger(_)
            | UnaryOp::CoerceMode { .. }
            | UnaryOp::MustBeFinalized
            | UnaryOp::MustBeElaborated
            | UnaryOp::HeightTrigger
            | UnaryOp::CastToInteger => {
                exp.new_x(ExpX::Unary(*op, insert_ext_eq_in_assert(ctx, e)))
            }
        },
        ExpX::UnaryOpr(op, e) => match op {
            UnaryOpr::HasType(_) | UnaryOpr::IsVariant { .. } => exp.clone(),
            UnaryOpr::TupleField { .. } | UnaryOpr::Field(_) => exp.clone(),
            UnaryOpr::IntegerTypeBound(..) => exp.clone(),
            UnaryOpr::Box(_) | UnaryOpr::Unbox(_) | UnaryOpr::CustomErr(_) => {
                exp.new_x(ExpX::UnaryOpr(op.clone(), insert_ext_eq_in_assert(ctx, e)))
            }
        },
        ExpX::Binary(op, e1, e2) => match op {
            BinaryOp::Eq(Mode::Spec)
                if auto_ext_equal_typ(ctx, &e1.typ)
                    && crate::ast_util::types_equal(&e1.typ, &e2.typ) =>
            {
                let op = BinaryOpr::ExtEq(false, e1.typ.clone());
                let e1 = crate::poly::coerce_exp_to_poly(ctx, e1);
                let e2 = crate::poly::coerce_exp_to_poly(ctx, e2);
                exp.new_x(ExpX::BinaryOpr(op, e1, e2))
            }
            BinaryOp::And | BinaryOp::Or => {
                let e1 = insert_ext_eq_in_assert(ctx, e1);
                let e2 = insert_ext_eq_in_assert(ctx, e2);
                exp.new_x(ExpX::Binary(*op, e1, e2))
            }
            BinaryOp::Implies => {
                let e2 = insert_ext_eq_in_assert(ctx, e2);
                exp.new_x(ExpX::Binary(*op, e1.clone(), e2))
            }
            BinaryOp::Eq(_)
            | BinaryOp::HeightCompare { .. }
            | BinaryOp::Ne
            | BinaryOp::Inequality(_)
            | BinaryOp::Xor
            | BinaryOp::Arith(..)
            | BinaryOp::Bitwise(..)
            | BinaryOp::StrGetChar
            | BinaryOp::ArrayIndex => exp.clone(),
        },
        ExpX::BinaryOpr(BinaryOpr::ExtEq(..), _, _) => exp.clone(),
        ExpX::If(e1, e2, e3) => {
            let e2 = insert_ext_eq_in_assert(ctx, e2);
            let e3 = insert_ext_eq_in_assert(ctx, e3);
            exp.new_x(ExpX::If(e1.clone(), e2, e3))
        }
        ExpX::WithTriggers(trigs, e) => {
            let e = insert_ext_eq_in_assert(ctx, e);
            exp.new_x(ExpX::WithTriggers(trigs.clone(), e.clone()))
        }
        ExpX::Bind(bnd, e) => match &bnd.x {
            BndX::Let(..) | BndX::Quant(..) => {
                let e = insert_ext_eq_in_assert(ctx, e);
                exp.new_x(ExpX::Bind(bnd.clone(), e))
            }
            BndX::Lambda(..) | BndX::Choose(..) => exp.clone(),
        },
        ExpX::ArrayLiteral(es) => {
            let es = es.iter().map(|e| insert_ext_eq_in_assert(ctx, e)).collect();
            exp.new_x(ExpX::ArrayLiteral(Arc::new(es)))
        }
        ExpX::Const(_)
        | ExpX::Var(_)
        | ExpX::StaticVar(_)
        | ExpX::VarLoc(_)
        | ExpX::VarAt(..)
        | ExpX::Loc(_)
        | ExpX::Old(..)
        | ExpX::Call(..)
        | ExpX::CallLambda(..)
        | ExpX::Ctor(..)
        | ExpX::NullaryOpr(_)
        | ExpX::ExecFnByName(_)
        | ExpX::FuelConst(_)
        | ExpX::Interp(_) => exp.clone(),
    }
}
