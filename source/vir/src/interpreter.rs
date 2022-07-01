//! A Symbolic Interpreter for VIR
//!
//! Operates on VIR's SST representation
//!
//! Current target is supporting proof by computation
//! https://github.com/secure-foundations/verus/discussions/120

#[allow(unused_imports)]
use crate::ast::{
    ArithOp, BinaryOp, BitwiseOp, Constant, InequalityOp, IntRange, SpannedTyped, UnaryOp,
    UnaryOpr, VirErr,
};
use crate::ast_util::err_string;
#[allow(unused_imports)]
use crate::sst::{BndX, Dest, Exp, ExpX, Stm, StmX, UniqueIdent};
#[allow(unused_imports)]
use crate::sst_visitor::{map_exp_visitor_bind, map_stm_visitor, VisitorScopeMap};
#[allow(unused_imports)]
use crate::visitor::VisitorControlFlow;
use air::scope_map::ScopeMap;
use num_bigint::{BigInt, Sign};
use num_traits::identities::Zero;
use num_traits::{One, Signed, ToPrimitive};
use std::collections::HashMap;
//use std::convert::TryInto;

type Env = HashMap<UniqueIdent, Exp>;

// TODO: Add support for function evaluation memoization

fn eval_expr_internal(env: &Env, exp: &Exp, _map: &mut VisitorScopeMap) -> Result<Exp, VirErr> {
    let exp_new = |e: ExpX| Ok(SpannedTyped::new(&exp.span, &exp.typ, e));
    let ok = Ok(exp.clone());
    use ExpX::*;
    match &exp.x {
        Const(_) => ok,
        Var(id) => match env.get(id) {
            None => ok,
            Some(e) => Ok(e.clone()),
        },
        Unary(op, e) => {
            use Constant::*;
            use UnaryOp::*;
            match &e.x {
                Const(Bool(b)) =>
                // Explicitly enumerate UnaryOps, in case more are added
                {
                    match op {
                        Not => exp_new(Const(Bool(!b))),
                        BitNot | Clip(_) | Trigger(_) => ok,
                    }
                }
                Const(Int(i)) =>
                // Explicitly enumerate UnaryOps, in case more are added
                {
                    match op {
                        BitNot => exp_new(Const(Int(!i))),
                        Clip(range) => {
                            let apply_range = |lower: BigInt, upper: BigInt| {
                                if i <= &lower {
                                    exp_new(Const(Int(lower)))
                                } else if i >= &upper {
                                    exp_new(Const(Int(upper)))
                                } else {
                                    Ok(exp.clone())
                                }
                            };
                            match range {
                                IntRange::Int => ok,
                                IntRange::Nat => apply_range(BigInt::zero(), i.clone()),
                                IntRange::U(n) => apply_range(
                                    BigInt::zero(),
                                    (BigInt::one() << n) - BigInt::one(),
                                ),
                                IntRange::I(n) => apply_range(
                                    BigInt::one() << (n - 1),
                                    (BigInt::one() << (n - 1)) - BigInt::one(),
                                ),
                                IntRange::USize => {
                                    apply_range(BigInt::from(usize::MIN), BigInt::from(usize::MAX))
                                }
                                IntRange::ISize => {
                                    apply_range(BigInt::from(isize::MIN), BigInt::from(isize::MAX))
                                }
                            }
                        }
                        Not | Trigger(_) => ok,
                    }
                }
                _ => ok,
            }
        }
        UnaryOpr(op, e1) => {
            use crate::ast::UnaryOpr::*;
            match op {
                Box(_) => Ok(e1.clone()),
                Unbox(_) => Ok(e1.clone()),
                HasType(_) => Ok(e1.clone()),
                IsVariant { datatype, variant } => match &e1.x {
                    Ctor(dt, var, _) => {
                        exp_new(Const(Constant::Bool(dt == datatype && var == variant)))
                    }
                    _ => ok,
                },
                TupleField { .. } => panic!("TupleField should have been removed by ast_simplify!"),
                Field(f) => match &e1.x {
                    Ctor(_dt, var, binders) => match binders.iter().position(|b| b.name == f.field)
                    {
                        None => ok,
                        Some(i) => Ok(binders.get(i).unwrap().a.clone()),
                    },
                    _ => ok,
                },
            }
        }
        Binary(op, e1, e2) => {
            use BinaryOp::*;
            use Constant::*;
            match op {
                And => match (&e1.x, &e2.x) {
                    (Const(Bool(true)), _) => Ok(e2.clone()),
                    (Const(Bool(false)), _) => exp_new(Const(Bool(false))),
                    (_, Const(Bool(true))) => Ok(e1.clone()),
                    (_, Const(Bool(false))) => exp_new(Const(Bool(false))),
                    _ => ok,
                },
                Or => match (&e1.x, &e2.x) {
                    (Const(Bool(true)), _) => exp_new(Const(Bool(true))),
                    (Const(Bool(false)), _) => Ok(e2.clone()),
                    (_, Const(Bool(true))) => exp_new(Const(Bool(true))),
                    (_, Const(Bool(false))) => Ok(e1.clone()),
                    _ => ok,
                },
                Xor => match (&e1.x, &e2.x) {
                    (Const(Bool(b1)), Const(Bool(b2))) => {
                        let r = (*b1 && !b2) || (!b1 && *b2);
                        exp_new(Const(Bool(r)))
                    }
                    (Const(Bool(true)), _) => exp_new(Unary(UnaryOp::Not, e2.clone())),
                    (Const(Bool(false)), _) => Ok(e2.clone()),
                    (_, Const(Bool(true))) => exp_new(Unary(UnaryOp::Not, e1.clone())),
                    (_, Const(Bool(false))) => Ok(e1.clone()),
                    _ => ok,
                },
                Implies => match (&e1.x, &e2.x) {
                    (Const(Bool(b1)), Const(Bool(b2))) => {
                        let r = !b1 || *b2;
                        exp_new(Const(Bool(r)))
                    }
                    (Const(Bool(true)), _) => Ok(e2.clone()),
                    (Const(Bool(false)), _) => exp_new(Const(Bool(true))),
                    (_, Const(Bool(true))) => exp_new(Const(Bool(true))),
                    (_, Const(Bool(false))) => exp_new(Unary(UnaryOp::Not, e1.clone())),
                    _ => ok,
                },
                Eq(_mode) => ok, // TODO: Implement a syntactic check for equality
                Ne => match (&e1.x, &e2.x) {
                    (Const(c1), Const(c2)) => exp_new(Const(Bool(c1 != c2))),
                    _ => ok, // In the presence of free variables, this is not the same as !Eq
                },
                Inequality(op) => match (&e1.x, &e2.x) {
                    (Const(Int(i1)), Const(Int(i2))) => {
                        use InequalityOp::*;
                        let b = match op {
                            Le => i1 <= i2,
                            Ge => i1 >= i2,
                            Lt => i1 < i2,
                            Gt => i1 > i2,
                        };
                        exp_new(Const(Bool(b)))
                    }
                    _ => ok,
                },
                Arith(op, _mode) => {
                    use ArithOp::*;
                    match (&e1.x, &e2.x) {
                        // Ideal case where both sides are concrete
                        (Const(Int(i1)), Const(Int(i2))) => {
                            use ArithOp::*;
                            match op {
                                Add => exp_new(Const(Int(i1 + i2))),
                                Sub => exp_new(Const(Int(i1 - i2))),
                                Mul => exp_new(Const(Int(i1 * i2))),
                                EuclideanDiv => {
                                    if i2.is_zero() {
                                        err_string(
                                            &exp.span,
                                            "computation tried to divide by 0".to_string(),
                                        )
                                    } else {
                                        // Based on Dafny's C# implementation:
                                        // https://github.com/dafny-lang/dafny/blob/08744a797296897f4efd486083579e484f57b9dc/Source/DafnyRuntime/DafnyRuntime.cs#L1383
                                        use Sign::*;
                                        let r = match (i1.sign(), i2.sign()) {
                                            (Plus | NoSign, Plus | NoSign) => i1 / i2,
                                            (Plus | NoSign, Minus) => -(i1 / (-i2)),
                                            (Minus, Plus | NoSign) => {
                                                -(-i1 - BigInt::one() / i2) - BigInt::one()
                                            }
                                            (Minus, Minus) => ((-i1 - BigInt::one()) / (-i2)) + 1,
                                        };
                                        exp_new(Const(Int(r)))
                                    }
                                }
                                EuclideanMod => {
                                    if i2.is_zero() {
                                        err_string(
                                            &exp.span,
                                            "tried to compute a remainder with respect to 0"
                                                .to_string(),
                                        )
                                    } else {
                                        // Based on Dafny's C# implementation:
                                        // https://github.com/dafny-lang/dafny/blob/08744a797296897f4efd486083579e484f57b9dc/Source/DafnyRuntime/DafnyRuntime.cs#L1436
                                        use Sign::*;
                                        let r = match i1.sign() {
                                            Plus | NoSign => i1 / i2.abs(),
                                            Minus => {
                                                let c = (-i1) % i2.abs();
                                                if c.is_zero() {
                                                    BigInt::zero()
                                                } else {
                                                    i2.abs() - c
                                                }
                                            }
                                        };
                                        exp_new(Const(Int(r)))
                                    }
                                }
                            }
                        }
                        // Special cases for certain concrete values
                        (Const(Int(i1)), _) if i1.is_zero() && matches!(op, Add) => Ok(e2.clone()),
                        (Const(Int(i1)), _) if i1.is_zero() && matches!(op, Mul) => {
                            exp_new(Const(Int(BigInt::zero())))
                        }
                        (Const(Int(i1)), _) if i1.is_one() && matches!(op, Mul) => Ok(e2.clone()),
                        (_, Const(Int(i2))) if i2.is_zero() => {
                            use ArithOp::*;
                            match op {
                                Add | Sub => Ok(e1.clone()),
                                Mul => exp_new(Const(Int(BigInt::zero()))),
                                EuclideanDiv => err_string(
                                    &exp.span,
                                    "computation tried to divide by 0".to_string(),
                                ),
                                EuclideanMod => err_string(
                                    &exp.span,
                                    "tried to compute a remainder with respect to 0".to_string(),
                                ),
                            }
                        }
                        (_, Const(Int(i2)))
                            if i2.is_one() && matches!(op, Mul | EuclideanDiv | EuclideanMod) =>
                        {
                            Ok(e1.clone())
                        }
                        // TODO: Once we have Eq, add a case for Minus(x, x) == 0
                        _ => ok,
                    }
                }
                Bitwise(op) => {
                    use BitwiseOp::*;
                    match (&e1.x, &e2.x) {
                        // Ideal case where both sides are concrete
                        (Const(Int(i1)), Const(Int(i2))) => match op {
                            BitXor => exp_new(Const(Int(i1 ^ i2))),
                            BitAnd => exp_new(Const(Int(i1 & i2))),
                            BitOr => exp_new(Const(Int(i1 | i2))),
                            Shr => match i2.to_u128() {
                                None => ok,
                                Some(shift) => exp_new(Const(Int(i1 >> shift))),
                            },
                            Shl => match i2.to_u128() {
                                None => ok,
                                Some(shift) => exp_new(Const(Int(i1 << shift))),
                            },
                        },
                        // Special cases for certain concrete values
                        (Const(Int(i)), _) | (_, Const(Int(i)))
                            if i.is_zero() && matches!(op, BitAnd) =>
                        {
                            exp_new(Const(Int(BigInt::zero())))
                        }
                        (Const(Int(i1)), _) if i1.is_zero() && matches!(op, BitOr) => {
                            Ok(e2.clone())
                        }
                        (_, Const(Int(i2))) if i2.is_zero() && matches!(op, BitOr) => {
                            Ok(e1.clone())
                        }
                        // TODO: Add additional cases here if we implement syntactic Eq check
                        _ => ok,
                    }
                }
            }
        }
        If(e1, e2, e3) => match &e1.x {
            Const(Constant::Bool(b)) => {
                if *b {
                    Ok(e2.clone())
                } else {
                    Ok(e3.clone())
                }
            }
            _ => ok,
        },
        // TODO: Fill these in
        Call(x, typs, es) => ok,
        CallLambda(typ, e0, es) => ok,
        Bind(bnd, e1) => ok,

        // Ignored by the interpreter at present (i.e., treated as symbolic)
        VarAt(..) | VarLoc(..) | Loc(..) | Old(..) | Ctor(..) | WithTriggers(..) => ok,
    }
}

pub fn eval_expr(exp: &Exp) -> Result<Exp, VirErr> {
    let env = HashMap::new();
    let mut scope_map = ScopeMap::new();
    map_exp_visitor_bind(exp, &mut scope_map, &mut |e, m| eval_expr_internal(&env, e, m))
}
