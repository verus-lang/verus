//! A Symbolic Interpreter for VIR
//!
//! Operates on VIR's SST representation
//!
//! Current target is supporting proof by computation
//! https://github.com/secure-foundations/verus/discussions/120

use crate::ast::{
    ArithOp, BinaryOp, BitwiseOp, Constant, InequalityOp, IntRange, SpannedTyped, UnaryOp, VirErr,
};
use crate::ast_util::err_string;
use crate::def::SstMap;
use crate::sst::{BndX, Exp, ExpX, UniqueIdent};
use air::scope_map::ScopeMap;
use num_bigint::{BigInt, Sign};
use num_traits::identities::Zero;
use num_traits::{One, Signed, ToPrimitive};
use std::sync::Arc;

type Env = ScopeMap<UniqueIdent, Exp>;

// TODO: Add support for function evaluation memoization
// TODO: Bound the running time, based on rlimit

// Computes the syntactic equality of two expressions
// Some(b) means b is exp1 == exp2
// None means we can't tell
/*
fn equal_exprs(left: &Exp, right: &Exp) -> Option<bool> {
    use ExpX::*;
    match (&left.x, &right.x) {
        (Const(l), Const(r)) => Some(l == r),
        (Var(l), Var(r)) => if l == r { Some(true) } else { None },
        (Unary(op_l, e_l), Unary(op_r, e_r)) => Some(op_l == op_r && equal_exprs(e_l, e_r)?),
        (UnaryOpr(op_l, e_l), UnaryOpr(op_r, e_r)) => Some(op_l == op_r && equal_exprs(e_l, e_r)?),
        (Binary(op_l, e1_l, e2_l), Binary(op_r, e1_r, e2_r)) => Some(op_l == op_r && equal_exprs(e1_l, e1_r)? && equal_exprs(e2_l, e2_r)?),
        (If(e1_l, e2_l, e3_l), If(e1_r, e2_r, e3_r)) =>
            equal_exprs(e1_l, e1_r)? && equal_exprs(e2_l, e2_r)? && equal_exprs(e3_l, e3_r)?,
        (Call(f_l, _, exps_l), Call(f_r, _, exps_r)) => {
            if f_l == f_r && exps_l.len() == exps_r.len() {
                let eq = exps_l.iter().zip(exps_r.iter()).fold(true, |b, |(e_l, r_r)| b && equal_exprs(e_l, e_r))


            }
        }

    }
}
*/

fn eval_expr_internal(env: &mut Env, fun_ssts: &SstMap, exp: &Exp) -> Result<Exp, VirErr> {
    let exp_new = |e: ExpX| Ok(SpannedTyped::new(&exp.span, &exp.typ, e));
    let ok = Ok(exp.clone());
    use ExpX::*;
    match &exp.x {
        Const(_) => ok,
        Var(id) => {
            println!("Looking up {:?} in {:?}", id, env.map());
            match env.get(id) {
            None => ok,
            Some(e) => { println!("\tGot {:?}", e); Ok(e.clone()) },
        }},
        Unary(op, e) => {
            use Constant::*;
            use UnaryOp::*;
            let e = eval_expr_internal(env, fun_ssts, e)?;
            let ok = exp_new(Unary(*op, e.clone()));
            match &e.x {
                Const(Bool(b)) => {
                    // Explicitly enumerate UnaryOps, in case more are added
                    match op {
                        Not => exp_new(Const(Bool(!b))),
                        BitNot | Clip(_) | Trigger(_) => ok,
                    }
                }
                Const(Int(i)) => {
                    // Explicitly enumerate UnaryOps, in case more are added
                    match op {
                        BitNot => exp_new(Const(Int(!i))),
                        Clip(range) => {
                            let apply_range = |lower: BigInt, upper: BigInt| {
                                if i <= &lower {
                                    exp_new(Const(Int(lower)))
                                } else if i >= &upper {
                                    exp_new(Const(Int(upper)))
                                } else {
                                    Ok(e.clone())
                                }
                            };
                            match range {
                                IntRange::Int => ok,
                                IntRange::Nat => apply_range(BigInt::zero(), i.clone()),
                                IntRange::U(n) => {
                                    let u = apply_range(
                                        BigInt::zero(),
                                        (BigInt::one() << n) - BigInt::one(),
                                    );
                                    u
                                }
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
        UnaryOpr(op, e) => {
            let e = eval_expr_internal(env, fun_ssts, e)?;
            let ok = exp_new(UnaryOpr(op.clone(), e.clone()));
            use crate::ast::UnaryOpr::*;
            match op {
                Box(_) => ok,
                Unbox(_) => match &e.x {
                    UnaryOpr(Box(_), inner_e) => Ok(inner_e.clone()),
                    _ => ok,
                },
                HasType(_) => ok,
                IsVariant { datatype, variant } => match &e.x {
                    Ctor(dt, var, _) => {
                        exp_new(Const(Constant::Bool(dt == datatype && var == variant)))
                    }
                    _ => ok,
                },
                TupleField { .. } => panic!("TupleField should have been removed by ast_simplify!"),
                Field(f) => match &e.x {
                    Ctor(_dt, _var, binders) => {
                        match binders.iter().position(|b| b.name == f.field) {
                            None => ok,
                            Some(i) => Ok(binders.get(i).unwrap().a.clone()),
                        }
                    }
                    _ => ok,
                },
            }
        }
        Binary(op, e1, e2) => {
            use BinaryOp::*;
            use Constant::*;
            let e1 = eval_expr_internal(env, fun_ssts, e1)?;
            let e2 = eval_expr_internal(env, fun_ssts, e2)?;
            let ok = exp_new(Binary(*op, e1.clone(), e2.clone()));
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
        If(e1, e2, e3) => {
            let e1 = eval_expr_internal(env, fun_ssts, e1)?;
            let e2 = eval_expr_internal(env, fun_ssts, e2)?;
            let e3 = eval_expr_internal(env, fun_ssts, e3)?;
            match &e1.x {
                Const(Constant::Bool(b)) => {
                    if *b {
                        Ok(e2.clone())
                    } else {
                        Ok(e3.clone())
                    }
                }
                _ => exp_new(If(e1, e2, e3)),
            }
        }
        Call(fun, typs, exps) => {
            let new_exps: Result<Vec<Exp>, VirErr> = exps.iter().map(|e| eval_expr_internal(env, fun_ssts, e)).collect();
            let new_exps = new_exps?;
            match fun_ssts.get(fun) {
                None => { 
                    println!("Failed to find func {:?} in {:?}", fun, fun_ssts); 
                    exp_new(Call(fun.clone(), typs.clone(), Arc::new(new_exps)))},
                Some((params, body)) => {
                    println!("Found func!");
                    env.push_scope(true);
                    for (formal, actual) in params.iter().zip(new_exps) {
                        env.insert((formal.x.name.clone(), Some(0)), actual.clone()).unwrap();
                    }
                    let e = eval_expr_internal(env, fun_ssts, body);
                    env.pop_scope();
                    e
                },
            }
        },
        // TODO: Fill this in
        CallLambda(_typ, _e0, _es) => ok,
        Bind(bnd, e) => match &bnd.x {
            BndX::Let(bnds) => {
                env.push_scope(true);
                for b in bnds.iter() {
                    env.insert((b.name.clone(), Some(0)), b.a.clone()).unwrap();
                }
                let e = eval_expr_internal(env, fun_ssts, e);
                env.pop_scope();
                e
            },
            _ => ok,
        },
        // Ignored by the interpreter at present (i.e., treated as symbolic)
        VarAt(..) | VarLoc(..) | Loc(..) | Old(..) | Ctor(..) | WithTriggers(..) => ok,
    }
}

pub fn eval_expr(exp: &Exp, fun_ssts: &SstMap) -> Result<Exp, VirErr> {
    let mut env = ScopeMap::new();
    println!("Starting with fun_ssts = {:?}", fun_ssts);
    eval_expr_internal(&mut env, fun_ssts, exp)
}
