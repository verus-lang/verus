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

struct State {
    depth: usize,
    env: Env,
    debug: bool,
}

// TODO: Add support for function evaluation memoization
// TODO: Bound the running time, based on rlimit
// TODO: Swap to CPS with enforced tail-call optimization to avoid exhausting the stack

// Computes the syntactic equality of two expressions
// Some(b) means b is exp1 == exp2
// None means we can't tell
// We expect to only call this after eval_expr has been called on both expressions
fn equal_exprs(left: &Exp, right: &Exp) -> Option<bool> {
    use ExpX::*;
    match (&left.x, &right.x) {
        (Const(l), Const(r)) => Some(l == r),
        (Var(l), Var(r)) => {
            if l == r {
                Some(true)
            } else {
                // These are free variables, so we can't know for sure
                // if they are equal (applies to cases below, too)
                None
            }
        }
        (VarLoc(l), VarLoc(r)) => {
            if l == r {
                Some(true)
            } else {
                None
            }
        }
        (VarAt(l, at_l), VarAt(r, at_r)) => {
            if l == r && at_l == at_r {
                Some(true)
            } else {
                None
            }
        }
        (Loc(l), Loc(r)) => equal_exprs(l, r),
        (Old(id_l, unique_id_l), Old(id_r, unique_id_r)) => {
            if id_l == id_r && unique_id_l == unique_id_r { Some(true) } else { None }
        }
        (Call(f_l, _, exps_l), Call(f_r, _, exps_r)) => {
            if f_l == f_r && exps_l.len() == exps_r.len() {
                let eq: Option<bool> = exps_l
                    .iter()
                    .zip(exps_r.iter())
                    .fold(Some(true), |b, (e_l, e_r)| Some(b? && equal_exprs(e_l, e_r)?));
                eq
            } else {
                None
            }
        }
        (CallLambda(..), CallLambda(..)) => None, // TODO: Can we do better here?
        (Ctor(path_l, id_l, bnds_l), Ctor(path_r, id_r, bnds_r)) => {
            if path_l != path_r || id_l != id_r {
                Some(false)
            } else {
                let eq: Option<bool> =
                    bnds_l.iter().zip(bnds_r.iter()).fold(Some(true), |b, (bnd_l, bnd_r)| {
                        Some(b? && bnd_l.name == bnd_r.name && equal_exprs(&bnd_l.a, &bnd_r.a)?)
                    });
                eq
            }
        }
        (Unary(op_l, e_l), Unary(op_r, e_r)) => Some(op_l == op_r && equal_exprs(e_l, e_r)?),
        (UnaryOpr(op_l, e_l), UnaryOpr(op_r, e_r)) => {
            use crate::ast::UnaryOpr::*;
            let op_eq = match (op_l, op_r) {
                // Safe to ignore types on these?
                (Box(_), Box(_)) => true,
                (Unbox(_), Unbox(_)) => true,
                (HasType(_), HasType(_)) => true,
                (
                    IsVariant { datatype: dt_l, variant: var_l },
                    IsVariant { datatype: dt_r, variant: var_r },
                ) => dt_l == dt_r && var_l == var_r,
                (TupleField { .. }, TupleField { .. }) => {
                    panic!("TupleField should have been removed by ast_simplify!")
                }
                (Field(l), Field(r)) => l == r,
                _ => false,
            };
            Some(op_eq && equal_exprs(e_l, e_r)?)
        }
        (Binary(op_l, e1_l, e2_l), Binary(op_r, e1_r, e2_r)) => {
            Some(op_l == op_r && equal_exprs(e1_l, e1_r)? && equal_exprs(e2_l, e2_r)?)
        }
        (If(e1_l, e2_l, e3_l), If(e1_r, e2_r, e3_r)) => {
            Some(equal_exprs(e1_l, e1_r)? && equal_exprs(e2_l, e2_r)? && equal_exprs(e3_l, e3_r)?)
        }
        (WithTriggers(_trigs_l, e_l), WithTriggers(_trigs_r, e_r)) => equal_exprs(e_l, e_r),
        (Bind(bnd_l, e_l), Bind(bnd_r, e_r)) => None, // TODO: Deep comparison?
        _ => None,
    }
}

fn definitely_equal(left: &Exp, right: &Exp) -> bool {
    match equal_exprs(left, right) {
        None => false,
        Some(b) => b,
    }
}

/// Symbolically execute the expression as far as we can,
/// stopping when we hit a symbolic control-flow decision
fn eval_expr_internal(state: &mut State, fun_ssts: &SstMap, exp: &Exp) -> Result<Exp, VirErr> {
    if state.debug {
        println!("{}Evaluating {:?}", "\t".repeat(state.depth), exp.x);
    }
    state.depth += 1;
    let exp_new = |e: ExpX| Ok(SpannedTyped::new(&exp.span, &exp.typ, e));
    let bool_new = |b: bool| Ok(SpannedTyped::new(&exp.span, &exp.typ, Const(Constant::Bool(b))));
    let int_new = |i: BigInt| Ok(SpannedTyped::new(&exp.span, &exp.typ, Const(Constant::Int(i))));
    let zero = Ok(SpannedTyped::new(&exp.span, &exp.typ, Const(Constant::Int(BigInt::zero()))));
    let ok = Ok(exp.clone());
    use ExpX::*;
    let r = match &exp.x {
        Const(_) => ok,
        Var(id) => match state.env.get(id) {
            None => {
                if state.debug {
                    println!("Failed to find a match for {:?}", id);
                };
                ok
            }
            Some(e) => {
                if state.debug {
                    println!("Found match for {:?}", id);
                };
                Ok(e.clone())
            }
        },
        Unary(op, e) => {
            use Constant::*;
            use UnaryOp::*;
            let e = eval_expr_internal(state, fun_ssts, e)?;
            let ok = exp_new(Unary(*op, e.clone()));
            match &e.x {
                Const(Bool(b)) => {
                    // Explicitly enumerate UnaryOps, in case more are added
                    match op {
                        Not => bool_new(!b),
                        BitNot | Clip(_) | Trigger(_) => ok,
                    }
                }
                Const(Int(i)) => {
                    // Explicitly enumerate UnaryOps, in case more are added
                    match op {
                        BitNot => int_new(!i),
                        Clip(range) => {
                            let apply_range = |lower: BigInt, upper: BigInt| {
                                if i <= &lower {
                                    int_new(lower)
                                } else if i >= &upper {
                                    int_new(upper)
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
            let e = eval_expr_internal(state, fun_ssts, e)?;
            let ok = exp_new(UnaryOpr(op.clone(), e.clone()));
            use crate::ast::UnaryOpr::*;
            match op {
                Box(_) => ok,
                Unbox(_) => match &e.x {
                    UnaryOpr(Box(_), inner_e) => {
                        if state.debug {
                            println!("Unbox found matching box");
                        };
                        Ok(inner_e.clone())
                    }
                    _ => ok,
                },
                HasType(_) => ok,
                IsVariant { datatype, variant } => match &e.x {
                    Ctor(dt, var, _) => {
                        if state.debug {
                            println!("IsVariant found matching Ctor!");
                        };
                        bool_new(dt == datatype && var == variant)
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
            // We initially evaluate only e1, since op may short circuit
            // e.g., x != 0 && y == 5 / x
            let e1 = eval_expr_internal(state, fun_ssts, e1)?;
            let ok_e2 = |e2: Exp| exp_new(Binary(*op, e1.clone(), e2.clone()));
            match op {
                And => match &e1.x {
                    Const(Bool(true)) => eval_expr_internal(state, fun_ssts, e2),
                    Const(Bool(false)) => bool_new(false),
                    _ => {
                        let e2 = eval_expr_internal(state, fun_ssts, e2)?;
                        match &e2.x {
                            Const(Bool(true)) => Ok(e1.clone()),
                            Const(Bool(false)) => bool_new(false),
                            _ => ok_e2(e2),
                        }
                    }
                },
                Or => match &e1.x {
                    Const(Bool(true)) => bool_new(true),
                    Const(Bool(false)) => eval_expr_internal(state, fun_ssts, e2),
                    _ => {
                        let e2 = eval_expr_internal(state, fun_ssts, e2)?;
                        match &e2.x {
                            Const(Bool(true)) => bool_new(true),
                            Const(Bool(false)) => Ok(e1.clone()),
                            _ => ok_e2(e2),
                        }
                    }
                },
                Xor => {
                    let e2 = eval_expr_internal(state, fun_ssts, e2)?;
                    match (&e1.x, &e2.x) {
                        (Const(Bool(b1)), Const(Bool(b2))) => {
                            let r = (*b1 && !b2) || (!b1 && *b2);
                            bool_new(r)
                        }
                        (Const(Bool(true)), _) => exp_new(Unary(UnaryOp::Not, e2.clone())),
                        (Const(Bool(false)), _) => Ok(e2.clone()),
                        (_, Const(Bool(true))) => exp_new(Unary(UnaryOp::Not, e1.clone())),
                        (_, Const(Bool(false))) => Ok(e1.clone()),
                        _ => ok_e2(e2),
                    }
                }
                // TODO: Does Implies short-circuit?
                Implies => {
                    let e2 = eval_expr_internal(state, fun_ssts, e2)?;
                    match (&e1.x, &e2.x) {
                        (Const(Bool(b1)), Const(Bool(b2))) => {
                            let r = !b1 || *b2;
                            bool_new(r)
                        }
                        (Const(Bool(true)), _) => Ok(e2.clone()),
                        (Const(Bool(false)), _) => bool_new(true),
                        (_, Const(Bool(true))) => bool_new(true),
                        (_, Const(Bool(false))) => exp_new(Unary(UnaryOp::Not, e1.clone())),
                        _ => ok_e2(e2),
                    }
                }
                Eq(_mode) => {
                    let e2 = eval_expr_internal(state, fun_ssts, e2)?;
                    match equal_exprs(&e1, &e2) {
                        None => ok_e2(e2),
                        Some(b) => bool_new(b),
                    }
                }
                Ne => {
                    let e2 = eval_expr_internal(state, fun_ssts, e2)?;
                    match equal_exprs(&e1, &e2) {
                        None => ok_e2(e2),
                        Some(b) => bool_new(!b),
                    }
                }
                Inequality(op) => {
                    let e2 = eval_expr_internal(state, fun_ssts, e2)?;
                    match (&e1.x, &e2.x) {
                        (Const(Int(i1)), Const(Int(i2))) => {
                            use InequalityOp::*;
                            let b = match op {
                                Le => i1 <= i2,
                                Ge => i1 >= i2,
                                Lt => i1 < i2,
                                Gt => i1 > i2,
                            };
                            bool_new(b)
                        }
                        _ => ok_e2(e2),
                    }
                }
                Arith(op, _mode) => {
                    let e2 = eval_expr_internal(state, fun_ssts, e2)?;
                    use ArithOp::*;
                    match (&e1.x, &e2.x) {
                        // Ideal case where both sides are concrete
                        (Const(Int(i1)), Const(Int(i2))) => {
                            use ArithOp::*;
                            match op {
                                Add => int_new(i1 + i2),
                                Sub => int_new(i1 - i2),
                                Mul => int_new(i1 * i2),
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
                                        int_new(r)
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
                                        int_new(r)
                                    }
                                }
                            }
                        }
                        // Special cases for certain concrete values
                        (Const(Int(i1)), _) if i1.is_zero() && matches!(op, Add) => Ok(e2.clone()),
                        (Const(Int(i1)), _) if i1.is_zero() && matches!(op, Mul) => zero,
                        (Const(Int(i1)), _) if i1.is_one() && matches!(op, Mul) => Ok(e2.clone()),
                        (_, Const(Int(i2))) if i2.is_zero() => {
                            use ArithOp::*;
                            match op {
                                Add | Sub => Ok(e1.clone()),
                                Mul => zero,
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
                        _ => {
                            match op {
                                // X - X => 0
                                ArithOp::Sub if definitely_equal(&e1, &e2) => zero,
                                _ => ok_e2(e2),
                            }
                        }
                    }
                }
                Bitwise(op) => {
                    use BitwiseOp::*;
                    let e2 = eval_expr_internal(state, fun_ssts, e2)?;
                    match (&e1.x, &e2.x) {
                        // Ideal case where both sides are concrete
                        (Const(Int(i1)), Const(Int(i2))) => match op {
                            BitXor => int_new(i1 ^ i2),
                            BitAnd => int_new(i1 & i2),
                            BitOr => int_new(i1 | i2),
                            Shr => match i2.to_u128() {
                                None => ok_e2(e2),
                                Some(shift) => int_new(i1 >> shift),
                            },
                            Shl => match i2.to_u128() {
                                None => ok_e2(e2),
                                Some(shift) => int_new(i1 << shift),
                            },
                        },
                        // Special cases for certain concrete values
                        (Const(Int(i)), _) | (_, Const(Int(i)))
                            if i.is_zero() && matches!(op, BitAnd) =>
                        {
                            zero
                        }
                        (Const(Int(i1)), _) if i1.is_zero() && matches!(op, BitOr) => {
                            Ok(e2.clone())
                        }
                        (_, Const(Int(i2))) if i2.is_zero() && matches!(op, BitOr) => {
                            Ok(e1.clone())
                        }
                        _ => {
                            match op {
                                // X ^ X => 0
                                BitXor if definitely_equal(&e1, &e2) => zero,
                                // X & X = X, X | X = X
                                BitAnd | BitOr if definitely_equal(&e1, &e2) => Ok(e1.clone()),
                                _ => ok_e2(e2),
                            }
                        }
                    }
                }
            }
        }
        If(e1, e2, e3) => {
            let e1 = eval_expr_internal(state, fun_ssts, e1)?;
            match &e1.x {
                Const(Constant::Bool(b)) => {
                    if *b {
                        eval_expr_internal(state, fun_ssts, e2)
                    } else {
                        eval_expr_internal(state, fun_ssts, e3)
                    }
                }
                _ => exp_new(If(e1, e2.clone(), e3.clone())),
            }
        }
        Call(fun, typs, exps) => {
            let new_exps: Result<Vec<Exp>, VirErr> =
                exps.iter().map(|e| eval_expr_internal(state, fun_ssts, e)).collect();
            let new_exps = new_exps?;
            match fun_ssts.get(fun) {
                None => exp_new(Call(fun.clone(), typs.clone(), Arc::new(new_exps))),
                Some((params, body)) => {
                    state.env.push_scope(true);
                    for (formal, actual) in params.iter().zip(new_exps) {
                        if state.debug {
                            println!("Binding {:?} to {:?}", formal, actual.x);
                        }
                        state.env.insert((formal.x.name.clone(), Some(0)), actual.clone()).unwrap();
                    }
                    let e = eval_expr_internal(state, fun_ssts, body);
                    state.env.pop_scope();
                    e
                }
            }
        }
        // TODO: Fill this in
        CallLambda(_typ, _e0, _es) => ok,
        Bind(bnd, e) => match &bnd.x {
            BndX::Let(bnds) => {
                state.env.push_scope(true);
                for b in bnds.iter() {
                    let val = eval_expr_internal(state, fun_ssts, &b.a)?;
                    state.env.insert((b.name.clone(), None), val).unwrap();
                }
                let e = eval_expr_internal(state, fun_ssts, e);
                state.env.pop_scope();
                e
            }
            _ => ok,
        },
        // Ignored by the interpreter at present (i.e., treated as symbolic)
        VarAt(..) | VarLoc(..) | Loc(..) | Old(..) | Ctor(..) | WithTriggers(..) => ok,
    };
    let res = r?;
    state.depth -= 1;
    if state.debug {
        println!("{}=> {:?}", "\t".repeat(state.depth), &res.x);
    }
    Ok(res)
}

pub fn eval_expr(exp: &Exp, fun_ssts: &SstMap) -> Result<Exp, VirErr> {
    let env = ScopeMap::new();
    let mut state = State { depth: 0, env, debug: true };
    eval_expr_internal(&mut state, fun_ssts, exp)
}
