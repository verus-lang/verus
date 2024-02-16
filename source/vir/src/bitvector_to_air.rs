use crate::ast::{
    ArithOp, BinaryOp, BitwiseOp, InequalityOp, IntRange, Typ, TypX, UnaryOp, UnaryOpr, VirErr,
};
use crate::ast_util::{
    allowed_bitvector_type, bitwidth_from_int_range, bitwidth_from_type, is_integer_type,
    undecorate_typ, IntegerTypeBitwidth,
};
use crate::context::Ctx;
use crate::def::suffix_local_expr_id;
use crate::def::suffix_local_unique_id;
use crate::messages::{error, Span};
use crate::sst::{BndX, Exp, ExpX};
use crate::util::vec_map_result;
use air::ast::{Binder, BinderX, Constant, Expr, ExprX};
use air::ast_util::{bool_typ, bv_typ, mk_and, mk_ite, mk_or, str_typ, string_var};
use std::sync::Arc;

#[derive(Debug, Clone)]
pub(crate) struct BvExprCtxt {
    pub bit_vector_typ_hint: Option<Typ>,
}

impl BvExprCtxt {
    pub(crate) fn new() -> Self {
        BvExprCtxt { bit_vector_typ_hint: None }
    }
    pub(crate) fn set_bit_vector_typ_hint(&self, bit_vector_typ_hint: Option<Typ>) -> Self {
        BvExprCtxt { bit_vector_typ_hint }
    }
}

pub(crate) fn bv_exp_to_expr(ctx: &Ctx, exp: &Exp, expr_ctxt: &BvExprCtxt) -> Result<Expr, VirErr> {
    let bit_vector_typ_hint = &expr_ctxt.bit_vector_typ_hint;
    let expr_ctxt = &expr_ctxt.set_bit_vector_typ_hint(None);
    let result = match &exp.x {
        ExpX::Const(crate::ast::Constant::Int(i)) => {
            let typ = match (&*undecorate_typ(&exp.typ), bit_vector_typ_hint) {
                (TypX::Int(IntRange::Int | IntRange::Nat), Some(hint))
                    if crate::ast_util::fixed_integer_const(&i.to_string(), hint) =>
                {
                    hint
                }
                _ => &exp.typ,
            };
            let width = bitwidth_from_type(typ);
            let width = bitvector_expect_exact(ctx, &exp.span, typ, &width)?;
            Arc::new(ExprX::Const(Constant::BitVec(Arc::new(i.to_string()), width)))
        }
        ExpX::Const(c) => {
            let expr = crate::sst_to_air::constant_to_expr(ctx, c);
            expr
        }
        ExpX::Var(x) => {
            if is_integer_type(&exp.typ) {
                // error if either:
                //  - it's an infinite width type
                //  - it's usize or isize and the arch-size is not specified
                // (TODO allow the second one)
                let width = bitwidth_from_type(&exp.typ);
                bitvector_expect_exact(ctx, &exp.span, &exp.typ, &width)?;
            } else {
                if allowed_bitvector_type(&exp.typ) {
                    // ok
                } else {
                    return Err(error(
                        &exp.span,
                        format!(
                            "error: bit_vector prover cannot handle this type (bit_vector can only handle variables of type `bool` or of fixed-width integers)"
                        ),
                    ));
                }
            }

            string_var(&suffix_local_unique_id(x))
        }
        ExpX::Unary(op, arg) => {
            if !allowed_bitvector_type(&arg.typ) {
                return Err(error(
                    &arg.span,
                    format!("error: cannot use bit-vector arithmetic on type {:?}", arg.typ),
                ));
            }
            let hint = match op {
                UnaryOp::BitNot => expr_ctxt.bit_vector_typ_hint.clone(),
                UnaryOp::Clip {
                    range: range @ (IntRange::U(..) | IntRange::I(..)),
                    truncate: _,
                } => Some(Arc::new(TypX::Int(*range))),
                _ => None,
            };
            let expr_ctxt = &expr_ctxt.set_bit_vector_typ_hint(hint);
            let bv_e = bv_exp_to_expr(ctx, arg, expr_ctxt)?;
            match op {
                UnaryOp::Not => {
                    let bop = air::ast::UnaryOp::Not;
                    return Ok(Arc::new(ExprX::Unary(bop, bv_e)));
                }
                UnaryOp::BitNot => {
                    let bop = air::ast::UnaryOp::BitNot;
                    return Ok(Arc::new(ExprX::Unary(bop, bv_e)));
                }
                // bitvector type casting by 'as' keyword
                // via converting Clip into concat/extract
                UnaryOp::Clip { range: int_range, .. } => {
                    let new_n = bitwidth_from_int_range(int_range);
                    let old_n = bitwidth_from_type(&arg.typ);

                    let new_n = bitvector_expect_exact(ctx, &arg.span, &exp.typ, &new_n)?;
                    let old_n = bitvector_expect_exact(ctx, &arg.span, &arg.typ, &old_n)?;

                    if new_n > old_n {
                        return Ok(zero_extend(&bv_e, new_n - old_n));
                    }
                    // extract lower new_n bits
                    else if new_n < old_n {
                        let op = air::ast::UnaryOp::BitExtract(new_n - 1, 0);
                        return Ok(Arc::new(ExprX::Unary(op, bv_e)));
                    } else {
                        return Ok(bv_e);
                    }
                }
                UnaryOp::HeightTrigger => panic!("internal error: unexpected HeightTrigger"),
                UnaryOp::Trigger(_) => bv_exp_to_expr(ctx, arg, expr_ctxt)?,
                UnaryOp::CoerceMode { .. } => {
                    panic!("internal error: TupleField should have been removed before here")
                }
                UnaryOp::MustBeFinalized => {
                    panic!("internal error: Exp not finalized: {:?}", arg)
                }
                UnaryOp::StrLen | UnaryOp::StrIsAscii | UnaryOp::CharToInt => panic!(
                    "internal error: matching for bit vector ops on this match should be impossible"
                ),
                UnaryOp::InferSpecForLoopIter { .. } => {
                    panic!("internal error: unexpected Option type (from InferSpecForLoopIter)")
                }
            }
        }
        ExpX::UnaryOpr(UnaryOpr::Box(_) | UnaryOpr::Unbox(_), exp) => {
            bv_exp_to_expr(ctx, exp, expr_ctxt)?
        }
        ExpX::Binary(op, lhs, rhs) => {
            if !allowed_bitvector_type(&exp.typ) {
                return Err(error(
                    &exp.span,
                    format!("error: cannot use bit-vector arithmetic on type {:?}", exp.typ),
                ));
            }
            if let BinaryOp::HeightCompare { .. } = op {
                return Err(error(
                    &exp.span,
                    format!("error: cannot use bit-vector arithmetic on is_smaller_than"),
                ));
            }
            // disallow signed integer from bitvec reasoning. However, allow that for shift
            // TODO: sanity check for shift
            let _ = match op {
                BinaryOp::Bitwise(BitwiseOp::Shl | BitwiseOp::Shr, _) => (),
                _ => {
                    check_unsigned(&lhs)?;
                    check_unsigned(&rhs)?;
                }
            };
            let hint = match op {
                BinaryOp::Eq(..)
                | BinaryOp::Ne
                | BinaryOp::Inequality(..)
                | BinaryOp::Arith(..) => {
                    match (&*undecorate_typ(&lhs.typ), &*undecorate_typ(&rhs.typ)) {
                        (TypX::Int(IntRange::U(..) | IntRange::I(..)), _) => Some(lhs.typ.clone()),
                        (_, TypX::Int(IntRange::U(..) | IntRange::I(..))) => Some(rhs.typ.clone()),
                        _ => None,
                    }
                }
                _ => None,
            };
            let expr_ctxt = &expr_ctxt.set_bit_vector_typ_hint(hint);
            let lh = bv_exp_to_expr(ctx, lhs, expr_ctxt)?;
            let rh = bv_exp_to_expr(ctx, rhs, expr_ctxt)?;

            let (lh, rh) = if matches!(op, BinaryOp::Inequality(..)) {
                zero_extend_smaller_one_to_same_bitwidth(ctx, &lh, lhs, &rh, rhs)?
            } else {
                (lh, rh)
            };

            let _ = match op {
                BinaryOp::And => return Ok(mk_and(&vec![lh, rh])),
                BinaryOp::Or => return Ok(mk_or(&vec![lh, rh])),
                BinaryOp::Ne => {
                    let eq = ExprX::Binary(air::ast::BinaryOp::Eq, lh, rh);
                    return Ok(Arc::new(ExprX::Unary(air::ast::UnaryOp::Not, Arc::new(eq))));
                }
                _ => (),
            };
            let bop = match op {
                BinaryOp::HeightCompare { .. } => unreachable!(),
                BinaryOp::Eq(_) => air::ast::BinaryOp::Eq,
                BinaryOp::Ne => unreachable!(),
                BinaryOp::Arith(ArithOp::Add, _) => air::ast::BinaryOp::BitAdd,
                BinaryOp::Arith(ArithOp::Sub, _) => air::ast::BinaryOp::BitSub,
                BinaryOp::Arith(ArithOp::Mul, _) => air::ast::BinaryOp::BitMul,
                BinaryOp::Arith(ArithOp::EuclideanDiv, _) => air::ast::BinaryOp::BitUDiv,
                BinaryOp::Arith(ArithOp::EuclideanMod, _) => air::ast::BinaryOp::BitUMod,
                BinaryOp::Inequality(InequalityOp::Le) => air::ast::BinaryOp::BitULe,
                BinaryOp::Inequality(InequalityOp::Lt) => air::ast::BinaryOp::BitULt,
                BinaryOp::Inequality(InequalityOp::Ge) => air::ast::BinaryOp::BitUGe,
                BinaryOp::Inequality(InequalityOp::Gt) => air::ast::BinaryOp::BitUGt,
                BinaryOp::Bitwise(BitwiseOp::BitXor, _) => air::ast::BinaryOp::BitXor,
                BinaryOp::Bitwise(BitwiseOp::BitAnd, _) => air::ast::BinaryOp::BitAnd,
                BinaryOp::Bitwise(BitwiseOp::BitOr, _) => air::ast::BinaryOp::BitOr,
                BinaryOp::Bitwise(BitwiseOp::Shl, _) => air::ast::BinaryOp::Shl,
                BinaryOp::Bitwise(BitwiseOp::Shr, _) => air::ast::BinaryOp::LShr,
                BinaryOp::Implies => air::ast::BinaryOp::Implies,
                BinaryOp::And => unreachable!(),
                BinaryOp::Or => unreachable!(),
                BinaryOp::Xor => unreachable!(),
                BinaryOp::StrGetChar => unreachable!(),
            };
            return Ok(Arc::new(ExprX::Binary(bop, lh, rh)));
        }
        ExpX::BinaryOpr(crate::ast::BinaryOpr::ExtEq(..), _, _) => {
            return Err(error(
                &exp.span,
                "error: cannot use extensional equality in bit vector proof",
            ));
        }
        ExpX::If(e1, e2, e3) => mk_ite(
            &bv_exp_to_expr(ctx, e1, expr_ctxt)?,
            &bv_exp_to_expr(ctx, e2, expr_ctxt)?,
            &bv_exp_to_expr(ctx, e3, expr_ctxt)?,
        ),
        ExpX::WithTriggers(_triggers, body) => bv_exp_to_expr(ctx, body, expr_ctxt)?,
        ExpX::Bind(bnd, e) => match &bnd.x {
            BndX::Let(binders) => {
                let expr = bv_exp_to_expr(ctx, e, expr_ctxt)?;
                let binders =
                    vec_map_result(&*binders, |b| match bv_exp_to_expr(ctx, &b.a, expr_ctxt) {
                        Ok(expr) => {
                            Ok(Arc::new(BinderX { name: suffix_local_expr_id(&b.name), a: expr }))
                        }
                        Err(vir_err) => Err(vir_err.clone()),
                    })?;
                air::ast_util::mk_let(&binders, &expr)
            }
            BndX::Quant(quant, binders, trigs, is_mbqi) => {
                let expr = bv_exp_to_expr(ctx, e, expr_ctxt)?;
                let mut bs: Vec<Binder<air::ast::Typ>> = Vec::new();
                for binder in binders.iter() {
                    let typ = {
                        let bv_typ_option = bv_typ_to_air(&binder.a);
                        if bv_typ_option.is_none() {
                            return Err(error(
                                &exp.span,
                                format!("unsupported type in bitvector {:?}", &binder.a),
                            ));
                        };
                        bv_typ_option.unwrap()
                    };
                    let names_typs = match &*binder.a {
                        // allow quantifiers over type parameters, generated for broadcast_forall
                        TypX::TypeId => {
                            let xts = crate::def::suffix_typ_param_ids_types(&binder.name);
                            xts.into_iter().map(|(x, t)| (x, str_typ(&t))).collect()
                        }
                        _ => vec![(suffix_local_expr_id(&binder.name), typ)],
                    };
                    for (name, typ) in names_typs {
                        bs.push(Arc::new(BinderX { name, a: typ.clone() }));
                    }
                }
                let triggers = vec_map_result(&*trigs, |trig| {
                    vec_map_result(trig, |x| bv_exp_to_expr(ctx, x, expr_ctxt)).map(|v| Arc::new(v))
                })?;
                let qid = crate::sst_to_air::new_user_qid(ctx, &exp, *is_mbqi);
                air::ast_util::mk_quantifier(quant.quant, &bs, &triggers, qid, &expr)
            }
            _ => {
                return Err(error(
                    &exp.span,
                    format!("unsupported for bit-vector: bind conversion, {:?} ", exp.x),
                ));
            }
        },
        ExpX::Interp(_) => {
            panic!("Found an interpreter expression {:?} outside the interpreter", exp)
        }
        _ => {
            return Err(error(
                &exp.span,
                format!("unsupported for bit-vector: expression conversion {:?}", exp.x),
            ));
        }
    };
    Ok(result)
}

fn bitvector_expect_exact(
    ctx: &Ctx,
    span: &Span,
    typ: &Typ,
    bitwidth: &Option<IntegerTypeBitwidth>,
) -> Result<u32, VirErr> {
    match bitwidth {
        Some(w) => {
            let w = w.to_exact(&ctx.global.arch);
            match w {
                Some(w) => Ok(w),
                None => Err(error(
                    span,
                    format!(
                        "IntRange error: the bit-width of type {:?} is architecture-dependent, which `by(bit_vector)` does not currently support",
                        typ
                    ),
                )),
            }
        }
        None => Err(error(
            span,
            format!("IntRange error: expected finite-width integer for bit-vector, got {:?}", typ),
        )),
    }
}

fn check_unsigned(exp: &Exp) -> Result<(), VirErr> {
    if let TypX::Int(range) = &*undecorate_typ(&exp.typ) {
        match range {
            IntRange::I(_) | IntRange::ISize => {
                return Err(error(
                    &exp.span,
                    format!("error: signed integer is not supported for bit-vector reasoning",),
                ));
            }
            _ => (),
        }
    };
    Ok(())
}

pub(crate) fn bv_typ_to_air(typ: &Typ) -> Option<air::ast::Typ> {
    match &**typ {
        TypX::Int(IntRange::U(size) | IntRange::I(size)) => Some(bv_typ(*size)),
        TypX::Bool => Some(bool_typ()),
        TypX::Decorate(_, t) => bv_typ_to_air(t),
        TypX::Boxed(t) => bv_typ_to_air(t),
        _ => None,
    }
}

pub(crate) fn zero_extend(bv_e: &Expr, padding: u32) -> Expr {
    let bop = air::ast::BinaryOp::BitConcat;
    let zero_pad = Arc::new(ExprX::Const(Constant::BitVec(Arc::new("0".to_string()), padding)));
    Arc::new(ExprX::Binary(bop, zero_pad, bv_e.clone()))
}

pub(crate) fn zero_extend_smaller_one_to_same_bitwidth(
    ctx: &Ctx,
    lh: &Expr,
    lexp: &Exp,
    rh: &Expr,
    rexp: &Exp,
) -> Result<(Expr, Expr), VirErr> {
    // When getting the widths, we need to account for the possibility that it was
    // an integer that used the type hints, in which case lexp.typ will
    // give a non-fixed or non-finite bit type. In this case we can get the chosen
    // bit width from the Constant::BitVec.
    // (We should be able to be more systematic about this.)

    let lwidth = match &**lh {
        ExprX::Const(Constant::BitVec(_, w)) => *w,
        _ => {
            let lwidth = bitwidth_from_type(&lexp.typ);
            let lwidth = bitvector_expect_exact(ctx, &lexp.span, &lexp.typ, &lwidth)?;
            lwidth
        }
    };

    let rwidth = match &**rh {
        ExprX::Const(Constant::BitVec(_, w)) => *w,
        _ => {
            let rwidth = bitwidth_from_type(&rexp.typ);
            let rwidth = bitvector_expect_exact(ctx, &rexp.span, &rexp.typ, &rwidth)?;
            rwidth
        }
    };

    if lwidth < rwidth {
        Ok((zero_extend(lh, rwidth - lwidth), rh.clone()))
    } else if lwidth > rwidth {
        Ok((lh.clone(), zero_extend(rh, lwidth - rwidth)))
    } else {
        Ok((lh.clone(), rh.clone()))
    }
}
