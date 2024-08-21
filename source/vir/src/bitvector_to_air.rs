use crate::ast::{
    ArchWordBits, ArithOp, BinaryOp, BitwiseOp, InequalityOp, IntRange, IntegerTypeBitwidth,
    IntegerTypeBoundKind, SpannedTyped, Typ, TypX, UnaryOp, UnaryOpr, VarIdent,
    VarIdentDisambiguate, VirErr,
};
use crate::ast_util::{
    allowed_bitvector_type, bitwidth_from_int_range, bitwidth_from_type, is_integer_type,
    is_integer_type_signed, LowerUniqueVar,
};
use crate::context::Ctx;
use crate::def::suffix_local_unique_id;
use crate::messages::{error, Span};
use crate::sst::{BndX, Exp, ExpX};
use crate::util::vec_map_result;
use air::ast::{Binder, BinderX, Constant, Decl, DeclX, Expr, ExprX, Ident, Query, QueryX};
use air::ast_util::{
    bool_typ, mk_and, mk_implies, mk_ite, mk_or, mk_unnamed_axiom, mk_xor, str_typ, string_var,
};
use air::scope_map::ScopeMap;
use num_bigint::BigInt;
use num_traits::{FromPrimitive, Zero};
use std::collections::HashMap;
use std::convert::TryInto;
use std::ops::Sub;
use std::sync::Arc;

pub(crate) fn bv_to_queries(
    ctx: &Ctx,
    reqs: &Vec<Exp>,
    enss: &Vec<Exp>,
) -> Result<Vec<(Query, String)>, VirErr> {
    let reqs = vec_map_result(reqs, |e| bv_maybe_split(ctx, e))?;
    let enss = vec_map_result(enss, |e| bv_maybe_split(ctx, e))?;

    let needs_specialization = reqs.iter().chain(enss.iter()).any(|v| v.len() > 1);

    if needs_specialization {
        Ok(vec![make_query(&reqs, &enss, Some(32)), make_query(&reqs, &enss, Some(64))])
    } else {
        Ok(vec![make_query(&reqs, &enss, None)])
    }
}

pub struct BvSpecialized {
    pub expr: Expr,
    pub decls: Vec<(Ident, air::ast::Typ)>,
    pub specialized: Option<u32>,
    pub span: Span,
}

fn make_query(
    reqs: &Vec<Vec<BvSpecialized>>,
    enss: &Vec<Vec<BvSpecialized>>,
    sp: Option<u32>,
) -> (Query, String) {
    let mut requires_air: Vec<Expr> = vec![];
    let mut ensures_air: Vec<(Span, Expr)> = vec![];
    let mut all_decl_lists: Vec<&Vec<(Ident, air::ast::Typ)>> = vec![];

    fn get_sp(v: &Vec<BvSpecialized>, sp: Option<u32>) -> &BvSpecialized {
        match sp {
            None => {
                assert!(v.len() == 1);
                assert!(v[0].specialized.is_none());
                &v[0]
            }
            Some(w) => {
                for bvs in v.iter() {
                    if bvs.specialized == None || bvs.specialized == Some(w) {
                        return bvs;
                    }
                }
                unreachable!();
            }
        }
    }

    for rs in reqs.iter() {
        let r = get_sp(rs, sp);
        requires_air.push(r.expr.clone());
        all_decl_lists.push(&r.decls);
    }
    for es in enss.iter() {
        let e = get_sp(es, sp);
        ensures_air.push((e.span.clone(), e.expr.clone()));
        all_decl_lists.push(&e.decls);
    }

    let mut all_decls_map = HashMap::<Ident, air::ast::Typ>::new();
    let mut local: Vec<Decl> = vec![];
    for list in all_decl_lists.iter() {
        for (id, typ) in list.iter() {
            if let Some(typ2) = all_decls_map.get(id) {
                assert!(typ == typ2);
            } else {
                all_decls_map.insert(id.clone(), typ.clone());
                local.push(Arc::new(DeclX::Const(id.clone(), typ.clone())));
            }
        }
    }

    for req in requires_air.iter() {
        local.push(mk_unnamed_axiom(req.clone()));
    }

    let mut air_body: Vec<air::ast::Stmt> = Vec::new();
    for (span, ens) in ensures_air.iter() {
        // This error seems to be ignored, the message below is the important one
        let error = error(span, format!("bitvector assertion not satisfied"));
        let ens_stmt = air::ast::StmtX::Assert(None, error, None, ens.clone());
        air_body.push(Arc::new(ens_stmt));
    }
    let assertion = crate::sst_to_air::one_stmt(air_body);
    let query = Arc::new(QueryX { local: Arc::new(local), assertion });

    let special_note = match sp {
        None => "".to_string(),
        Some(w) => format!(" (with arch-size set to {} bits)", w),
    };
    let error = format!("bitvector assertion not satisfied{}", special_note);

    (query, error)
}

fn bv_maybe_split(ctx: &Ctx, exp: &Exp) -> Result<Vec<BvSpecialized>, VirErr> {
    // If the expression depends on the arch size *and* the arch size isn't specified,
    // then we run translation twice, once for 32-bit and once for 64-bit.
    // The way this works is that, if 'arch' is set to Either32Or64, then
    // bv_exp_to_expr might choose to 'specialize' it if anything in the expression
    // is arch-dependent. After bv_exp_to_expr, we check to see if that happens, and if so,
    // we perform the second run.

    let mut state =
        State { arch: ctx.global.arch, decls: vec![], scope_map: ScopeMap::new(), id_idx: 0 };
    let BvExpr { expr: expr1, bv_typ } = bv_exp_to_expr(ctx, &mut state, exp)?;
    bv_typ.expect_bool(&exp.span)?;
    let mut bv_sp1 = BvSpecialized {
        expr: expr1,
        decls: state.decls,
        specialized: None,
        span: exp.span.clone(),
    };

    if state.arch != ctx.global.arch {
        assert!(ctx.global.arch == ArchWordBits::Either32Or64);
        assert!(state.arch == ArchWordBits::Exactly(32));

        let mut state = State {
            arch: ArchWordBits::Exactly(64),
            decls: vec![],
            scope_map: ScopeMap::new(),
            id_idx: 0,
        };
        let BvExpr { expr: expr2, bv_typ } = bv_exp_to_expr(ctx, &mut state, exp)?;
        bv_typ.expect_bool(&exp.span)?;

        let bv_sp2 = BvSpecialized {
            expr: expr2,
            decls: state.decls,
            specialized: Some(64),
            span: exp.span.clone(),
        };
        bv_sp1.specialized = Some(32);
        Ok(vec![bv_sp1, bv_sp2])
    } else {
        Ok(vec![bv_sp1])
    }
}

struct State {
    pub arch: ArchWordBits,
    pub decls: Vec<(Ident, air::ast::Typ)>,
    pub scope_map: ScopeMap<crate::ast::VarIdent, BvTyp>,
    pub id_idx: u64,
}

fn bitwidth_exact(state: &mut State, w: IntegerTypeBitwidth) -> u32 {
    match w {
        IntegerTypeBitwidth::Width(w) => w,
        IntegerTypeBitwidth::ArchWordSize => {
            match state.arch {
                ArchWordBits::Either32Or64 => {
                    // Fix it to 32 for the rest of this run; later we will
                    // redo the whole translation with 64 bits.
                    let w = 32;
                    state.arch = ArchWordBits::Exactly(w);
                    w
                }
                ArchWordBits::Exactly(w) => w,
            }
        }
    }
}

// SMT BitVecs don't have an inherent notion of signedness;
// The only thing a BitVec has is a bit-width.
// However, some SMT BitVec _operations_ have a notion
// of signedness (e.g., the right shift).
//
// Verus's mathematical model is the opposite: a mathematical
// is just an element of Z, so it has no notion of bit-width
// at all (but of course it has a sign).
//
// Therefore, any integer has many possible representations as
// as bit-vector (different possible bit-widths)
// while any given bit-vector could be the representation of 1 of 2
// possible integers (by treating it as signed or unsigned).
//
// We can express all the standard bit operators as being
// independent of the 'input representations',
// though this is easier for some than others, because there
// are some operators that depend on a given "bit width":
//
//   (+) : Z x Z -> Z
//   (|) : Z x Z -> Z
//   (&) : Z x Z -> Z
//   (^) : Z x Z -> Z
//   (<<) : Bitwidth x Z x Z -> Z
//   (>>) : Z x Z -> Z
//   (signed !) : Z -> Z
//   (unsigned !) : Bitwidth x Z -> Z
//
// For (<<) and (unsigned !), we can consider the Bitwidth to be
// part of the operator, thus we can also view these as
// functions/operators on Z.
//
// In general, when encoding any of these operators, we assume
// the inputs might have arbitrary representations.
// However, some representations are ideal for certain operators,
// so we might need to coerce by truncating or extending.
//
// For example:
//
//   - If we want to do (<< bitwidth=8), and we our two inputs
//     are both 'bv4 interpretted as unsigned', we would extend them to bitwidth 8
//     in order to perform the <<.
//
//   - If we do a (+) and both inputs are represented as unsigned bv32,
//     then we know the answer can fit in a bv33.
//     Thus we emit an addition on two bv33 values.

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Extend {
    Zero,
    Sign,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum BvTyp {
    Bool,
    Bv(u32, Extend),
}

#[derive(Debug, Clone)]
struct BvExpr {
    expr: Expr,
    bv_typ: BvTyp,
}

fn bv_exp_to_expr(ctx: &Ctx, state: &mut State, exp: &Exp) -> Result<BvExpr, VirErr> {
    match &exp.x {
        ExpX::Const(crate::ast::Constant::Int(i)) => {
            let (bv_typ, bitstr) = minimal_bv_for_const(i);
            let (width, _) = bv_typ.expect_bv(&exp.span)?;
            Ok(BvExpr {
                expr: Arc::new(ExprX::Const(Constant::BitVec(Arc::new(bitstr), width))),
                bv_typ: bv_typ,
            })
        }
        ExpX::Const(crate::ast::Constant::Bool(b)) => {
            Ok(BvExpr { expr: Arc::new(ExprX::Const(Constant::Bool(*b))), bv_typ: BvTyp::Bool })
        }
        ExpX::Var(x) => {
            let id = suffix_local_unique_id(x);

            match state.scope_map.get(x) {
                Some(bv_typ) => {
                    // Bound var
                    Ok(BvExpr { expr: string_var(&id), bv_typ: *bv_typ })
                }
                None => {
                    // Free var
                    let bv_typ = bv_typ_for_vir_typ(state, &exp.span, &exp.typ)?;

                    // Add to free vars list (we'll de-dupe later)
                    state.decls.push((id.clone(), bv_typ.to_air_typ()));

                    Ok(BvExpr { expr: string_var(&id), bv_typ: bv_typ })
                }
            }
        }
        ExpX::Unary(op, arg) => match op {
            UnaryOp::Not => {
                let BvExpr { expr, bv_typ } = bv_exp_to_expr(ctx, state, arg)?;
                bv_typ.expect_bool(&arg.span)?;
                let bop = air::ast::UnaryOp::Not;
                let expr = Arc::new(ExprX::Unary(bop, expr));
                Ok(BvExpr { expr, bv_typ: BvTyp::Bool })
            }
            UnaryOp::BitNot(None) => {
                let bv_expr = bv_exp_to_expr(ctx, state, arg)?;
                let bv_expr = make_signed(&exp.span, bv_expr)?;

                let BvExpr { expr, bv_typ } = bv_expr;
                bv_typ.expect_bv_signed(&arg.span)?;

                let bop = air::ast::UnaryOp::BitNot;
                Ok(BvExpr { expr: Arc::new(ExprX::Unary(bop, expr)), bv_typ: bv_typ })
            }
            UnaryOp::BitNot(Some(w)) => {
                let BvExpr { expr, bv_typ } = bv_exp_to_expr(ctx, state, arg)?;
                let w = bitwidth_exact(state, *w);

                let (width, extend) = bv_typ.expect_bv(&arg.span)?;
                let expr = extend_or_trunc(&expr, extend, width, w);

                let bop = air::ast::UnaryOp::BitNot;
                Ok(BvExpr {
                    expr: Arc::new(ExprX::Unary(bop, expr)),
                    bv_typ: BvTyp::Bv(w, Extend::Zero),
                })
            }
            UnaryOp::Clip { range: int_range, .. } => {
                match &arg.x {
                    ExpX::Binary(BinaryOp::Arith(arith_op, _), lhs, rhs) => {
                        return do_arith_then_clip(
                            ctx,
                            state,
                            &exp.span,
                            arith_op,
                            lhs,
                            rhs,
                            Some(*int_range),
                        );
                    }
                    _ => {}
                }

                let bv_expr = bv_exp_to_expr(ctx, state, arg)?;
                do_clip(state, &arg.span, bv_expr, *int_range)
            }
            UnaryOp::HeightTrigger => panic!("internal error: unexpected HeightTrigger"),
            UnaryOp::Trigger(_) => bv_exp_to_expr(ctx, state, arg),
            UnaryOp::CoerceMode { .. } => {
                panic!("internal error: TupleField should have been removed before here")
            }
            UnaryOp::MustBeFinalized | UnaryOp::MustBeElaborated => {
                panic!("internal error: Exp not finalized: {:?}", arg)
            }
            UnaryOp::StrLen | UnaryOp::StrIsAscii => panic!(
                "internal error: matching for bit vector ops on this match should be impossible"
            ),
            UnaryOp::InferSpecForLoopIter { .. } => {
                panic!("internal error: unexpected Option type (from InferSpecForLoopIter)")
            }
            UnaryOp::CastToInteger => {
                panic!("internal error: unexpected CastToInteger")
            }
        },
        ExpX::UnaryOpr(UnaryOpr::Box(_) | UnaryOpr::Unbox(_), exp) => {
            bv_exp_to_expr(ctx, state, exp)
        }
        ExpX::Binary(BinaryOp::Inequality(ineq), lhs, rhs) => {
            let lhs = bv_exp_to_expr(ctx, state, lhs)?;
            let rhs = bv_exp_to_expr(ctx, state, rhs)?;

            let (lhs, rhs) = make_same_bv_typ(&exp.span, lhs, rhs)?;
            assert!(lhs.bv_typ == rhs.bv_typ);

            let (_w, extend) = lhs.bv_typ.expect_bv(&exp.span)?;

            let op = match (ineq, extend) {
                (InequalityOp::Le, Extend::Zero) => air::ast::BinaryOp::BitULe,
                (InequalityOp::Lt, Extend::Zero) => air::ast::BinaryOp::BitULt,
                (InequalityOp::Ge, Extend::Zero) => air::ast::BinaryOp::BitUGe,
                (InequalityOp::Gt, Extend::Zero) => air::ast::BinaryOp::BitUGt,
                (InequalityOp::Le, Extend::Sign) => air::ast::BinaryOp::BitSLe,
                (InequalityOp::Lt, Extend::Sign) => air::ast::BinaryOp::BitSLt,
                (InequalityOp::Ge, Extend::Sign) => air::ast::BinaryOp::BitSGe,
                (InequalityOp::Gt, Extend::Sign) => air::ast::BinaryOp::BitSGt,
            };

            Ok(BvExpr {
                expr: Arc::new(ExprX::Binary(op, lhs.expr, rhs.expr)),
                bv_typ: BvTyp::Bool,
            })
        }
        ExpX::Binary(op @ (BinaryOp::Eq(_) | BinaryOp::Ne), lhs, rhs) => {
            let lhs = bv_exp_to_expr(ctx, state, lhs)?;
            let rhs = bv_exp_to_expr(ctx, state, rhs)?;

            let (lhs, rhs) = make_same_bv_typ(&exp.span, lhs, rhs)?;
            assert!(lhs.bv_typ == rhs.bv_typ);

            let mut expr = Arc::new(ExprX::Binary(air::ast::BinaryOp::Eq, lhs.expr, rhs.expr));
            if op == &BinaryOp::Ne {
                expr = Arc::new(ExprX::Unary(air::ast::UnaryOp::Not, expr));
            }
            Ok(BvExpr { expr: expr, bv_typ: BvTyp::Bool })
        }
        ExpX::Binary(
            op @ (BinaryOp::Implies | BinaryOp::And | BinaryOp::Or | BinaryOp::Xor),
            lhs,
            rhs,
        ) => {
            let lhs = bv_exp_to_expr(ctx, state, lhs)?;
            let rhs = bv_exp_to_expr(ctx, state, rhs)?;

            assert!(lhs.bv_typ == BvTyp::Bool);
            assert!(rhs.bv_typ == BvTyp::Bool);

            let res = match op {
                BinaryOp::Implies => mk_implies(&lhs.expr, &rhs.expr),
                BinaryOp::Xor => mk_xor(&lhs.expr, &rhs.expr),
                BinaryOp::And => mk_and(&vec![lhs.expr, rhs.expr]),
                BinaryOp::Or => mk_or(&vec![lhs.expr, rhs.expr]),
                _ => unreachable!(),
            };
            Ok(BvExpr { expr: res, bv_typ: BvTyp::Bool })
        }
        ExpX::Binary(
            BinaryOp::Bitwise(op @ (BitwiseOp::BitXor | BitwiseOp::BitAnd | BitwiseOp::BitOr), _),
            lhs,
            rhs,
        ) => {
            let lhs = bv_exp_to_expr(ctx, state, lhs)?;
            let rhs = bv_exp_to_expr(ctx, state, rhs)?;

            let (lhs, rhs) = make_same_bv_typ(&exp.span, lhs, rhs)?;
            assert!(lhs.bv_typ == rhs.bv_typ);

            let op = match op {
                BitwiseOp::BitXor => air::ast::BinaryOp::BitXor,
                BitwiseOp::BitAnd => air::ast::BinaryOp::BitAnd,
                BitwiseOp::BitOr => air::ast::BinaryOp::BitOr,
                _ => unreachable!(),
            };

            Ok(BvExpr { expr: Arc::new(ExprX::Binary(op, lhs.expr, rhs.expr)), bv_typ: lhs.bv_typ })
        }
        ExpX::Binary(BinaryOp::Bitwise(BitwiseOp::Shr(_), _), lhs, rhs) => {
            let lhs = bv_exp_to_expr(ctx, state, lhs)?;
            let rhs = bv_exp_to_expr(ctx, state, rhs)?;

            let (lhs_w, lhs_extend) = lhs.bv_typ.expect_bv(&exp.span)?;
            let (rhs_w, rhs_extend) = rhs.bv_typ.expect_bv(&exp.span)?;

            let mut lhs_expr = lhs.expr;
            let mut rhs_expr = rhs.expr;

            // Rust doesn't require the operands to have equal size
            // Z3 does require it, though, so we have to equalize.

            if lhs_w < rhs_w {
                lhs_expr = extend_bv_expr(&lhs_expr, lhs_extend, lhs_w, rhs_w);
            }
            if lhs_w > rhs_w {
                rhs_expr = extend_bv_expr(&rhs_expr, rhs_extend, rhs_w, lhs_w);
            }

            // Not clear what it would mean to shift by a negative amount.
            if rhs_extend != Extend::Zero {
                return Err(error(
                    &exp.span,
                    format!(
                        "not supported: bit-shift with possibly negative shift (If you believe this value is always nonnegative, try casting the RHS to an unsigned type)"
                    ),
                ));
            }

            let op = match lhs_extend {
                Extend::Zero => air::ast::BinaryOp::LShr,
                Extend::Sign => air::ast::BinaryOp::AShr,
            };
            let expr = Arc::new(ExprX::Binary(op, lhs_expr, rhs_expr));

            let expr = if lhs_w < rhs_w { truncate(&expr, lhs_w) } else { expr };

            Ok(BvExpr { expr, bv_typ: lhs.bv_typ })
        }
        ExpX::Binary(BinaryOp::Bitwise(BitwiseOp::Shl(w, signed), _), lhs, rhs) => {
            let w = bitwidth_exact(state, *w);

            let lhs = bv_exp_to_expr(ctx, state, lhs)?;
            let rhs = bv_exp_to_expr(ctx, state, rhs)?;

            let (lhs_w, lhs_extend) = lhs.bv_typ.expect_bv(&exp.span)?;
            let (rhs_w, rhs_extend) = rhs.bv_typ.expect_bv(&exp.span)?;

            if rhs_extend != Extend::Zero {
                // There isn't an obvious way to choose a definition of
                // shifting by a negative amount that we could implement
                // consistently.
                return Err(error(
                    &exp.span,
                    format!(
                        "not supported: bit-shift with possibly negative shift (If you believe this value is always nonnegative, try casting the RHS to an unsigned type)"
                    ),
                ));
            }

            let shift_w = std::cmp::max(w, rhs_w);

            let mut lhs_expr = lhs.expr;
            let mut rhs_expr = rhs.expr;

            if shift_w < lhs_w {
                lhs_expr = truncate(&lhs_expr, shift_w);
            } else if shift_w > lhs_w {
                lhs_expr = extend_bv_expr(&lhs_expr, lhs_extend, lhs_w, shift_w);
            }

            if rhs_w < shift_w {
                rhs_expr = extend_bv_expr(&rhs_expr, rhs_extend, rhs_w, shift_w);
            }

            let op = air::ast::BinaryOp::Shl;
            let extend = if *signed { Extend::Sign } else { Extend::Zero };
            let expr = Arc::new(ExprX::Binary(op, lhs_expr, rhs_expr));

            let expr = if w < shift_w { truncate(&expr, w) } else { expr };

            Ok(BvExpr { expr: expr, bv_typ: BvTyp::Bv(w, extend) })
        }
        ExpX::Binary(BinaryOp::Arith(arith_op, _), lhs, rhs) => {
            return do_arith_then_clip(ctx, state, &exp.span, arith_op, lhs, rhs, None);
        }
        ExpX::BinaryOpr(crate::ast::BinaryOpr::ExtEq(..), _, _) => {
            return Err(error(
                &exp.span,
                "error: cannot use extensional equality in bit vector proof",
            ));
        }
        ExpX::UnaryOpr(
            crate::ast::UnaryOpr::IntegerTypeBound(IntegerTypeBoundKind::ArchWordBits, _mode),
            _e,
        ) => {
            let archw = bitwidth_exact(state, IntegerTypeBitwidth::ArchWordSize);
            let i = BigInt::from_u32(archw).unwrap();
            let expx = ExpX::Const(crate::ast::Constant::Int(i));
            let exp = SpannedTyped::new(&exp.span, &exp.typ, expx);
            bv_exp_to_expr(ctx, state, &exp)
        }
        ExpX::If(e1, e2, e3) => {
            let cond = bv_exp_to_expr(ctx, state, e1)?;
            let thn = bv_exp_to_expr(ctx, state, e2)?;
            let els = bv_exp_to_expr(ctx, state, e3)?;

            cond.bv_typ.expect_bool(&e1.span)?;
            let (thn, els) = make_same_bv_typ(&exp.span, thn, els)?;

            Ok(BvExpr { expr: mk_ite(&cond.expr, &thn.expr, &els.expr), bv_typ: thn.bv_typ })
        }
        ExpX::WithTriggers(_triggers, body) => bv_exp_to_expr(ctx, state, body),
        ExpX::Bind(bnd, e) => match &bnd.x {
            BndX::Let(binders) => {
                let mut bs: Vec<Binder<Expr>> = Vec::new();
                let mut bv_typs = vec![];
                for b in binders.iter() {
                    let e = bv_exp_to_expr(ctx, state, &b.a)?;
                    bs.push(Arc::new(BinderX { name: b.name.lower(), a: e.expr }));
                    bv_typs.push((b.name.clone(), e.bv_typ));
                }

                state.scope_map.push_scope(true);
                for (id, bv_typ) in bv_typs.iter() {
                    state.scope_map.insert(id.clone(), *bv_typ).unwrap();
                }

                let body = bv_exp_to_expr(ctx, state, e)?;

                state.scope_map.pop_scope();

                let expr = air::ast_util::mk_let(&bs, &body.expr);
                Ok(BvExpr { expr, bv_typ: body.bv_typ })
            }
            BndX::Quant(quant, binders, trigs) => {
                state.scope_map.push_scope(true);
                for b in binders.iter() {
                    let bv_typ = bv_typ_for_vir_typ(state, &exp.span, &b.a)?;
                    state.scope_map.insert(b.name.clone(), bv_typ).unwrap();
                }

                let BvExpr { expr, bv_typ } = bv_exp_to_expr(ctx, state, e)?;
                bv_typ.expect_bool(&e.span)?;

                let mut bs: Vec<Binder<air::ast::Typ>> = Vec::new();
                for binder in binders.iter() {
                    let typ = vir_typ_to_air(state, &exp.span, &binder.a)?;
                    let names_typs = match &*binder.a {
                        // allow quantifiers over type parameters, generated for broadcast_forall
                        TypX::TypeId => {
                            let xts = crate::def::suffix_typ_param_vars_types(&binder.name);
                            xts.into_iter().map(|(x, t)| (x.lower(), str_typ(&t))).collect()
                        }
                        _ => vec![(binder.name.lower(), typ)],
                    };
                    for (name, typ) in names_typs {
                        bs.push(Arc::new(BinderX { name, a: typ.clone() }));
                    }
                }
                let triggers = vec_map_result(&*trigs, |trig| {
                    vec_map_result::<_, _, VirErr, _>(trig, |x| {
                        Ok(bv_exp_to_expr(ctx, state, x)?.expr)
                    })
                    .map(|v| Arc::new(v))
                })?;

                state.scope_map.pop_scope();

                let qid = crate::sst_to_air::new_user_qid(ctx, &exp);
                let e = air::ast_util::mk_quantifier(quant.quant, &bs, &triggers, qid, &expr);

                Ok(BvExpr { expr: e, bv_typ: BvTyp::Bool })
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
    }
}

fn bitvector_expect_finite(
    state: &mut State,
    span: &Span,
    typ: &Typ,
    bitwidth: &Option<IntegerTypeBitwidth>,
) -> Result<u32, VirErr> {
    match bitwidth {
        Some(w) => Ok(bitwidth_exact(state, *w)),
        None => Err(error(
            span,
            format!("IntRange error: expected finite-width integer for bit-vector, got {:?}", typ),
        )),
    }
}

fn vir_typ_to_air(state: &mut State, span: &Span, typ: &Typ) -> Result<air::ast::Typ, VirErr> {
    match &**typ {
        TypX::Int(range) => Ok(air::ast_util::bv_typ(width_of_int_range(state, span, range)?)),
        TypX::Bool => Ok(bool_typ()),
        TypX::Decorate(_, _, t) => vir_typ_to_air(state, span, t),
        TypX::Boxed(t) => vir_typ_to_air(state, span, t),
        _ => Err(error(span, format!("unsupported type in bitvector {:?}", &typ))),
    }
}

fn zero_extend(expr: &Expr, cur: u32, target: u32) -> Expr {
    assert!(cur <= target);
    if cur == target {
        return expr.clone();
    }
    let uop = air::ast::UnaryOp::BitZeroExtend(target - cur);
    Arc::new(ExprX::Unary(uop, expr.clone()))
}

fn sign_extend(expr: &Expr, cur: u32, target: u32) -> Expr {
    assert!(cur <= target);
    if cur == target {
        return expr.clone();
    }
    let uop = air::ast::UnaryOp::BitSignExtend(target - cur);
    Arc::new(ExprX::Unary(uop, expr.clone()))
}

fn extend_bv_expr(expr: &Expr, extend: Extend, cur: u32, target: u32) -> Expr {
    match extend {
        Extend::Zero => zero_extend(expr, cur, target),
        Extend::Sign => sign_extend(expr, cur, target),
    }
}

/// Truncate to the given bitwidth
fn truncate(expr: &Expr, w: u32) -> Expr {
    let op = air::ast::UnaryOp::BitExtract(w - 1, 0);
    Arc::new(ExprX::Unary(op, expr.clone()))
}

/// Extend or truncate to the given bitwidth
fn extend_or_trunc(expr: &Expr, extend: Extend, cur: u32, target: u32) -> Expr {
    if target > cur {
        extend_bv_expr(expr, extend, cur, target)
    } else if target < cur {
        truncate(expr, target)
    } else {
        expr.clone()
    }
}

/// Clips value to the given range,
/// but might return a smaller bit width if possible.
fn do_clip(
    state: &mut State,
    span: &Span,
    bv_expr: BvExpr,
    int_range: IntRange,
) -> Result<BvExpr, VirErr> {
    let BvExpr { expr, bv_typ } = bv_expr;
    let new_n = bitwidth_from_int_range(&int_range);

    let typ = Arc::new(TypX::Int(int_range));
    let new_n = bitvector_expect_finite(state, span, &typ, &new_n)?;
    let new_extend = signedness_of_int_range(span, &int_range)?;

    let (old_n, old_extend) = bv_typ.expect_bv(span)?;

    if new_n > old_n {
        // truncate to a larger n does nothing unless we
        // are going signed -> unsigned
        if old_extend == Extend::Sign && new_extend == Extend::Zero {
            let expr = extend_bv_expr(&expr, old_extend, old_n, new_n);
            Ok(BvExpr { expr: expr, bv_typ: BvTyp::Bv(new_n, new_extend) })
        } else {
            Ok(BvExpr { expr: expr, bv_typ: BvTyp::Bv(old_n, old_extend) })
        }
    } else if new_n < old_n {
        let expr = truncate(&expr, new_n);
        Ok(BvExpr { expr: expr, bv_typ: BvTyp::Bv(new_n, new_extend) })
    } else {
        Ok(BvExpr { expr: expr, bv_typ: BvTyp::Bv(new_n, new_extend) })
    }
}

/// Returns a BvExpr with the same value that is guaranteed to be Sign extended
fn make_signed(span: &Span, e: BvExpr) -> Result<BvExpr, VirErr> {
    let (w, extend) = e.bv_typ.expect_bv(span)?;

    Ok(match extend {
        Extend::Sign => e.clone(),
        Extend::Zero => {
            // Add a 0 to the left so sign-extending is the same as zero-extending it
            let expr = extend_bv_expr(&e.expr, Extend::Zero, w, w + 1);
            BvExpr { expr, bv_typ: BvTyp::Bv(w + 1, Extend::Sign) }
        }
    })
}

/// Extend one or both of the bit-vectors so they have the same width and signedness.
fn make_same_bv_typ(span: &Span, lhs: BvExpr, rhs: BvExpr) -> Result<(BvExpr, BvExpr), VirErr> {
    if lhs.bv_typ == BvTyp::Bool && rhs.bv_typ == BvTyp::Bool {
        return Ok((lhs, rhs));
    }

    // Compute the minimum extension satisfying both constraints:
    //  - We need to extend both to be the same width
    //  - If signed vs unsigned, the unsigned one must be zero-extended
    //    by at least one bit.

    let BvExpr { expr: lhs_expr, bv_typ: lhs_typ } = lhs;
    let BvExpr { expr: rhs_expr, bv_typ: rhs_typ } = rhs;
    let (lhs_w, lhs_extend) = lhs_typ.expect_bv(span)?;
    let (rhs_w, rhs_extend) = rhs_typ.expect_bv(span)?;

    let l_w =
        if lhs_extend == Extend::Zero && rhs_extend == Extend::Sign { lhs_w + 1 } else { lhs_w };

    let r_w =
        if rhs_extend == Extend::Zero && lhs_extend == Extend::Sign { rhs_w + 1 } else { rhs_w };

    let target_width = std::cmp::max(l_w, r_w);

    let lhs_expr = extend_bv_expr(&lhs_expr, lhs_extend, lhs_w, target_width);
    let rhs_expr = extend_bv_expr(&rhs_expr, rhs_extend, rhs_w, target_width);
    let extend = if lhs_extend == Extend::Sign || rhs_extend == Extend::Sign {
        Extend::Sign
    } else {
        Extend::Zero
    };
    let bv_typ = BvTyp::Bv(target_width, extend);

    Ok((BvExpr { expr: lhs_expr, bv_typ }, BvExpr { expr: rhs_expr, bv_typ }))
}

impl BvTyp {
    fn expect_bool(&self, span: &Span) -> Result<(), VirErr> {
        match self {
            BvTyp::Bool => Ok(()),
            _ => Err(error(span, format!("Verus Internal Error: expect_bool"))),
        }
    }

    fn expect_bv_signed(&self, span: &Span) -> Result<(), VirErr> {
        match self {
            BvTyp::Bv(_, Extend::Sign) => Ok(()),
            _ => Err(error(span, format!("Verus Internal Error: expect_bv_signed"))),
        }
    }

    fn expect_bv(&self, span: &Span) -> Result<(u32, Extend), VirErr> {
        match self {
            BvTyp::Bv(w, extend) => Ok((*w, *extend)),
            _ => Err(error(span, format!("Verus Internal Error: expect_bv"))),
        }
    }

    fn to_air_typ(&self) -> air::ast::Typ {
        match self {
            BvTyp::Bv(w, _) => air::ast_util::bv_typ(*w),
            BvTyp::Bool => bool_typ(),
        }
    }
}

fn signedness_of_int_range(span: &Span, range: &IntRange) -> Result<Extend, VirErr> {
    match range {
        IntRange::Int | IntRange::I(_) | IntRange::ISize => Ok(Extend::Sign),
        IntRange::Nat | IntRange::U(_) | IntRange::USize => Ok(Extend::Zero),
        IntRange::Char => Err(error(span, format!("char not supported in bit-vector query"))),
    }
}

fn width_of_int_range(state: &mut State, span: &Span, range: &IntRange) -> Result<u32, VirErr> {
    match range {
        IntRange::I(w) | IntRange::U(w) => Ok(*w),
        IntRange::USize | IntRange::ISize => {
            Ok(bitwidth_exact(state, IntegerTypeBitwidth::ArchWordSize))
        }
        IntRange::Int | IntRange::Nat => {
            Err(error(span, format!("symbolic int/nat not supported in bit-vector query")))
        }
        IntRange::Char => Err(error(span, format!("char not supported in bit-vector query"))),
    }
}

fn minimal_bv_for_const(i: &BigInt) -> (BvTyp, String) {
    if i.lt(&BigInt::zero()) {
        let mut twos_complement = BigInt::from_i64(-1).unwrap().sub(i);
        // Set the sign bit
        let width = twos_complement.bits() + 1;
        twos_complement.set_bit(width - 1, true);
        (BvTyp::Bv(width.try_into().unwrap(), Extend::Sign), twos_complement.to_string())
    } else {
        let width = std::cmp::max(i.bits(), 1);
        (BvTyp::Bv(width.try_into().unwrap(), Extend::Zero), i.to_string())
    }
}

fn bv_typ_for_vir_typ(state: &mut State, span: &Span, typ: &Typ) -> Result<BvTyp, VirErr> {
    if is_integer_type(typ) {
        // error if either:
        //  - it's an infinite width type / char
        let width = bitwidth_from_type(typ);
        let width = bitvector_expect_finite(state, span, typ, &width)?;
        let signed = is_integer_type_signed(typ);
        Ok(BvTyp::Bv(width, if signed { Extend::Sign } else { Extend::Zero }))
    } else {
        if allowed_bitvector_type(typ) {
            Ok(BvTyp::Bool)
        } else {
            Err(error(
                span,
                format!(
                    "error: bit_vector prover cannot handle this type (bit_vector can only handle variables of type `bool` or of fixed-width integers)"
                ),
            ))
        }
    }
}

/// If no clip is given: compute `lhs op rhs` (losslessly)
/// If clip is given: compute `clip(lhs op rhs)`
fn do_arith_then_clip(
    ctx: &Ctx,
    state: &mut State,
    span: &Span,
    arith_op: &ArithOp,
    lhs: &Exp,
    rhs: &Exp,
    int_range: Option<IntRange>,
) -> Result<BvExpr, VirErr> {
    let bv_lhs = bv_exp_to_expr(ctx, state, lhs)?;
    let bv_rhs = bv_exp_to_expr(ctx, state, rhs)?;

    let (lhs_w, lhs_extend) = bv_lhs.bv_typ.expect_bv(&lhs.span)?;
    let (rhs_w, rhs_extend) = bv_rhs.bv_typ.expect_bv(&rhs.span)?;

    let lhs_expr = bv_lhs.expr.clone();
    let rhs_expr = bv_rhs.expr.clone();

    let mut int_range = int_range;
    if int_range == Some(IntRange::Int) {
        int_range = None;
    }
    if int_range == Some(IntRange::Nat) {
        if lhs_extend == Extend::Zero
            && rhs_extend == Extend::Zero
            && (*arith_op == ArithOp::Add || *arith_op == ArithOp::Mul)
        {
            int_range = None;
        } else {
            return Err(error(span, format!("not supported: nat cast here")));
        }
    }

    if matches!(arith_op, ArithOp::Add | ArithOp::Mul | ArithOp::Sub) {
        let op = match arith_op {
            ArithOp::Add => air::ast::BinaryOp::BitAdd,
            ArithOp::Sub => air::ast::BinaryOp::BitSub,
            ArithOp::Mul => air::ast::BinaryOp::BitMul,
            ArithOp::EuclideanDiv | ArithOp::EuclideanMod => unreachable!(),
        };

        // How can we represent the result losslessly?
        let (lossless_w, lossless_extend) = match arith_op {
            ArithOp::Add => {
                match (lhs_extend, rhs_extend) {
                    (Extend::Zero, Extend::Zero) => {
                        // If X and Y fit in N bits, unsigned,
                        // then (X + Y) fits in N+1 bits, unsigned
                        //  (2^N - 1) + (2^N - 1) <= (2^N - 1)

                        let w = std::cmp::max(lhs_w, rhs_w) + 1;
                        (w, Extend::Zero)
                    }
                    (Extend::Sign, Extend::Sign) => {
                        // If X and Y fit in N bits, signed
                        // then (X + Y) fits in N+1 bits, signed
                        //  (2^(N-1) - 1) + (2^(N-1) - 1) <= (2^N - 1)
                        //  -2^(N-1) - 2^(N-1) >= -2^N

                        let w = std::cmp::max(lhs_w, rhs_w) + 1;
                        (w, Extend::Sign)
                    }
                    (Extend::Zero, Extend::Sign) => {
                        // If X fits in N bits, unsigned
                        // and Y fits in M bits, signed then:
                        // hi: (2^N - 1) + (2^(M-1) - 1) <= 2^max(N+1, M) - 1
                        // lo: (-2^(M-1))
                        // which all fit in signed max(N+2, M+1)

                        let w = std::cmp::max(lhs_w + 2, rhs_w + 1);
                        (w, Extend::Sign)
                    }
                    (Extend::Sign, Extend::Zero) => {
                        let w = std::cmp::max(lhs_w + 1, rhs_w + 2);
                        (w, Extend::Sign)
                    }
                }
            }
            ArithOp::Sub => {
                let w = match (lhs_extend, rhs_extend) {
                    (Extend::Zero, Extend::Zero) => {
                        // max: 2^a - 1
                        // min: -2^b + 1
                        // all fit in signed max(a+1, b+1)
                        std::cmp::max(lhs_w + 1, rhs_w + 1)
                    }
                    (Extend::Zero, Extend::Sign) => {
                        // max: (2^a - 1) - (-2^(b-1)) <= 2^max(a+1, b) - 1
                        // min: -2^a - (2^(b-1) - 1) >= -2^max(a+1, b)
                        // all fit in signed max(a+2, b+1)
                        std::cmp::max(lhs_w + 2, rhs_w + 1)
                    }
                    (Extend::Sign, Extend::Zero) => {
                        // max: (2^(a-1) - 1)
                        // min: -2^(a-1) - 2^b + 1 >= -2^max(a, b+1)
                        std::cmp::max(lhs_w + 1, rhs_w + 2)
                    }
                    (Extend::Sign, Extend::Sign) => {
                        // max: 2^(a-1) - 1 + 2^(b-1) <= 2^max(a+b) - 1
                        // min: -2^(a-1) - 2^(b-1) + 1 >= -2^max(a+b)
                        std::cmp::max(lhs_w + 1, rhs_w + 1)
                    }
                };
                (w, Extend::Sign)
            }
            ArithOp::Mul => match (lhs_extend, rhs_extend) {
                (Extend::Zero, Extend::Zero) => (lhs_w + rhs_w, Extend::Zero),
                (Extend::Zero, Extend::Sign) | (Extend::Sign, Extend::Zero) => {
                    (lhs_w + rhs_w, Extend::Sign)
                }
                (Extend::Sign, Extend::Sign) => (lhs_w + rhs_w, Extend::Sign),
            },
            _ => unreachable!(),
        };

        match int_range {
            None => {
                let lhs_expr = extend_bv_expr(&lhs_expr, lhs_extend, lhs_w, lossless_w);
                let rhs_expr = extend_bv_expr(&rhs_expr, rhs_extend, rhs_w, lossless_w);

                let expr = Arc::new(ExprX::Binary(op, lhs_expr, rhs_expr));

                Ok(BvExpr { expr: expr, bv_typ: BvTyp::Bv(lossless_w, lossless_extend) })
            }
            Some(ir) => {
                let ir_w = width_of_int_range(state, span, &ir)?;
                let ir_extend = signedness_of_int_range(span, &ir)?;

                if ir_w <= lossless_w {
                    // For `op` in [add, mul, sub]:
                    // `clip(a op b, rng) = clip(a, rng) op[rng] clip(b, rng)
                    // Thus, we can do the clip before calling the op.

                    let lhs_expr = extend_or_trunc(&lhs_expr, lhs_extend, lhs_w, ir_w);
                    let rhs_expr = extend_or_trunc(&rhs_expr, rhs_extend, rhs_w, ir_w);

                    let expr = Arc::new(ExprX::Binary(op, lhs_expr, rhs_expr));

                    Ok(BvExpr { expr: expr, bv_typ: BvTyp::Bv(ir_w, ir_extend) })
                } else {
                    // Case: The clip-width is actually *larger* than the lossless_w
                    // In this case, we perform the lossless arith operation before
                    // the clip

                    let lhs_expr = extend_bv_expr(&lhs_expr, lhs_extend, lhs_w, lossless_w);
                    let rhs_expr = extend_bv_expr(&rhs_expr, rhs_extend, rhs_w, lossless_w);

                    let expr = Arc::new(ExprX::Binary(op, lhs_expr, rhs_expr));
                    let bv_expr =
                        BvExpr { expr: expr, bv_typ: BvTyp::Bv(lossless_w, lossless_extend) };

                    // Since lossless_w < ir_w, this clip operation is only
                    // nontrivial when clipping from signed to unsigned
                    do_clip(state, span, bv_expr, ir)
                }
            }
        }
    } else {
        let id = state.fresh_id();
        let rhs_tmp = BvExpr { expr: Arc::new(ExprX::Var(id.clone())), bv_typ: bv_rhs.bv_typ };

        let bve = do_div_or_mod_then_clip(state, span, arith_op, &bv_lhs, &rhs_tmp, int_range)?;
        let guarded = if_then_arbitrary(state, span, &test_eq_0(span, &rhs_tmp)?, &bve)?;

        let binders = Arc::new(vec![Arc::new(BinderX { name: id, a: bv_rhs.expr })]);
        let e = Arc::new(ExprX::Bind(Arc::new(air::ast::BindX::Let(binders)), guarded.expr));
        Ok(BvExpr { expr: e, bv_typ: guarded.bv_typ })
    }
}

/// Caller is responsible for handling the rhs=0 case
fn do_div_or_mod_then_clip(
    state: &mut State,
    span: &Span,
    arith_op: &ArithOp,
    bv_lhs: &BvExpr,
    bv_rhs: &BvExpr,
    int_range: Option<IntRange>,
) -> Result<BvExpr, VirErr> {
    let (lhs_w, lhs_extend) = bv_lhs.bv_typ.expect_bv(span)?;
    let (rhs_w, rhs_extend) = bv_rhs.bv_typ.expect_bv(span)?;

    let lhs_expr = bv_lhs.expr.clone();
    let rhs_expr = bv_rhs.expr.clone();

    match (lhs_extend, rhs_extend) {
        (Extend::Zero, Extend::Zero) => {
            // Nothing fancy, do the operation losslessly, then clip.

            let op = match arith_op {
                ArithOp::EuclideanDiv => air::ast::BinaryOp::BitUDiv,
                ArithOp::EuclideanMod => air::ast::BinaryOp::BitUMod,
                _ => unreachable!(),
            };

            // When dealing with only unsigned, we always have
            // 0 <= a / b <= a
            // So w = max(lhs_w, rhs_w) is big enough to hold
            // both operands and the result.
            let w = std::cmp::max(lhs_w, rhs_w);

            let lhs_expr = extend_bv_expr(&lhs_expr, lhs_extend, lhs_w, w);
            let rhs_expr = extend_bv_expr(&rhs_expr, rhs_extend, rhs_w, w);

            let expr = Arc::new(ExprX::Binary(op, lhs_expr, rhs_expr));

            let bv_expr = BvExpr { expr: expr, bv_typ: BvTyp::Bv(w, Extend::Zero) };

            match int_range {
                None => Ok(bv_expr),
                Some(ir) => do_clip(state, span, bv_expr, ir),
            }
        }
        _ => {
            return Err(error(span, format!("not yet supported: div/mod for signed arithmetic")));

            /*
            None of z3's bv operations give us what we need.
            Good luck!

            Verus Euclidean Mod:
                   7    %   3     ==  1
                   (-7) %   3     ==  2
                   7    %   (-3)  ==  1
                   (-7) %   (-3)  ==  2

            Verus Euclidean Div:
                   7    /   3     ==  2
                   (-7) /   3     ==  -3
                   7    /   (-3)  ==  -2
                   (-7) /   (-3)  ==  3

            z3 operations:
                Using bvsrem:
                   7     %  3     ==  1
                   (-7)  %  3     ==  -1
                   7     %  (-3)  ==  1
                   (-7)  %  (-3)  ==  -1

                Using bvsmod:
                   7     %  3     ==  1
                   (-7)  %  3     ==  2
                   7     %  (-3)  ==  -2
                   (-7)  %  (-3)  ==  -1

                Using bvsdiv:
                   7     /  3     ==  2
                   (-7)  /  (-3)  ==  -2
                   7     /  (-3)  ==  -2
                   (-7)  /  3     ==  2

            Try it yourself:

            (simplify (bvsrem #x07 #x03))
            (simplify (bvsrem (bvneg #x07) #x03))
            (simplify (bvsrem #x07 (bvneg #x03)))
            (simplify (bvsrem (bvneg #x07) (bvneg #x03)))

            (simplify (bvsmod #x07 #x03))
            (simplify (bvsmod (bvneg #x07) #x03))
            (simplify (bvsmod #x07 (bvneg #x03)))
            (simplify (bvsmod (bvneg #x07) (bvneg #x03)))

            (simplify (bvsdiv #x07 #x03))
            (simplify (bvsdiv (bvneg #x07) #x03))
            (simplify (bvsdiv #x07 (bvneg #x03)))
            (simplify (bvsdiv (bvneg #x07) (bvneg #x03)))
            */
        }
    }
}

fn test_eq_0(span: &Span, exp: &BvExpr) -> Result<Expr, VirErr> {
    let (width, _) = exp.bv_typ.expect_bv(span)?;
    let zero = Arc::new(ExprX::Const(Constant::BitVec(Arc::new("0".to_string()), width)));
    let eq = Arc::new(ExprX::Binary(air::ast::BinaryOp::Eq, exp.expr.clone(), zero));
    Ok(eq)
}

/// if condition { arbitrary } else { exp }
/// the "arbitrary" variable is fresh for every instance
fn if_then_arbitrary(
    state: &mut State,
    span: &Span,
    bool_condition: &Expr,
    exp: &BvExpr,
) -> Result<BvExpr, VirErr> {
    let (width, _) = exp.bv_typ.expect_bv(span)?;
    let id = state.fresh_id();
    state.decls.push((id.clone(), air::ast_util::bv_typ(width)));
    let arb = Arc::new(ExprX::Var(id));
    Ok(BvExpr { expr: mk_ite(bool_condition, &arb, &exp.expr), bv_typ: exp.bv_typ })
}

impl State {
    fn fresh_id(&mut self) -> Ident {
        let idx = self.id_idx;
        self.id_idx += 1;
        let id =
            VarIdent(Arc::new("tmp".to_string()), VarIdentDisambiguate::BitVectorToAirDecl(idx));
        suffix_local_unique_id(&id)
    }
}
