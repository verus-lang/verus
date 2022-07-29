use crate::ast::{
    ArithOp, AssertQueryMode, BinaryOp, BitwiseOp, FieldOpr, Fun, Ident, Idents, InequalityOp,
    IntRange, InvAtomicity, MaskSpec, Mode, Params, Path, PathX, SpannedTyped, Typ, TypX, Typs,
    UnaryOp, UnaryOpr, VarAt, VirErr, Visibility,
};
use crate::ast_util::{
    allowed_bitvector_type, bitwidth_from_type, err_string, fun_as_rust_dbg, get_field, get_variant,
};
use crate::context::Ctx;
use crate::def::{fn_inv_name, fn_namespace_name, new_user_qid_name};
use crate::def::{
    fun_to_string, new_internal_qid, path_to_string, prefix_box, prefix_ensures, prefix_fuel_id,
    prefix_lambda_type, prefix_pre_var, prefix_requires, prefix_unbox, snapshot_ident,
    suffix_global_id, suffix_local_expr_id, suffix_local_stmt_id, suffix_local_unique_id,
    suffix_typ_param_id, unique_local, variant_field_ident, variant_ident, ProverChoice, SnapPos,
    SpanKind, Spanned, FUEL_BOOL, FUEL_BOOL_DEFAULT, FUEL_DEFAULTS, FUEL_ID, FUEL_PARAM, FUEL_TYPE,
    POLY, SNAPSHOT_ASSIGN, SNAPSHOT_CALL, SNAPSHOT_PRE, SUCC, SUFFIX_SNAP_JOIN, SUFFIX_SNAP_MUT,
    SUFFIX_SNAP_WHILE_BEGIN, SUFFIX_SNAP_WHILE_END,
};
use crate::def::{CommandsWithContext, CommandsWithContextX};
use crate::inv_masks::MaskSet;
use crate::poly::{typ_as_mono, MonoTyp, MonoTypX};
use crate::sst::{BndInfo, BndX, Dest, Exp, ExpX, LocalDecl, Stm, StmX, UniqueIdent};
use crate::sst_vars::{get_loc_var, AssignMap};
use crate::util::{vec_map, vec_map_result};
use air::ast::{
    BindX, Binder, BinderX, Binders, CommandX, Constant, Decl, DeclX, Expr, ExprX, MultiOp, Qid,
    Quant, QueryX, Span, Stmt, StmtX, Trigger, Triggers,
};
use air::ast_util::{
    bool_typ, bv_typ, ident_apply, ident_binder, ident_typ, ident_var, int_typ, mk_and,
    mk_bind_expr, mk_bitvector_option, mk_eq, mk_exists, mk_implies, mk_ite, mk_let, mk_not,
    mk_option_command, mk_or, mk_xor, str_apply, str_ident, str_typ, str_var, string_var,
};
use air::errors::{error, error_with_label};
use std::collections::{BTreeMap, HashMap, HashSet};
use std::mem::swap;
use std::sync::Arc;

#[inline(always)]
pub(crate) fn fun_to_air_ident(fun: &Fun) -> Ident {
    Arc::new(fun_to_string(fun))
}

#[inline(always)]
pub(crate) fn path_to_air_ident(path: &Path) -> Ident {
    Arc::new(path_to_string(path))
}

pub(crate) fn apply_range_fun(name: &str, range: &IntRange, exprs: Vec<Expr>) -> Expr {
    let mut args = exprs;
    match range {
        IntRange::Int | IntRange::Nat => {}
        IntRange::U(range) | IntRange::I(range) => {
            let bits = Constant::Nat(Arc::new(range.to_string()));
            args.insert(0, Arc::new(ExprX::Const(bits)));
        }
        IntRange::USize | IntRange::ISize => {
            args.insert(0, str_var(crate::def::ARCH_SIZE));
        }
    }
    str_apply(name, &args)
}

pub(crate) fn monotyp_to_path(typ: &MonoTyp) -> Path {
    let id = match &**typ {
        MonoTypX::Bool => str_ident("bool"),
        MonoTypX::Int(range) => match range {
            IntRange::Int => str_ident("int"),
            IntRange::Nat => str_ident("nat"),
            IntRange::U(n) => Arc::new(format!("u{}", n)),
            IntRange::I(n) => Arc::new(format!("i{}", n)),
            IntRange::USize => str_ident("usize"),
            IntRange::ISize => str_ident("isize"),
        },
        MonoTypX::Datatype(path, typs) => {
            return crate::def::monotyp_apply(path, &typs.iter().map(monotyp_to_path).collect());
        }
    };
    Arc::new(PathX { krate: None, segments: Arc::new(vec![id]) })
}

pub(crate) fn typ_to_air(ctx: &Ctx, typ: &Typ) -> air::ast::Typ {
    match &**typ {
        TypX::Int(_) => int_typ(),
        TypX::Bool => bool_typ(),
        TypX::Tuple(_) => panic!("internal error: Tuple should have been removed by ast_simplify"),
        TypX::Lambda(..) => Arc::new(air::ast::TypX::Lambda),
        TypX::Datatype(path, _) => {
            if ctx.datatype_is_transparent[path] {
                ident_typ(&path_to_air_ident(path))
            } else {
                match typ_as_mono(typ) {
                    None => panic!("abstract datatype should be boxed"),
                    Some(monotyp) => ident_typ(&path_to_air_ident(&monotyp_to_path(&monotyp))),
                }
            }
        }
        TypX::Boxed(_) => str_typ(POLY),
        TypX::TypParam(_) => str_typ(POLY),
        TypX::TypeId => str_typ(crate::def::TYPE),
        TypX::Air(t) => t.clone(),
    }
}

pub fn range_to_id(range: &IntRange) -> Expr {
    match range {
        IntRange::Int => str_var(crate::def::TYPE_ID_INT),
        IntRange::Nat => str_var(crate::def::TYPE_ID_NAT),
        IntRange::U(_) | IntRange::USize => {
            apply_range_fun(crate::def::TYPE_ID_UINT, range, vec![])
        }
        IntRange::I(_) | IntRange::ISize => {
            apply_range_fun(crate::def::TYPE_ID_SINT, range, vec![])
        }
    }
}

pub fn monotyp_to_id(typ: &MonoTyp) -> Expr {
    match &**typ {
        MonoTypX::Int(range) => range_to_id(range),
        MonoTypX::Bool => str_var(crate::def::TYPE_ID_BOOL),
        MonoTypX::Datatype(path, typs) => {
            let f_name = crate::def::prefix_type_id(path);
            air::ast_util::ident_apply_or_var(&f_name, &Arc::new(vec_map(&**typs, monotyp_to_id)))
        }
    }
}

// SMT-level type identifiers.
// We currently rely on these type identifiers for:
// 1) Axioms about unboxing integer refinement types (nat, u8, etc.)
// 2) The box(unbox(x)) == x axiom
pub fn typ_to_id(typ: &Typ) -> Expr {
    match &**typ {
        TypX::Int(range) => range_to_id(range),
        TypX::Bool => str_var(crate::def::TYPE_ID_BOOL),
        TypX::Tuple(_) => panic!("internal error: Tuple should have been removed by ast_simplify"),
        TypX::Lambda(typs, typ) => fun_id(typs, typ),
        TypX::Datatype(path, typs) => datatype_id(path, typs),
        TypX::Boxed(typ) => typ_to_id(typ),
        TypX::TypParam(x) => ident_var(&suffix_typ_param_id(x)),
        TypX::TypeId => panic!("internal error: typ_to_id of TypeId"),
        TypX::Air(_) => panic!("internal error: typ_to_id of Air"),
    }
}

pub(crate) fn fun_id(typs: &Typs, typ: &Typ) -> Expr {
    let f_name = crate::def::prefix_type_id_fun(typs.len());
    let mut typids: Vec<Expr> = vec_map(&**typs, typ_to_id);
    typids.push(typ_to_id(typ));
    air::ast_util::ident_apply_or_var(&f_name, &Arc::new(typids))
}

pub(crate) fn datatype_id(path: &Path, typs: &Typs) -> Expr {
    let f_name = crate::def::prefix_type_id(path);
    air::ast_util::ident_apply_or_var(&f_name, &Arc::new(vec_map(&**typs, typ_to_id)))
}

pub(crate) fn datatype_has_type(path: &Path, typs: &Typs, expr: &Expr) -> Expr {
    str_apply(crate::def::HAS_TYPE, &vec![expr.clone(), datatype_id(path, typs)])
}

pub(crate) fn expr_has_type(id: &Expr, expr: &Expr) -> Expr {
    str_apply(crate::def::HAS_TYPE, &vec![expr.clone(), id.clone()])
}

// If expr has type typ, what can we assume to be true about expr?
// For refinement types, transparent datatypes potentially containing refinement types,
// abstract types applied to type variables,
// and type variables potentially instantiated with refinement types, return Some invariant.
// For non-refinement types and abstract monotypes, return None,
// since the SMT sorts for these types can express the types precisely with no need for refinement.
pub(crate) fn typ_invariant(ctx: &Ctx, typ: &Typ, expr: &Expr) -> Option<Expr> {
    // Should be kept in sync with vir::context::datatypes_invs
    match &**typ {
        TypX::Int(IntRange::Int) => None,
        TypX::Int(IntRange::Nat) => {
            let zero = Arc::new(ExprX::Const(Constant::Nat(Arc::new("0".to_string()))));
            Some(Arc::new(ExprX::Binary(air::ast::BinaryOp::Le, zero, expr.clone())))
        }
        TypX::Int(range) => {
            let f_name = match range {
                IntRange::Int => panic!("internal error: Int"),
                IntRange::Nat => panic!("internal error: Int"),
                IntRange::U(_) | IntRange::USize => crate::def::U_INV,
                IntRange::I(_) | IntRange::ISize => crate::def::I_INV,
            };
            Some(apply_range_fun(&f_name, &range, vec![expr.clone()]))
        }
        TypX::Lambda(..) => Some(str_apply(
            crate::def::HAS_TYPE,
            &vec![try_box(ctx, expr.clone(), typ).expect("try_box lambda"), typ_to_id(typ)],
        )),
        TypX::Datatype(path, typs) => {
            if ctx.datatype_is_transparent[path] {
                if ctx.datatypes_with_invariant.contains(path) {
                    let box_expr = ident_apply(&prefix_box(&path), &vec![expr.clone()]);
                    Some(datatype_has_type(path, typs, &box_expr))
                } else {
                    None
                }
            } else {
                if typ_as_mono(typ).is_none() {
                    panic!("abstract datatype should be boxed")
                } else {
                    None
                }
            }
        }
        TypX::Boxed(t) => Some(str_apply(crate::def::HAS_TYPE, &vec![expr.clone(), typ_to_id(t)])),
        TypX::TypParam(x) => Some(str_apply(
            crate::def::HAS_TYPE,
            &vec![expr.clone(), ident_var(&suffix_typ_param_id(&x))],
        )),
        _ => None,
    }
}

fn try_box(ctx: &Ctx, expr: Expr, typ: &Typ) -> Option<Expr> {
    let f_name = match &**typ {
        TypX::Bool => Some(str_ident(crate::def::BOX_BOOL)),
        TypX::Int(_) => Some(str_ident(crate::def::BOX_INT)),
        TypX::Tuple(_) => None,
        TypX::Lambda(typs, _) => Some(prefix_box(&prefix_lambda_type(typs.len()))),
        TypX::Datatype(path, _) => {
            if ctx.datatype_is_transparent[path] {
                Some(prefix_box(&path))
            } else {
                if let Some(monotyp) = typ_as_mono(typ) {
                    let dpath = crate::sst_to_air::monotyp_to_path(&monotyp);
                    Some(prefix_box(&dpath))
                } else {
                    panic!("abstract datatype should be boxed")
                }
            }
        }
        TypX::Boxed(_) => None,
        TypX::TypParam(_) => None,
        TypX::TypeId => None,
        TypX::Air(_) => None,
    };
    f_name.map(|f_name| ident_apply(&f_name, &vec![expr]))
}

fn try_unbox(ctx: &Ctx, expr: Expr, typ: &Typ) -> Option<Expr> {
    let f_name = match &**typ {
        TypX::Bool => Some(str_ident(crate::def::UNBOX_BOOL)),
        TypX::Int(_) => Some(str_ident(crate::def::UNBOX_INT)),
        TypX::Datatype(path, _) => {
            if ctx.datatype_is_transparent[path] {
                Some(prefix_unbox(&path))
            } else {
                if let Some(monotyp) = typ_as_mono(typ) {
                    let dpath = crate::sst_to_air::monotyp_to_path(&monotyp);
                    Some(prefix_unbox(&dpath))
                } else {
                    panic!("abstract datatype should stay boxed")
                }
            }
        }
        TypX::Tuple(_) => None,
        TypX::Lambda(typs, _) => Some(prefix_unbox(&prefix_lambda_type(typs.len()))),
        TypX::Boxed(_) => None,
        TypX::TypParam(_) => None,
        TypX::TypeId => None,
        TypX::Air(_) => None,
    };
    f_name.map(|f_name| ident_apply(&f_name, &vec![expr]))
}

fn call_inv(ctx: &Ctx, outer: Expr, inner: Expr, typ: &Typ, atomicity: InvAtomicity) -> Expr {
    let inv_fn_ident = suffix_global_id(&fun_to_air_ident(&fn_inv_name(atomicity)));
    let typ_expr = typ_to_id(typ);
    let boxed_inner = try_box(ctx, inner.clone(), typ).unwrap_or(inner);
    let args = vec![typ_expr, outer, boxed_inner];
    ident_apply(&inv_fn_ident, &args)
}

fn call_namespace(arg: Expr, typ: &Typ, atomicity: InvAtomicity) -> Expr {
    let inv_fn_ident = suffix_global_id(&fun_to_air_ident(&fn_namespace_name(atomicity)));
    let typ_expr = typ_to_id(typ);
    let args = vec![typ_expr, arg];
    ident_apply(&inv_fn_ident, &args)
}

pub fn mask_set_from_spec(spec: &MaskSpec, mode: Mode) -> MaskSet {
    match spec {
        MaskSpec::NoSpec => {
            // By default, we assume an #[exec] fn can open any invariant, and that
            // a #[proof] fn can open no invariants.
            if mode == Mode::Exec { MaskSet::full() } else { MaskSet::empty() }
        }
        MaskSpec::InvariantOpens(exprs) if exprs.len() == 0 => MaskSet::empty(),
        MaskSpec::InvariantOpensExcept(exprs) if exprs.len() == 0 => MaskSet::full(),
        MaskSpec::InvariantOpens(_exprs) | MaskSpec::InvariantOpensExcept(_exprs) => {
            panic!("custom mask specs are not yet implemented");
        }
    }
}

pub(crate) fn ctor_to_apply<'a>(
    ctx: &'a Ctx,
    path: &Path,
    variant: &Ident,
    binders: &'a Binders<Exp>,
) -> (Ident, impl Iterator<Item = &'a Arc<BinderX<Exp>>>) {
    let fields = &get_variant(&ctx.global.datatypes[path], variant).a;
    (variant_ident(path, &variant), fields.iter().map(move |f| get_field(binders, &f.name)))
}

pub(crate) fn constant_to_expr(_ctx: &Ctx, constant: &crate::ast::Constant) -> Expr {
    match constant {
        crate::ast::Constant::Bool(b) => Arc::new(ExprX::Const(Constant::Bool(*b))),
        crate::ast::Constant::Nat(s) => Arc::new(ExprX::Const(Constant::Nat(s.clone()))),
    }
}

#[derive(Debug, PartialEq, Eq, Clone, Copy)]
pub(crate) enum ExprMode {
    Spec,
    Body,
    BodyPre,
}

#[derive(Debug, Clone)]
pub(crate) struct ExprCtxt {
    pub mode: ExprMode,
    pub is_bit_vector: bool,
    pub bit_vector_typ_hint: Option<Typ>,
}

impl ExprCtxt {
    pub(crate) fn new() -> Self {
        ExprCtxt { mode: ExprMode::Body, is_bit_vector: false, bit_vector_typ_hint: None }
    }
    pub(crate) fn new_mode(mode: ExprMode) -> Self {
        ExprCtxt { mode, is_bit_vector: false, bit_vector_typ_hint: None }
    }
    pub(crate) fn new_mode_bv(mode: ExprMode, is_bit_vector: bool) -> Self {
        ExprCtxt { mode, is_bit_vector, bit_vector_typ_hint: None }
    }
    fn set_bit_vector_typ_hint(&self, bit_vector_typ_hint: Option<Typ>) -> Self {
        ExprCtxt { mode: self.mode, is_bit_vector: self.is_bit_vector, bit_vector_typ_hint }
    }
}

pub(crate) fn bv_typ_to_air(typ: &Typ) -> Option<air::ast::Typ> {
    match &**typ {
        TypX::Int(IntRange::U(size) | IntRange::I(size)) => Some(bv_typ(*size)),
        TypX::Bool => Some(bool_typ()),
        TypX::Boxed(t) => bv_typ_to_air(t),
        _ => None,
    }
}

fn clip_bitwise_result(bit_expr: ExprX, exp: &Exp) -> Result<Expr, VirErr> {
    if let TypX::Int(range) = &*exp.typ {
        match range {
            IntRange::I(_) | IntRange::ISize => {
                return Ok(apply_range_fun(&crate::def::I_CLIP, &range, vec![Arc::new(bit_expr)]));
            }
            IntRange::U(_) | IntRange::USize => {
                return Ok(apply_range_fun(&crate::def::U_CLIP, &range, vec![Arc::new(bit_expr)]));
            }
            _ => return Ok(Arc::new(bit_expr)),
        };
    } else {
        return err_string(
            &exp.span,
            format!("In translating Bitwise operator, encountered non-integer operand",),
        );
    }
}

fn check_unsigned(exp: &Exp) -> Result<(), VirErr> {
    if let TypX::Int(range) = &*exp.typ {
        match range {
            IntRange::I(_) | IntRange::ISize => {
                return err_string(
                    &exp.span,
                    format!("error: signed integer is not supported for bit-vector reasoning",),
                );
            }
            _ => (),
        }
    };
    Ok(())
}

// Generate a unique quantifier ID and map it to the quantifier's span
fn new_user_qid(ctx: &Ctx, exp: &Exp) -> Qid {
    let fun_name = fun_as_rust_dbg(
        &ctx.fun.as_ref().expect("Expressions are expected to be within a function").current_fun,
    );
    let qcount = ctx.quantifier_count.get();
    let qid = new_user_qid_name(&fun_name, qcount);
    ctx.quantifier_count.set(qcount + 1);
    let trigs = match &exp.x {
        ExpX::Bind(bnd, _) => match &bnd.x {
            BndX::Quant(_, _, trigs) => trigs,
            BndX::Choose(_, trigs, _) => trigs,
            _ => panic!(
                "internal error: user quantifier expressions should only be Quant or Choose; found {:?}",
                bnd.x
            ),
        },
        _ => panic!(
            "internal error: user quantifier expressions should only be Bind expressions; found {:?}",
            exp.x
        ),
    };
    let bnd_info = BndInfo { span: exp.span.clone(), trigs: trigs.clone() };
    ctx.global.qid_map.borrow_mut().insert(qid.clone(), bnd_info);
    Some(Arc::new(qid))
}

pub(crate) fn exp_to_expr(ctx: &Ctx, exp: &Exp, expr_ctxt: &ExprCtxt) -> Result<Expr, VirErr> {
    let bit_vector_typ_hint = &expr_ctxt.bit_vector_typ_hint;
    let expr_ctxt = &expr_ctxt.set_bit_vector_typ_hint(None);
    let result = match (&exp.x, expr_ctxt.is_bit_vector) {
        (ExpX::Const(crate::ast::Constant::Nat(s)), true) => {
            let typ = match (&*exp.typ, bit_vector_typ_hint) {
                (TypX::Int(IntRange::Int | IntRange::Nat), Some(hint))
                    if crate::ast_util::fixed_integer_const(s, hint) =>
                {
                    hint
                }
                _ => &exp.typ,
            };
            if let Some(width) = bitwidth_from_type(typ) {
                return Ok(Arc::new(ExprX::Const(Constant::BitVec(s.clone(), width))));
            }
            return err_string(
                &exp.span,
                format!("error: unable to get bit-width from constant of type {:?}", exp.typ),
            );
        }
        (ExpX::Const(c), _) => {
            let expr = constant_to_expr(ctx, c);
            expr
        }
        (ExpX::Var(x), _) => string_var(&suffix_local_unique_id(x)),
        (ExpX::VarLoc(x), false) => string_var(&suffix_local_unique_id(x)),
        (ExpX::VarAt(x, VarAt::Pre), false) => match expr_ctxt.mode {
            ExprMode::Spec => string_var(&prefix_pre_var(&suffix_local_unique_id(x))),
            ExprMode::Body => {
                Arc::new(ExprX::Old(snapshot_ident(SNAPSHOT_PRE), suffix_local_unique_id(x)))
            }
            ExprMode::BodyPre => string_var(&suffix_local_unique_id(x)),
        },
        (ExpX::Loc(e0), false) => exp_to_expr(ctx, e0, expr_ctxt)?,
        (ExpX::Old(span, x), false) => {
            Arc::new(ExprX::Old(span.clone(), suffix_local_unique_id(x)))
        }
        (ExpX::Call(x, typs, args), false) => {
            let name = suffix_global_id(&fun_to_air_ident(&x));
            let mut exprs: Vec<Expr> = vec_map(typs, typ_to_id);
            for arg in args.iter() {
                exprs.push(exp_to_expr(ctx, arg, expr_ctxt)?);
            }
            ident_apply(&name, &exprs)
        }
        (ExpX::CallLambda(typ, e0, args), false) => {
            let e0 = exp_to_expr(ctx, e0, expr_ctxt)?;
            let args = vec_map_result(args, |e| exp_to_expr(ctx, e, expr_ctxt))?;
            Arc::new(ExprX::ApplyLambda(typ_to_air(ctx, typ), e0, Arc::new(args)))
        }
        (ExpX::Ctor(path, variant, binders), false) => {
            let (variant, args) = ctor_to_apply(ctx, path, variant, binders);
            let args = args
                .map(|b| exp_to_expr(ctx, &b.a, expr_ctxt))
                .collect::<Result<Vec<_>, VirErr>>()?;
            Arc::new(ExprX::Apply(variant, Arc::new(args)))
        }
        (ExpX::Unary(op, exp), true) => {
            if !allowed_bitvector_type(&exp.typ) {
                return err_string(
                    &exp.span,
                    format!("error: cannot use bit-vector arithmetic on type {:?}", exp.typ),
                );
            }
            let hint = match op {
                UnaryOp::BitNot => expr_ctxt.bit_vector_typ_hint.clone(),
                UnaryOp::Clip(range @ (IntRange::U(..) | IntRange::I(..))) => {
                    Some(Arc::new(TypX::Int(*range)))
                }
                _ => None,
            };
            let expr_ctxt = &expr_ctxt.set_bit_vector_typ_hint(hint);
            let bv_e = exp_to_expr(ctx, exp, expr_ctxt)?;
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
                UnaryOp::Clip(IntRange::U(new_n) | IntRange::I(new_n)) => {
                    match &*exp.typ {
                        TypX::Int(IntRange::U(old_n) | IntRange::I(old_n)) => {
                            // expand with zero using concat
                            if new_n > old_n {
                                let bop = air::ast::BinaryOp::BitConcat;
                                let zero_pad = Arc::new(ExprX::Const(Constant::BitVec(
                                    Arc::new("0".to_string()),
                                    new_n - old_n,
                                )));
                                return Ok(Arc::new(ExprX::Binary(bop, zero_pad, bv_e)));
                            }
                            // extract lower new_n bits
                            else if new_n < old_n {
                                let op = air::ast::UnaryOp::BitExtract(new_n - 1, 0);
                                return Ok(Arc::new(ExprX::Unary(op, bv_e)));
                            } else {
                                return Ok(bv_e);
                            }
                        }
                        _ => {
                            return err_string(
                                &exp.span,
                                format!(
                                    "IntRange error: should be I(_) or U(_) for bit-vector, got {:?}",
                                    exp.typ
                                ),
                            );
                        }
                    }
                }
                UnaryOp::Clip(_) => {
                    return err_string(
                        &exp.span,
                        format!(
                            "IntRange error: should be I(_) or U(_) for bit-vector, got {:?}",
                            exp.typ
                        ),
                    );
                }
                UnaryOp::Trigger(_) => exp_to_expr(ctx, exp, expr_ctxt)?,
                UnaryOp::CoerceMode { .. } => {
                    panic!("internal error: TupleField should have been removed before here")
                }
                UnaryOp::MustBeFinalized => {
                    panic!("internal error: Exp not finalized: {:?}", exp)
                }
            }
        }
        (ExpX::Unary(op, exp), false) => match op {
            UnaryOp::Not => mk_not(&exp_to_expr(ctx, exp, expr_ctxt)?),
            UnaryOp::BitNot => {
                let width = match bitwidth_from_type(&exp.typ) {
                    Some(w) => w,
                    None => {
                        return err_string(
                            &exp.span,
                            format!("error: unable to get bit-width from type {:?}", exp.typ),
                        );
                    }
                };
                let width_exp = Arc::new(ExprX::Const(Constant::Nat(Arc::new(width.to_string()))));
                let expr = exp_to_expr(ctx, exp, expr_ctxt)?;
                let expr = try_box(ctx, expr, &exp.typ).expect("Box");
                let bit_expr = ExprX::Apply(
                    Arc::new(crate::def::UINT_NOT.to_string()),
                    Arc::new(vec![width_exp, expr]),
                );
                clip_bitwise_result(bit_expr, exp)?
            }
            UnaryOp::Trigger(_) => exp_to_expr(ctx, exp, expr_ctxt)?,
            UnaryOp::Clip(IntRange::Int) => exp_to_expr(ctx, exp, expr_ctxt)?,
            UnaryOp::Clip(range) => {
                let expr = exp_to_expr(ctx, exp, expr_ctxt)?;
                let f_name = match range {
                    IntRange::Int => panic!("internal error: Int"),
                    IntRange::Nat => crate::def::NAT_CLIP,
                    IntRange::U(_) | IntRange::USize => crate::def::U_CLIP,
                    IntRange::I(_) | IntRange::ISize => crate::def::I_CLIP,
                };
                apply_range_fun(&f_name, &range, vec![expr])
            }
            UnaryOp::CoerceMode { .. } => {
                panic!("internal error: TupleField should have been removed before here")
            }
            UnaryOp::MustBeFinalized => {
                panic!("internal error: Exp not finalized: {:?}", exp)
            }
        },
        (ExpX::UnaryOpr(UnaryOpr::Box(_) | UnaryOpr::Unbox(_), exp), true) => {
            exp_to_expr(ctx, exp, expr_ctxt)?
        }
        (ExpX::UnaryOpr(op, exp), false) => match op {
            UnaryOpr::Box(typ) => {
                let expr = exp_to_expr(ctx, exp, expr_ctxt)?;
                try_box(ctx, expr, typ).expect("Box")
            }
            UnaryOpr::Unbox(typ) => {
                let expr = exp_to_expr(ctx, exp, expr_ctxt)?;
                try_unbox(ctx, expr, typ).expect("Unbox")
            }
            UnaryOpr::HasType(typ) => {
                let expr = exp_to_expr(ctx, exp, expr_ctxt)?;
                typ_invariant(ctx, typ, &expr).expect("HasType")
            }
            UnaryOpr::IsVariant { datatype, variant } => {
                let expr = exp_to_expr(ctx, exp, expr_ctxt)?;
                let name = Arc::new(format!("is-{}", variant_ident(datatype, variant)));
                Arc::new(ExprX::Apply(name, Arc::new(vec![expr])))
            }
            UnaryOpr::TupleField { .. } => {
                panic!("internal error: TupleField should have been removed before here")
            }
            UnaryOpr::Field(FieldOpr { datatype, variant, field }) => {
                let expr = exp_to_expr(ctx, exp, expr_ctxt)?;
                Arc::new(ExprX::Apply(
                    variant_field_ident(datatype, variant, field),
                    Arc::new(vec![expr]),
                ))
            }
        },
        (ExpX::Binary(op, lhs, rhs), true) => {
            if !allowed_bitvector_type(&exp.typ) {
                return err_string(
                    &exp.span,
                    format!("error: cannot use bit-vector arithmetic on type {:?}", exp.typ),
                );
            }
            // disallow signed integer from bitvec reasoning. However, allow that for shift
            // TODO: sanity check for shift
            let _ = match op {
                BinaryOp::Bitwise(BitwiseOp::Shl | BitwiseOp::Shr) => (),
                _ => {
                    check_unsigned(&lhs)?;
                    check_unsigned(&rhs)?;
                }
            };
            let hint = match op {
                BinaryOp::Eq(..)
                | BinaryOp::Ne
                | BinaryOp::Inequality(..)
                | BinaryOp::Arith(..) => match (&*lhs.typ, &*rhs.typ) {
                    (TypX::Int(IntRange::U(..) | IntRange::I(..)), _) => Some(lhs.typ.clone()),
                    (_, TypX::Int(IntRange::U(..) | IntRange::I(..))) => Some(rhs.typ.clone()),
                    _ => None,
                },
                _ => None,
            };
            let expr_ctxt = &expr_ctxt.set_bit_vector_typ_hint(hint);
            let lh = exp_to_expr(ctx, lhs, expr_ctxt)?;
            let rh = exp_to_expr(ctx, rhs, expr_ctxt)?;
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
                BinaryOp::Bitwise(BitwiseOp::BitXor) => air::ast::BinaryOp::BitXor,
                BinaryOp::Bitwise(BitwiseOp::BitAnd) => air::ast::BinaryOp::BitAnd,
                BinaryOp::Bitwise(BitwiseOp::BitOr) => air::ast::BinaryOp::BitOr,
                BinaryOp::Bitwise(BitwiseOp::Shl) => air::ast::BinaryOp::Shl,
                BinaryOp::Bitwise(BitwiseOp::Shr) => air::ast::BinaryOp::LShr,
                BinaryOp::Implies => air::ast::BinaryOp::Implies,
                BinaryOp::And => unreachable!(),
                BinaryOp::Or => unreachable!(),
                BinaryOp::Xor => unreachable!(),
            };
            return Ok(Arc::new(ExprX::Binary(bop, lh, rh)));
        }
        (ExpX::Binary(op, lhs, rhs), false) => {
            let has_const = match (&lhs.x, &rhs.x) {
                (ExpX::Const(..), _) => true,
                (_, ExpX::Const(..)) => true,
                _ => false,
            };
            let lh = exp_to_expr(ctx, lhs, expr_ctxt)?;
            let rh = exp_to_expr(ctx, rhs, expr_ctxt)?;
            let expx = match op {
                BinaryOp::And => {
                    return Ok(mk_and(&vec![lh, rh]));
                }
                BinaryOp::Or => {
                    return Ok(mk_or(&vec![lh, rh]));
                }
                BinaryOp::Xor => {
                    return Ok(mk_xor(&lh, &rh));
                }
                BinaryOp::Implies => {
                    return Ok(mk_implies(&lh, &rh));
                }
                BinaryOp::Arith(ArithOp::Add, _) => {
                    ExprX::Multi(MultiOp::Add, Arc::new(vec![lh, rh]))
                }
                BinaryOp::Arith(ArithOp::Sub, _) => {
                    ExprX::Multi(MultiOp::Sub, Arc::new(vec![lh, rh]))
                }
                BinaryOp::Arith(ArithOp::Mul, _) if !has_const => {
                    return Ok(str_apply(crate::def::MUL, &vec![lh, rh]));
                }
                BinaryOp::Arith(ArithOp::EuclideanDiv, _) if !has_const => {
                    return Ok(str_apply(crate::def::EUC_DIV, &vec![lh, rh]));
                }
                BinaryOp::Arith(ArithOp::EuclideanMod, _) if !has_const => {
                    return Ok(str_apply(crate::def::EUC_MOD, &vec![lh, rh]));
                }
                BinaryOp::Arith(ArithOp::Mul, _) => {
                    ExprX::Multi(MultiOp::Mul, Arc::new(vec![lh, rh]))
                }
                BinaryOp::Ne => {
                    let eq = ExprX::Binary(air::ast::BinaryOp::Eq, lh, rh);
                    ExprX::Unary(air::ast::UnaryOp::Not, Arc::new(eq))
                }
                // here the binary bitvector Ops are translated into the integer versions
                // Similar to typ_invariant(), make obvious range according to bit-width
                BinaryOp::Bitwise(bo) => {
                    let box_lh = try_box(ctx, lh, &lhs.typ).expect("Box");
                    let box_rh = try_box(ctx, rh, &rhs.typ).expect("Box");
                    let width_left = match bitwidth_from_type(&lhs.typ) {
                        Some(w) => w,
                        None => {
                            return err_string(
                                &lhs.span,
                                format!("error: unable to get bit-width from type {:?}", lhs.typ),
                            );
                        }
                    };
                    let width_right = match bitwidth_from_type(&rhs.typ) {
                        Some(w) => w,
                        None => {
                            return err_string(
                                &rhs.span,
                                format!("error: unable to get bit-width from type {:?}", rhs.typ),
                            );
                        }
                    };
                    if width_left != width_right {
                        return err_string(
                            &exp.span,
                            format!(
                                "error: argument bit-width does not match. Left: {}, Right: {}",
                                width_left, width_right
                            ),
                        );
                    }
                    let width_exp =
                        Arc::new(ExprX::Const(Constant::Nat(Arc::new(width_left.to_string()))));
                    let fname = match bo {
                        BitwiseOp::BitXor => crate::def::UINT_XOR,
                        BitwiseOp::BitAnd => crate::def::UINT_AND,
                        BitwiseOp::BitOr => crate::def::UINT_OR,
                        BitwiseOp::Shl => crate::def::UINT_SHL,
                        BitwiseOp::Shr => crate::def::UINT_SHR,
                    };
                    let bit_expr = ExprX::Apply(
                        Arc::new(fname.to_string()),
                        Arc::new(vec![width_exp.clone(), box_lh, box_rh]),
                    );
                    return clip_bitwise_result(bit_expr, exp);
                }
                _ => {
                    let aop = match op {
                        BinaryOp::And => unreachable!(),
                        BinaryOp::Or => unreachable!(),
                        BinaryOp::Xor => unreachable!(),
                        BinaryOp::Implies => unreachable!(),
                        BinaryOp::Eq(_) => air::ast::BinaryOp::Eq,
                        BinaryOp::Ne => unreachable!(),
                        BinaryOp::Inequality(InequalityOp::Le) => air::ast::BinaryOp::Le,
                        BinaryOp::Inequality(InequalityOp::Lt) => air::ast::BinaryOp::Lt,
                        BinaryOp::Inequality(InequalityOp::Ge) => air::ast::BinaryOp::Ge,
                        BinaryOp::Inequality(InequalityOp::Gt) => air::ast::BinaryOp::Gt,
                        BinaryOp::Arith(ArithOp::Add, _) => unreachable!(),
                        BinaryOp::Arith(ArithOp::Sub, _) => unreachable!(),
                        BinaryOp::Arith(ArithOp::Mul, _) => unreachable!(),
                        BinaryOp::Arith(ArithOp::EuclideanDiv, _) => {
                            air::ast::BinaryOp::EuclideanDiv
                        }
                        BinaryOp::Arith(ArithOp::EuclideanMod, _) => {
                            air::ast::BinaryOp::EuclideanMod
                        }
                        BinaryOp::Bitwise(..) => unreachable!(),
                    };
                    ExprX::Binary(aop, lh, rh)
                }
            };
            Arc::new(expx)
        }
        (ExpX::If(e1, e2, e3), _) => mk_ite(
            &exp_to_expr(ctx, e1, expr_ctxt)?,
            &exp_to_expr(ctx, e2, expr_ctxt)?,
            &exp_to_expr(ctx, e3, expr_ctxt)?,
        ),
        (ExpX::WithTriggers(_triggers, body), _) => exp_to_expr(ctx, body, expr_ctxt)?,
        (ExpX::Bind(bnd, e), _) => match (&bnd.x, expr_ctxt.is_bit_vector) {
            (BndX::Let(binders), _) => {
                let expr = exp_to_expr(ctx, e, expr_ctxt)?;
                let binders =
                    vec_map_result(&*binders, |b| match exp_to_expr(ctx, &b.a, expr_ctxt) {
                        Ok(expr) => {
                            Ok(Arc::new(BinderX { name: suffix_local_expr_id(&b.name), a: expr }))
                        }
                        Err(vir_err) => Err(vir_err.clone()),
                    })?;
                air::ast_util::mk_let(&binders, &expr)
            }
            (BndX::Quant(quant, binders, trigs), _) => {
                let expr = exp_to_expr(ctx, e, expr_ctxt)?;
                let mut invs: Vec<Expr> = Vec::new();
                if !expr_ctxt.is_bit_vector {
                    for binder in binders.iter() {
                        let typ_inv = typ_invariant(
                            ctx,
                            &binder.a,
                            &ident_var(&suffix_local_expr_id(&binder.name)),
                        );
                        if let Some(inv) = typ_inv {
                            invs.push(inv);
                        }
                    }
                }
                let inv = mk_and(&invs);
                let expr = match quant.quant {
                    Quant::Forall => mk_implies(&inv, &expr),
                    Quant::Exists => mk_and(&vec![inv, expr]),
                };
                let binders = vec_map_result(&*binders, |b| {
                    let name = match &*b.a {
                        // allow quantifiers over type parameters, generated for broadcast_forall
                        TypX::TypeId => suffix_typ_param_id(&b.name),
                        _ => suffix_local_expr_id(&b.name),
                    };
                    let typ = if expr_ctxt.is_bit_vector {
                        let bv_typ_option = bv_typ_to_air(&b.a);
                        if bv_typ_option.is_none() {
                            return err_string(
                                &exp.span,
                                format!("unsupported type in bitvector {:?}", &b.a),
                            );
                        };
                        bv_typ_option.unwrap()
                    } else {
                        typ_to_air(ctx, &b.a)
                    };
                    Ok(Arc::new(BinderX { name, a: typ }))
                })?;
                let triggers = vec_map_result(&*trigs, |trig| {
                    vec_map_result(trig, |x| exp_to_expr(ctx, x, expr_ctxt)).map(|v| Arc::new(v))
                })?;
                let qid = new_user_qid(ctx, &exp);
                air::ast_util::mk_quantifier(quant.quant, &binders, &triggers, qid, &expr)
            }
            (BndX::Lambda(binders), false) => {
                let expr = exp_to_expr(ctx, e, expr_ctxt)?;
                let binders = vec_map(&*binders, |b| {
                    let name = suffix_local_expr_id(&b.name);
                    Arc::new(BinderX { name, a: typ_to_air(ctx, &b.a) })
                });
                let lambda = air::ast_util::mk_lambda(&binders, &expr);
                str_apply(crate::def::MK_FUN, &vec![lambda])
            }
            (BndX::Choose(binders, trigs, cond), false) => {
                let mut bs: Vec<Binder<air::ast::Typ>> = Vec::new();
                let mut invs: Vec<Expr> = Vec::new();
                for b in binders.iter() {
                    let name = suffix_local_expr_id(&b.name);
                    let typ_inv = typ_invariant(ctx, &b.a, &ident_var(&name));
                    if let Some(inv) = &typ_inv {
                        invs.push(inv.clone());
                    }
                    bs.push(Arc::new(BinderX { name, a: typ_to_air(ctx, &b.a) }));
                }
                let cond_expr = exp_to_expr(ctx, cond, expr_ctxt)?;
                let body_expr = exp_to_expr(ctx, e, expr_ctxt)?;
                invs.push(cond_expr.clone());
                let cond_expr = mk_and(&invs);
                let typ = &e.typ;
                let typ_inv = typ_invariant(ctx, typ, &body_expr);
                let triggers = vec_map_result(&*trigs, |trig| {
                    vec_map_result(trig, |x| exp_to_expr(ctx, x, expr_ctxt)).map(|v| Arc::new(v))
                })?;
                let binders = Arc::new(bs);
                let qid = new_user_qid(ctx, &exp);
                let bind = Arc::new(BindX::Choose(binders, Arc::new(triggers), qid, cond_expr));
                let mut choose_expr = Arc::new(ExprX::Bind(bind, body_expr));
                match typ_inv {
                    Some(_) => {
                        // use as_type to coerce expression to some value of the requested type,
                        // even if the choose expression is unsatisfiable
                        let id = typ_to_id(typ);
                        choose_expr = str_apply(crate::def::AS_TYPE, &vec![choose_expr, id]);
                    }
                    _ => {}
                }
                choose_expr
            }
            (_, true) => {
                return err_string(
                    &exp.span,
                    format!("unsupported for bit-vector: bind conversion, {:?} ", exp.x),
                );
            }
        },
        (_, true) => {
            return err_string(
                &exp.span,
                format!("unsupported for bit-vector: expression conversion {:?}", exp.x),
            );
        }
    };
    Ok(result)
}

struct State {
    local_shared: Vec<Decl>, // shared between all queries for a single function
    local_bv_shared: Vec<Decl>, // used in bv mode, fixed width uint variables have corresponding bv types
    commands: Vec<CommandsWithContext>,
    snapshot_count: u32, // Used to ensure unique Idents for each snapshot
    sids: Vec<Ident>, // a stack of snapshot ids, the top one should dominate the current position in the AST
    snap_map: Vec<(Span, SnapPos)>, // Maps each statement's span to the closest dominating snapshot's ID
    assign_map: AssignMap, // Maps Maps each statement's span to the assigned variables (that can potentially be queried)
    mask: MaskSet,         // set of invariants that are allowed to be opened
}

impl State {
    /// get the current sid (top of the scope stack)
    fn get_current_sid(&self) -> Ident {
        let last = self.sids.last().unwrap();
        last.clone()
    }

    /// copy the current sid into a new scope (when entering a block)
    fn push_scope(&mut self) {
        let sid = self.get_current_sid();
        self.sids.push(sid);
    }

    /// pop off the scope (when exiting a block)
    fn pop_scope(&mut self) {
        self.sids.pop();
    }

    fn get_new_sid(&mut self, suffix: &str) -> Ident {
        self.snapshot_count += 1;
        Arc::new(format!("{}{}", self.snapshot_count, suffix))
    }

    /// replace the current sid (without changing scope depth)
    fn update_current_sid(&mut self, suffix: &str) -> Ident {
        let sid = self.get_new_sid(suffix);
        self.sids.pop();
        self.sids.push(sid.clone());
        sid
    }

    // fn get_assigned_set(&self, stm: &Stm) -> HashSet<Arc<String>> {
    //     if let Some(s) = self.assign_map.get(&Arc::as_ptr(stm)) {
    //         return s.clone();
    //     }
    //     return HashSet::new();
    // }

    fn map_span(&mut self, stm: &Stm, kind: SpanKind) {
        let spos = SnapPos { snapshot_id: self.get_current_sid(), kind: kind };
        // let aset = self.get_assigned_set(stm);
        // println!("{:?} {:?}", stm.span, aset);
        self.snap_map.push((stm.span.clone(), spos));
    }
}

fn loc_is_var(e: &Exp) -> Option<&UniqueIdent> {
    match &e.x {
        ExpX::VarLoc(x) => Some(x),
        _ => None,
    }
}

fn assume_var(span: &Span, x: &UniqueIdent, exp: &Exp) -> Stm {
    let x_var = SpannedTyped::new(&span, &exp.typ, ExpX::Var(x.clone()));
    let eqx = ExpX::Binary(BinaryOp::Eq(Mode::Spec), x_var, exp.clone());
    let eq = SpannedTyped::new(&span, &Arc::new(TypX::Bool), eqx);
    Spanned::new(span.clone(), StmX::Assume(eq))
}

fn one_stmt(stmts: Vec<Stmt>) -> Stmt {
    if stmts.len() == 1 { stmts[0].clone() } else { Arc::new(StmtX::Block(Arc::new(stmts))) }
}

#[derive(Debug)]
struct LocFieldInfo<A> {
    base_typ: Typ,
    base_span: Span,
    a: A,
}

fn loc_to_field_path(loc: &Exp) -> (UniqueIdent, LocFieldInfo<Vec<FieldOpr>>) {
    let mut e: &Exp = loc;
    let mut fields = Vec::new();
    loop {
        match &e.x {
            ExpX::Loc(ee) => e = ee,
            ExpX::UnaryOpr(UnaryOpr::Box(_) | UnaryOpr::Unbox(_), ee) => e = ee,
            ExpX::VarLoc(x) => {
                fields.reverse();
                return (
                    x.clone(),
                    LocFieldInfo { base_typ: e.typ.clone(), base_span: e.span.clone(), a: fields },
                );
            }
            ExpX::UnaryOpr(UnaryOpr::Field(field), ee) => {
                fields.push(field.clone());
                e = ee;
            }
            _ => panic!("loc unexpected {:?}", e),
        }
    }
}

fn snapshotted_var_locs(arg: &Exp, snapshot_name: &str) -> Exp {
    crate::sst_visitor::map_exp_visitor(arg, &mut |e| match &e.x {
        ExpX::VarLoc(x) => {
            SpannedTyped::new(&e.span, &e.typ, ExpX::Old(snapshot_ident(snapshot_name), x.clone()))
        }
        _ => e.clone(),
    })
}

fn snapshotted_vars(arg: &Exp, snapshot_name: &str) -> Exp {
    crate::sst_visitor::map_exp_visitor(arg, &mut |e| match &e.x {
        ExpX::Var(x) => {
            SpannedTyped::new(&e.span, &e.typ, ExpX::Old(snapshot_ident(snapshot_name), x.clone()))
        }
        _ => e.clone(),
    })
}

fn assume_other_fields_unchanged(
    ctx: &Ctx,
    snapshot_name: &str,
    stm_span: &Span,
    base: &UniqueIdent,
    mutated_fields: &LocFieldInfo<Vec<Vec<FieldOpr>>>,
    expr_ctxt: &ExprCtxt,
) -> Result<Option<Stmt>, VirErr> {
    let LocFieldInfo { base_typ, base_span, a: updates } = mutated_fields;
    let base_exp = SpannedTyped::new(base_span, base_typ, ExpX::VarLoc(base.clone()));
    let eqs = assume_other_fields_unchanged_inner(
        ctx,
        snapshot_name,
        stm_span,
        &base_exp,
        updates,
        expr_ctxt,
    )?;
    Ok((eqs.len() > 0)
        .then(|| Arc::new(StmtX::Assume(Arc::new(ExprX::Multi(MultiOp::And, Arc::new(eqs)))))))
}

fn assume_other_fields_unchanged_inner(
    ctx: &Ctx,
    snapshot_name: &str,
    stm_span: &Span,
    base: &Exp,
    updates: &Vec<Vec<FieldOpr>>,
    expr_ctxt: &ExprCtxt,
) -> Result<Vec<Expr>, VirErr> {
    match &updates[..] {
        [f] if f.len() == 0 => Ok(vec![]),
        _ => {
            let mut updated_fields: BTreeMap<_, Vec<_>> = BTreeMap::new();
            let FieldOpr { datatype, variant, field: _ } = &updates[0][0];
            for u in updates {
                assert!(u[0].datatype == *datatype && u[0].variant == *variant);
                updated_fields.entry(&u[0].field).or_insert(Vec::new()).push(u[1..].to_vec());
            }
            let datatype_fields = &get_variant(&ctx.global.datatypes[datatype], variant).a;
            let dt =
                vec_map_result(&**datatype_fields, |field: &Binder<(Typ, Mode, Visibility)>| {
                    let field_exp = SpannedTyped::new(
                        stm_span,
                        &field.a.0,
                        ExpX::UnaryOpr(
                            UnaryOpr::Field(FieldOpr {
                                datatype: datatype.clone(),
                                variant: variant.clone(),
                                field: field.name.clone(),
                            }),
                            base.clone(),
                        ),
                    );
                    if let Some(further_updates) = updated_fields.get(&field.name) {
                        assume_other_fields_unchanged_inner(
                            ctx,
                            snapshot_name,
                            stm_span,
                            &field_exp,
                            further_updates,
                            expr_ctxt,
                        )
                    } else {
                        let old = exp_to_expr(
                            ctx,
                            &snapshotted_var_locs(&field_exp, snapshot_name),
                            expr_ctxt,
                        )?;
                        let new = exp_to_expr(ctx, &field_exp, expr_ctxt)?;
                        Ok(vec![Arc::new(ExprX::Binary(air::ast::BinaryOp::Eq, old, new))])
                    }
                })?;
            Ok(dt.into_iter().flatten().collect())
        }
    }
}

// fn stm_to_stmts(ctx: &Ctx, state: &mut State, stm: &Stm) -> Result<Vec<Stmt>, VirErr> {
//     let expr_ctxt = ExprCtxt { mode: ExprMode::Body, is_bit_vector: false };
//     let result = match &stm.x {

fn stm_to_stmts(ctx: &Ctx, state: &mut State, stm: &Stm) -> Result<Vec<Stmt>, VirErr> {
    let expr_ctxt = &ExprCtxt::new();
    let result = match &stm.x {
        StmX::Call(x, mode, typs, args, dest) => {
            let mut stmts: Vec<Stmt> = Vec::new();
            let func = &ctx.func_map[x];
            if func.x.require.len() > 0 && (!ctx.checking_recommends() || *mode == Mode::Spec) {
                let f_req = prefix_requires(&fun_to_air_ident(&func.x.name));
                let mut req_args = vec_map(typs, typ_to_id);
                for arg in args.iter() {
                    req_args.push(exp_to_expr(ctx, arg, expr_ctxt)?);
                }
                let e_req = Arc::new(ExprX::Apply(f_req, Arc::new(req_args)));
                let description = match (ctx.checking_recommends(), &func.x.attrs.custom_req_err) {
                    (true, None) => "recommendation not met".to_string(),
                    (_, None) => "precondition not satisfied".to_string(),
                    (_, Some(s)) => s.clone(),
                };
                let error = error(description, &stm.span);
                stmts.push(Arc::new(StmtX::Assert(error, e_req)));
            }

            let callee_mask_set = mask_set_from_spec(&func.x.mask_spec, func.x.mode);
            callee_mask_set.assert_is_contained_in(&state.mask, &stm.span, &mut stmts);

            let typ_args: Vec<Expr> = vec_map(typs, typ_to_id);
            if func.x.params.iter().any(|p| p.x.is_mut) && ctx.debug {
                unimplemented!("&mut args are unsupported in debugger mode");
            }
            let mut call_snapshot = false;
            let mut ens_args_wo_typ = Vec::new();
            let mut mutated_fields: BTreeMap<_, LocFieldInfo<Vec<_>>> = BTreeMap::new();
            for (param, arg) in func.x.params.iter().zip(args.iter()) {
                let arg_x = if let Some(Dest { dest, is_init: _ }) = dest {
                    let var: UniqueIdent = get_loc_var(dest);
                    crate::sst_visitor::map_exp_visitor(arg, &mut |e| match &e.x {
                        ExpX::Var(x) if *x == var => {
                            call_snapshot = true;
                            SpannedTyped::new(
                                &e.span,
                                &e.typ,
                                ExpX::Old(snapshot_ident(SNAPSHOT_CALL), x.clone()),
                            )
                        }
                        _ => e.clone(),
                    })
                } else {
                    arg.clone()
                };
                if param.x.is_mut {
                    call_snapshot = true;
                    let (base_var, LocFieldInfo { base_typ, base_span, a: fields }) =
                        loc_to_field_path(arg);
                    mutated_fields
                        .entry(base_var)
                        .or_insert(LocFieldInfo { base_typ, base_span, a: Vec::new() })
                        .a
                        .push(fields);
                    let arg_old = snapshotted_var_locs(arg, SNAPSHOT_CALL);
                    ens_args_wo_typ.push(exp_to_expr(ctx, &arg_old, expr_ctxt)?);
                    ens_args_wo_typ.push(exp_to_expr(ctx, &arg_x, expr_ctxt)?);
                } else {
                    ens_args_wo_typ.push(exp_to_expr(ctx, &arg_x, expr_ctxt)?)
                };
            }
            let havoc_stmts = mutated_fields
                .keys()
                .map(|base| Arc::new(StmtX::Havoc(suffix_local_unique_id(&base))));

            let unchaged_stmts = mutated_fields
                .iter()
                .map(|(base, mutated_fields)| {
                    let LocFieldInfo { base_typ, base_span: _, a: _ } = mutated_fields;
                    match assume_other_fields_unchanged(
                        ctx,
                        SNAPSHOT_CALL,
                        &stm.span,
                        base,
                        mutated_fields,
                        expr_ctxt,
                    ) {
                        Ok(stmt) => {
                            let typ_inv_stmts = typ_invariant(
                                ctx,
                                base_typ,
                                &string_var(&suffix_local_unique_id(base)),
                            )
                            .into_iter()
                            .map(|e| Arc::new(StmtX::Assume(e)));
                            let unchanged_and_typ_inv: Vec<Stmt> =
                                stmt.into_iter().chain(typ_inv_stmts).collect();
                            Ok(unchanged_and_typ_inv)
                        }
                        Err(vir_err) => Err(vir_err.clone()),
                    }
                })
                .collect::<Result<Vec<Vec<Stmt>>, VirErr>>()?
                .into_iter()
                .flatten();
            let mut_stmts: Vec<_> = havoc_stmts.chain(unchaged_stmts).collect::<Vec<_>>();

            if call_snapshot {
                stmts.push(Arc::new(StmtX::Snapshot(snapshot_ident(SNAPSHOT_CALL))));
                stmts.extend(mut_stmts.into_iter());
            } else {
                assert_eq!(mut_stmts.len(), 0);
                if ctx.debug {
                    state.map_span(&stm, SpanKind::Full);
                }
            }
            let mut ens_args: Vec<_> =
                typ_args.into_iter().chain(ens_args_wo_typ.into_iter()).collect();
            if let Some(Dest { dest, is_init }) = dest {
                let var = suffix_local_unique_id(&get_loc_var(dest));
                ens_args.push(exp_to_expr(ctx, &dest, expr_ctxt)?);
                if !*is_init {
                    let havoc = StmtX::Havoc(var.clone());
                    stmts.push(Arc::new(havoc));
                }
                if ctx.debug {
                    // Add a snapshot after we modify the destination
                    let sid = state.update_current_sid(SUFFIX_SNAP_MUT);
                    // Update the snap_map so that it reflects the state _after_ the
                    // statement takes effect.
                    state.map_span(&stm, SpanKind::Full);
                    let snapshot = Arc::new(StmtX::Snapshot(sid.clone()));
                    stmts.push(snapshot);
                }
            }
            if ctx.funcs_with_ensure_predicate.contains(&func.x.name) {
                let f_ens = prefix_ensures(&fun_to_air_ident(&func.x.name));
                let e_ens = Arc::new(ExprX::Apply(f_ens, Arc::new(ens_args)));
                stmts.push(Arc::new(StmtX::Assume(e_ens)));
            }
            vec![Arc::new(StmtX::Block(Arc::new(stmts)))] // wrap in block for readability
        }
        StmX::Assert(error, expr) => {
            let air_expr = exp_to_expr(ctx, &expr, expr_ctxt)?;
            let error = match error {
                Some(error) => error.clone(),
                None => error_with_label(
                    "assertion failed".to_string(),
                    &stm.span,
                    "assertion failed".to_string(),
                ),
            };
            if ctx.debug {
                state.map_span(&stm, SpanKind::Full);
            }
            vec![Arc::new(StmtX::Assert(error, air_expr))]
        }
        StmX::AssertQuery { typ_inv_vars, body, mode } => {
            if ctx.debug {
                unimplemented!("assert query is unsupported in debugger mode");
            }

            let mut local = state.local_shared.clone();
            for (x, typ) in typ_inv_vars.iter() {
                let typ_inv = typ_invariant(ctx, typ, &ident_var(&suffix_local_unique_id(x)));
                if let Some(expr) = typ_inv {
                    local.push(Arc::new(DeclX::Axiom(expr)));
                }
            }

            state.push_scope();
            let proof_stmts: Vec<Stmt> = stm_to_stmts(ctx, state, body)?;
            state.pop_scope();
            let mut air_body: Vec<Stmt> = Vec::new();
            air_body.append(&mut proof_stmts.clone());
            let assertion = one_stmt(air_body);

            match mode {
                AssertQueryMode::NonLinear => {
                    let query = Arc::new(QueryX { local: Arc::new(local), assertion });
                    state.commands.push(CommandsWithContextX::new(
                        stm.span.clone(),
                        "assert_nonlinear_by".to_string(),
                        Arc::new(vec![
                            mk_option_command("smt.arith.nl", "true"),
                            Arc::new(CommandX::CheckValid(query)),
                            mk_option_command("smt.arith.nl", "false"),
                        ]),
                        ProverChoice::DefaultProver,
                    ));
                }
                _ => unreachable!("bitvector mode in wrong place"),
            }

            vec![]
        }
        StmX::AssertBitVector { requires, ensures } => {
            if ctx.debug {
                unimplemented!("AssertBitVector is unsupported in debugger mode");
            }
            let bv_expr_ctxt = &ExprCtxt::new_mode_bv(ExprMode::Body, true);

            let requires_air: Vec<Expr> =
                vec_map_result(requires, |e| exp_to_expr(ctx, e, bv_expr_ctxt))?;

            let ensures_air: Vec<(Span, Expr)> =
                vec_map_result(ensures, |e| match exp_to_expr(ctx, e, bv_expr_ctxt) {
                    Ok(ens_air) => Ok((e.span.clone(), ens_air)),
                    Err(vir_err) => Err(vir_err.clone()),
                })?;

            let mut local = state.local_bv_shared.clone();
            for req in requires_air.iter() {
                local.push(Arc::new(DeclX::Axiom(req.clone())));
            }

            let mut air_body: Vec<Stmt> = Vec::new();
            for (span, ens) in ensures_air.iter() {
                let error = error("bitvector ensures not satisfied", span);
                let ens_stmt = StmtX::Assert(error, ens.clone());
                air_body.push(Arc::new(ens_stmt));
            }
            let assertion = one_stmt(air_body);

            let query = Arc::new(QueryX { local: Arc::new(local), assertion });
            state.commands.push(CommandsWithContextX::new(
                stm.span.clone(),
                "assert_bitvector_by".to_string(),
                Arc::new(vec![
                    mk_option_command("smt.case_split", "0"),
                    Arc::new(CommandX::CheckValid(query)),
                    mk_option_command("smt.case_split", "3"),
                ]),
                ProverChoice::DefaultProver,
            ));
            vec![]
        }

        StmX::AssertBV(expr) => {
            // here expr is boxed/unboxed in poly::poly_expr
            // this is for integer version
            // for bitvector part, box/unbox will be completely removed in exp_to_bv_expr
            let bv_expr_ctxt = &ExprCtxt::new_mode_bv(ExprMode::Body, true);
            let error = error_with_label(
                "assertion failed".to_string(),
                &stm.span,
                "assertion failed".to_string(),
            );
            let local = state.local_bv_shared.clone();
            let air_expr = exp_to_expr(ctx, &expr, bv_expr_ctxt)?;
            let assertion = Arc::new(StmtX::Assert(error, air_expr));
            // this creates a separate query for the bv assertion
            let query = Arc::new(QueryX { local: Arc::new(local), assertion });
            let mut bv_commands = mk_bitvector_option();
            bv_commands.push(Arc::new(CommandX::CheckValid(query)));
            state.commands.push(CommandsWithContextX::new(
                stm.span.clone(),
                "assert_bit_vector".to_string(),
                Arc::new(bv_commands),
                ProverChoice::Spinoff,
            ));

            vec![Arc::new(StmtX::Assume(exp_to_expr(ctx, &expr, expr_ctxt)?))]
        }
        StmX::Assume(expr) => {
            if ctx.debug {
                state.map_span(&stm, SpanKind::Full);
            }
            vec![Arc::new(StmtX::Assume(exp_to_expr(ctx, &expr, expr_ctxt)?))]
        }
        StmX::Assign { lhs: Dest { dest, is_init: true }, rhs } => {
            let x = loc_is_var(dest).expect("is_init assign dest must be a variable");
            stm_to_stmts(ctx, state, &assume_var(&stm.span, x, rhs))?
        }
        StmX::Assign { lhs: Dest { dest, is_init: false }, rhs } => {
            let mut stmts: Vec<Stmt> = Vec::new();
            if let Some(x) = loc_is_var(dest) {
                let name = suffix_local_unique_id(x);
                stmts.push(Arc::new(StmtX::Assign(name, exp_to_expr(ctx, rhs, expr_ctxt)?)));
                if ctx.debug {
                    // Add a snapshot after we modify the destination
                    let sid = state.update_current_sid(SUFFIX_SNAP_MUT);
                    let snapshot = Arc::new(StmtX::Snapshot(sid.clone()));
                    stmts.push(snapshot);
                    // Update the snap_map so that it reflects the state _after_ the
                    // statement takes effect.
                    state.map_span(&stm, SpanKind::Full);
                }
            } else {
                let (base_var, LocFieldInfo { base_typ, base_span, a: fields }) =
                    loc_to_field_path(dest);
                stmts.push(Arc::new(StmtX::Snapshot(snapshot_ident(SNAPSHOT_ASSIGN))));
                stmts.push(Arc::new(StmtX::Havoc(suffix_local_unique_id(&base_var))));
                let snapshotted_rhs = snapshotted_vars(rhs, SNAPSHOT_ASSIGN);
                let eqx = ExpX::Binary(BinaryOp::Eq(Mode::Spec), dest.clone(), snapshotted_rhs);
                let eq = SpannedTyped::new(&stm.span, &Arc::new(TypX::Bool), eqx);
                stmts.extend(stm_to_stmts(
                    ctx,
                    state,
                    &Spanned::new(stm.span.clone(), StmX::Assume(eq)),
                )?);
                stmts.extend(assume_other_fields_unchanged(
                    ctx,
                    SNAPSHOT_ASSIGN,
                    &stm.span,
                    &base_var,
                    &LocFieldInfo { base_typ, base_span, a: vec![fields] },
                    expr_ctxt,
                )?);
                if ctx.debug {
                    unimplemented!("complex assignments are unsupported in debugger mode");
                }
            }
            stmts
        }
        StmX::DeadEnd(s) => {
            vec![Arc::new(StmtX::DeadEnd(one_stmt(stm_to_stmts(ctx, state, s)?)))]
        }
        StmX::If(cond, lhs, rhs) => {
            let pos_cond = exp_to_expr(ctx, &cond, expr_ctxt)?;
            let neg_cond = Arc::new(ExprX::Unary(air::ast::UnaryOp::Not, pos_cond.clone()));
            let pos_assume = Arc::new(StmtX::Assume(pos_cond));
            let neg_assume = Arc::new(StmtX::Assume(neg_cond));
            let mut lhss = stm_to_stmts(ctx, state, lhs)?;
            let mut rhss = match rhs {
                None => vec![],
                Some(rhs) => stm_to_stmts(ctx, state, rhs)?,
            };
            lhss.insert(0, pos_assume);
            rhss.insert(0, neg_assume);
            let lblock = Arc::new(StmtX::Block(Arc::new(lhss)));
            let rblock = Arc::new(StmtX::Block(Arc::new(rhss)));
            let mut stmts = vec![Arc::new(StmtX::Switch(Arc::new(vec![lblock, rblock])))];
            if ctx.debug {
                // Add a snapshot for the state after we join the lhs and rhs back together
                let sid = state.update_current_sid(SUFFIX_SNAP_JOIN);
                let snapshot = Arc::new(StmtX::Snapshot(sid.clone()));
                stmts.push(snapshot);
                state.map_span(&stm, SpanKind::End);
            }
            stmts
        }
        StmX::While { cond_stms, cond_exp, body, invs, typ_inv_vars, modified_vars } => {
            let pos_cond = exp_to_expr(ctx, &cond_exp, expr_ctxt)?;
            let neg_cond = Arc::new(ExprX::Unary(air::ast::UnaryOp::Not, pos_cond.clone()));
            let pos_assume = Arc::new(StmtX::Assume(pos_cond));
            let neg_assume = Arc::new(StmtX::Assume(neg_cond));
            let invs: Vec<(Span, Expr)> = vec_map_result(invs, {
                |e| match exp_to_expr(ctx, e, expr_ctxt) {
                    Ok(expr) => Ok((e.span.clone(), expr)),
                    Err(vir_err) => Err(vir_err.clone()),
                }
            })?;

            let entry_snap_id = if ctx.debug {
                // Add a snapshot to capture the start of the while loop
                // We add the snapshot via Block to avoid copying the entire AST of the loop body
                let entry_snap = state.update_current_sid(SUFFIX_SNAP_WHILE_BEGIN);
                Some(entry_snap)
            } else {
                None
            };

            let cond_stmts: Vec<Stmt> = vec_map_result(cond_stms, |s| stm_to_stmts(ctx, state, s))?
                .into_iter()
                .flatten()
                .collect();
            let mut air_body: Vec<Stmt> = Vec::new();
            air_body.append(&mut cond_stmts.clone());
            air_body.push(pos_assume);
            air_body.append(&mut stm_to_stmts(ctx, state, body)?);

            /*
            Generate a separate SMT query for the loop body.
            Rationale: large functions with while loops tend to be slow to verify.
            Therefore, it's good to try to factor large functions
            into smaller, easier-to-verify pieces.
            Since we have programmer-supplied invariants anyway,
            this is a good place for such refactoring.
            This isn't necessarily a benefit for small functions or small loops,
            but in practice, verification for large functions and large loops are slow
            enough that programmers often do this refactoring by hand anyway,
            so it's a benefit when verification gets hard, which is arguably what matters most.
            (The downside: the programmer might have to write more complete invariants,
            but this is part of the point: the invariants specify a precise interface
            between the outer function and the inner loop body, so we don't have to import
            the outer function's entire context into the verification of the loop body,
            which would slow verification of the loop body.)
            */
            let mut local = state.local_shared.clone();
            for (x, typ) in typ_inv_vars.iter() {
                let typ_inv = typ_invariant(ctx, typ, &ident_var(&suffix_local_unique_id(x)));
                if let Some(expr) = typ_inv {
                    local.push(Arc::new(DeclX::Axiom(expr)));
                }
            }
            for (_, inv) in invs.iter() {
                local.push(Arc::new(DeclX::Axiom(inv.clone())));
            }
            if !ctx.checking_recommends() {
                for (span, inv) in invs.iter() {
                    let error = error("invariant not satisfied at end of loop body", span);
                    let inv_stmt = StmtX::Assert(error, inv.clone());
                    air_body.push(Arc::new(inv_stmt));
                }
            }
            let assertion = one_stmt(air_body);

            let assertion = if !ctx.debug {
                assertion
            } else {
                // Update the snap_map to associate the start of the while loop with the new snapshot
                let entry_snap_id = entry_snap_id.unwrap(); // Always Some if ctx.debug
                let snapshot: Stmt = Arc::new(StmtX::Snapshot(entry_snap_id.clone()));
                state.map_span(&body, SpanKind::Start);
                let block_contents: Vec<Stmt> = vec![snapshot, assertion];
                Arc::new(StmtX::Block(Arc::new(block_contents)))
            };

            let query = Arc::new(QueryX { local: Arc::new(local), assertion });
            state.commands.push(Arc::new(CommandsWithContextX {
                span: stm.span.clone(),
                desc: "while loop".to_string(),
                commands: Arc::new(vec![Arc::new(CommandX::CheckValid(query))]),
                prover_choice: ProverChoice::DefaultProver,
            }));

            // At original site of while loop, assert invariant, havoc, assume invariant + neg_cond
            let mut stmts: Vec<Stmt> = Vec::new();
            if !ctx.checking_recommends() {
                for (span, inv) in invs.iter() {
                    let error = error("invariant not satisfied before loop", span);
                    let inv_stmt = StmtX::Assert(error, inv.clone());
                    stmts.push(Arc::new(inv_stmt));
                }
            }
            for x in modified_vars.iter() {
                stmts.push(Arc::new(StmtX::Havoc(suffix_local_unique_id(&x))));
            }
            for (x, typ) in typ_inv_vars.iter() {
                if modified_vars.contains(x) {
                    let typ_inv = typ_invariant(ctx, typ, &ident_var(&suffix_local_unique_id(x)));
                    if let Some(expr) = typ_inv {
                        stmts.push(Arc::new(StmtX::Assume(expr)));
                    }
                }
            }
            for (_, inv) in invs.iter() {
                let inv_stmt = StmtX::Assume(inv.clone());
                stmts.push(Arc::new(inv_stmt));
            }
            stmts.append(&mut cond_stmts.clone());
            stmts.push(neg_assume);
            if ctx.debug {
                // Add a snapshot for the state after we emerge from the while loop
                let sid = state.update_current_sid(SUFFIX_SNAP_WHILE_END);
                // Update the snap_map so that it reflects the state _after_ the
                // statement takes effect.
                state.map_span(&stm, SpanKind::End);
                let snapshot = Arc::new(StmtX::Snapshot(sid));
                stmts.push(snapshot);
            }
            stmts
        }
        StmX::OpenInvariant(inv_exp, uid, typ, body_stm, atomicity) => {
            let mut stmts = vec![];

            // Build the inv_expr. Note: In the SST, this should have been assigned
            // to a tmp variable
            // to ensure that its value is constant across the entire invariant block.
            // We will be referencing it later.
            let inv_expr = exp_to_expr(ctx, inv_exp, &ExprCtxt::new())?;

            // Assert that the namespace of the inv we are opening is in the mask set
            let namespace_expr = call_namespace(inv_expr.clone(), typ, *atomicity);
            state.mask.assert_contains(&inv_exp.span, &namespace_expr, &mut stmts);

            // add an 'assume' that inv holds
            let inner_var = SpannedTyped::new(&stm.span, typ, ExpX::Var(uid.clone()));
            let inner_expr = exp_to_expr(ctx, &inner_var, &ExprCtxt::new())?;
            let ty_inv_opt = typ_invariant(ctx, typ, &inner_expr);
            if let Some(ty_inv) = ty_inv_opt {
                stmts.push(Arc::new(StmtX::Assume(ty_inv)));
            }
            let main_inv = call_inv(ctx, inv_expr, inner_expr, typ, *atomicity);
            stmts.push(Arc::new(StmtX::Assume(main_inv.clone())));

            // process the body
            // first remove the namespace from the mask set so that we cannot re-open
            // the same invariant inside
            let mut inner_mask = state.mask.remove_element(inv_exp.span.clone(), namespace_expr);
            swap(&mut state.mask, &mut inner_mask);
            stmts.append(&mut stm_to_stmts(ctx, state, body_stm)?);
            swap(&mut state.mask, &mut inner_mask);

            // assert the invariant still holds
            // Note that we re-use main_inv here; but main_inv references the variable
            // given by `uid` which may have been assigned to since the start of the block.
            // so this may evaluate differently in the SMT.
            let error = error("Cannot show invariant holds at end of block", &body_stm.span);
            stmts.push(Arc::new(StmtX::Assert(error, main_inv)));

            stmts
        }
        StmX::Fuel(x, fuel) => {
            let mut stmts: Vec<Stmt> = Vec::new();
            if *fuel >= 1 {
                // (assume (fuel_bool fuel%f))
                let id_fuel = prefix_fuel_id(&fun_to_air_ident(&x));
                let expr_fuel_bool = str_apply(&FUEL_BOOL, &vec![ident_var(&id_fuel)]);
                stmts.push(Arc::new(StmtX::Assume(expr_fuel_bool)));
            }
            if *fuel >= 2 {
                // (assume (exists ((fuel Fuel)) (= fuel_nat%f (succ ... succ fuel))))
                let mut added_fuel = str_var(FUEL_PARAM);
                for _ in 0..*fuel - 1 {
                    added_fuel = str_apply(SUCC, &vec![added_fuel]);
                }
                let eq = mk_eq(
                    &ident_var(&crate::def::prefix_fuel_nat(&fun_to_air_ident(&x))),
                    &added_fuel,
                );
                let binder = ident_binder(&str_ident(FUEL_PARAM), &str_typ(FUEL_TYPE));
                let qid = None; // Introduces a variable name but shouldn't otherwise be instantiated
                stmts.push(Arc::new(StmtX::Assume(mk_exists(&vec![binder], &vec![], qid, &eq))));
            }
            if ctx.debug {
                state.map_span(&stm, SpanKind::Full);
            }
            stmts
        }
        StmX::Block(stms) => {
            if ctx.debug {
                state.push_scope();
                state.map_span(&stm, SpanKind::Start);
            }
            let stmts: Vec<Stmt> = vec_map_result(stms, |s| stm_to_stmts(ctx, state, s))?
                .into_iter()
                .flatten()
                .collect();
            if ctx.debug {
                state.pop_scope();
            }
            stmts
        }
    };
    Ok(result)
}

fn set_fuel(ctx: &Ctx, local: &mut Vec<Decl>, hidden: &Vec<Fun>) {
    let fuel_expr = if hidden.len() == 0 {
        str_var(&FUEL_DEFAULTS)
    } else {
        let mut disjuncts: Vec<Expr> = Vec::new();
        let id = str_ident("id");
        let x_id = ident_var(&id);

        // (= (fuel_bool id) (fuel_bool_default id))
        let fuel_bool = str_apply(&FUEL_BOOL, &vec![x_id.clone()]);
        let fuel_bool_default = str_apply(&FUEL_BOOL_DEFAULT, &vec![x_id.clone()]);
        let eq = air::ast::BinaryOp::Eq;
        disjuncts.push(Arc::new(ExprX::Binary(eq, fuel_bool.clone(), fuel_bool_default)));

        // ... || id == hidden1 || id == hidden2 || ...
        for hide in hidden {
            let x_hide = ident_var(&prefix_fuel_id(&fun_to_air_ident(hide)));
            disjuncts.push(Arc::new(ExprX::Binary(air::ast::BinaryOp::Eq, x_id.clone(), x_hide)));
        }

        // (forall ((id FuelId)) ...)
        let trigger: Trigger = Arc::new(vec![fuel_bool.clone()]);
        let triggers: Triggers = Arc::new(vec![trigger]);
        let binders: Binders<air::ast::Typ> = Arc::new(vec![ident_binder(&id, &str_typ(FUEL_ID))]);

        let fun_name = fun_as_rust_dbg(
            &ctx.fun.as_ref().expect("Missing a current function value").current_fun,
        );
        let qid = new_internal_qid(format!("{}_nondefault_fuel", fun_name));
        let bind = Arc::new(BindX::Quant(Quant::Forall, binders, triggers, qid));
        let or = Arc::new(ExprX::Multi(air::ast::MultiOp::Or, Arc::new(disjuncts)));
        mk_bind_expr(&bind, &or)
    };
    local.push(Arc::new(DeclX::Axiom(fuel_expr)));
}

pub fn body_stm_to_air(
    ctx: &Ctx,
    func_span: &Span,
    trait_typ_substs: &Vec<(Ident, Typ)>,
    typ_params: &Idents,
    params: &Params,
    local_decls: &Vec<LocalDecl>,
    hidden: &Vec<Fun>,
    reqs: &Vec<Exp>,
    enss: &Vec<Exp>,
    mask_spec: &MaskSpec,
    mode: Mode,
    stm: &Stm,
    is_integer_ring: bool,
    is_bit_vector_mode: bool,
    skip_ensures: bool,
    is_nonlinear: bool,
    is_spinoff_prover: bool,
) -> Result<(Vec<CommandsWithContext>, Vec<(Span, SnapPos)>), VirErr> {
    // Verifying a single function can generate multiple SMT queries.
    // Some declarations (local_shared) are shared among the queries.
    // Others are private to each query.
    let mut local_shared: Vec<Decl> = Vec::new();
    let mut local_bv_shared: Vec<Decl> = Vec::new();

    let trait_typ_bind =
        vec_map(trait_typ_substs, |(x, t)| ident_binder(&suffix_typ_param_id(x), &typ_to_id(t)));

    for x in typ_params.iter() {
        local_shared
            .push(Arc::new(DeclX::Const(suffix_typ_param_id(&x), str_typ(crate::def::TYPE))));
    }
    for decl in local_decls {
        local_shared.push(if decl.mutable {
            Arc::new(DeclX::Var(suffix_local_unique_id(&decl.ident), typ_to_air(ctx, &decl.typ)))
        } else {
            Arc::new(DeclX::Const(suffix_local_unique_id(&decl.ident), typ_to_air(ctx, &decl.typ)))
        });
        // for assert_bit_vector/bit_vector function, only allow integer and boolean types
        if let Some(width) = bitwidth_from_type(&decl.typ) {
            let typ = bv_typ(width);
            local_bv_shared.push(Arc::new(DeclX::Var(suffix_local_unique_id(&decl.ident), typ)));
        } else if let TypX::Bool = *decl.typ {
            local_bv_shared
                .push(Arc::new(DeclX::Var(suffix_local_unique_id(&decl.ident), bool_typ())));
        }
    }

    set_fuel(ctx, &mut local_shared, hidden);

    let mut declared: HashMap<UniqueIdent, Typ> = HashMap::new();
    let mut assigned: HashSet<UniqueIdent> = HashSet::new();
    let mut has_mut_params = false;
    for param in params.iter() {
        declared.insert(unique_local(&param.x.name), param.x.typ.clone());
        assigned.insert(unique_local(&param.x.name));
        if param.x.is_mut {
            has_mut_params = true;
        }
    }
    for decl in local_decls {
        declared.insert(decl.ident.clone(), decl.typ.clone());
    }

    let initial_sid = Arc::new("0_entry".to_string());

    let mask = mask_set_from_spec(mask_spec, mode);

    let mut state = State {
        local_shared,
        local_bv_shared,
        commands: Vec::new(),
        snapshot_count: 0,
        sids: vec![initial_sid.clone()],
        snap_map: Vec::new(),
        assign_map: HashMap::new(),
        mask,
    };

    let mut _modified = HashSet::new();

    let stm = crate::sst_vars::stm_assign(
        &mut state.assign_map,
        &declared,
        &mut assigned,
        &mut _modified,
        stm,
    );

    let mut stmts = stm_to_stmts(ctx, &mut state, &stm)?;

    if has_mut_params {
        stmts.insert(0, Arc::new(StmtX::Snapshot(snapshot_ident(SNAPSHOT_PRE))));
    }

    if ctx.debug {
        let snapshot = Arc::new(StmtX::Snapshot(initial_sid));
        let mut new_stmts = vec![snapshot];
        new_stmts.append(&mut stmts);
        stmts = new_stmts;
    }

    let mut local = if !is_bit_vector_mode {
        state.local_shared.clone()
    } else {
        state.local_bv_shared.clone()
    };

    if !skip_ensures {
        // This generates postconditions for the end of the function.
        // Note: Postconditions for 'return' statements are handled in ast_to_sst.

        for ens in enss {
            let error = error_with_label(
                "postcondition not satisfied".to_string(),
                &stm.span,
                "at the end of the function body".to_string(),
            )
            .secondary_label(&ens.span, "failed this postcondition".to_string());

            let expr_ctxt = &ExprCtxt::new_mode_bv(ExprMode::Body, is_bit_vector_mode);
            let e = mk_let(&trait_typ_bind, &exp_to_expr(ctx, ens, expr_ctxt)?);
            let ens_stmt = StmtX::Assert(error, e);
            stmts.push(Arc::new(ens_stmt));
        }
    }
    let assertion = one_stmt(stmts);

    if !is_bit_vector_mode && !is_integer_ring {
        for param in params.iter() {
            let typ_inv =
                typ_invariant(ctx, &param.x.typ, &ident_var(&suffix_local_stmt_id(&param.x.name)));
            if let Some(expr) = typ_inv {
                local.push(Arc::new(DeclX::Axiom(expr)));
            }
        }
    }

    for req in reqs {
        let expr_ctxt = &ExprCtxt::new_mode_bv(ExprMode::BodyPre, is_bit_vector_mode);
        let e = mk_let(&trait_typ_bind, &exp_to_expr(ctx, req, expr_ctxt)?);
        local.push(Arc::new(DeclX::Axiom(e)));
    }

    if is_integer_ring {
        if is_bit_vector_mode {
            panic! {"Error: integer_ring and bit_vector should not be used together"}
        };
        // parameters, requires, ensures to Singular Query
        // in the resulting queryX::assertion, the last stmt should be ensure expression
        let mut singular_vars: Vec<Decl> = vec![];
        for param in params.iter() {
            singular_vars
                .push(Arc::new(DeclX::Var(param.x.name.clone(), typ_to_air(ctx, &param.x.typ))));
        }
        let mut singular_stmts: Vec<Stmt> = vec![];
        for req in reqs {
            let error = error_with_label(
                "Failed to translate this expression into a singular query".to_string(),
                &req.span,
                "at the require clause".to_string(),
            );
            let air_expr = exp_to_expr(ctx, req, &ExprCtxt::new_mode(ExprMode::BodyPre))?;
            let assert_stm = Arc::new(StmtX::Assert(error, air_expr));
            singular_stmts.push(assert_stm);
        }
        for ens in enss {
            let error = error_with_label(
                "Failed to translate this expression into a singular query".to_string(),
                &ens.span,
                "at the ensure clause".to_string(),
            );
            let air_expr = exp_to_expr(ctx, ens, &ExprCtxt::new_mode(ExprMode::BodyPre))?;
            let assert_stm = Arc::new(StmtX::Assert(error, air_expr));
            singular_stmts.push(assert_stm);
        }

        let query = Arc::new(QueryX {
            local: Arc::new(singular_vars),
            assertion: Arc::new(air::ast::StmtX::Block(Arc::new(singular_stmts))),
        });
        let singular_command = Arc::new(CommandX::CheckValid(query));

        state.commands.push(CommandsWithContextX::new(
            func_span.clone(),
            "Singular check valid".to_string(),
            Arc::new(vec![singular_command]),
            ProverChoice::Singular,
        ));
    } else {
        let query = Arc::new(QueryX { local: Arc::new(local), assertion });
        let commands = if is_nonlinear {
            vec![
                mk_option_command("smt.arith.nl", "true"),
                Arc::new(CommandX::CheckValid(query)),
                mk_option_command("smt.arith.nl", "false"),
            ]
        } else if is_bit_vector_mode {
            let mut bv_commands = mk_bitvector_option();
            bv_commands.push(Arc::new(CommandX::CheckValid(query)));
            bv_commands
        } else {
            vec![Arc::new(CommandX::CheckValid(query))]
        };
        state.commands.push(CommandsWithContextX::new(
            func_span.clone(),
            "function body check".to_string(),
            Arc::new(commands),
            if is_spinoff_prover || is_bit_vector_mode {
                ProverChoice::Spinoff
            } else {
                ProverChoice::DefaultProver
            },
        ));
    }
    Ok((state.commands, state.snap_map))
}
