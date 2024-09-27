use crate::ast::{
    ArithOp, AssertQueryMode, BinaryOp, BitwiseOp, FieldOpr, Fun, Ident, Idents, InequalityOp,
    IntRange, IntegerTypeBitwidth, IntegerTypeBoundKind, MaskSpec, Mode, Path, PathX, Primitive,
    SpannedTyped, Typ, TypDecoration, TypDecorationArg, TypX, Typs, UnaryOp, UnaryOpr, UnwindSpec,
    VarAt, VarIdent, VariantCheck, VirErr, Visibility,
};
use crate::ast_util::{
    fun_as_friendly_rust_name, get_field, get_variant, typ_args_for_datatype_typ, undecorate_typ,
    LowerUniqueVar,
};
use crate::bitvector_to_air::bv_to_queries;
use crate::context::Ctx;
use crate::def::{
    fun_to_string, is_variant_ident, new_internal_qid, new_user_qid_name, path_to_string,
    prefix_box, prefix_ensures, prefix_fuel_id, prefix_no_unwind_when, prefix_open_inv,
    prefix_pre_var, prefix_requires, prefix_spec_fn_type, prefix_unbox, snapshot_ident,
    static_name, suffix_global_id, suffix_local_unique_id, suffix_typ_param_ids, unique_local,
    variant_field_ident, variant_ident, CommandsWithContext, CommandsWithContextX, ProverChoice,
    SnapPos, SpanKind, Spanned, ARCH_SIZE, FUEL_BOOL, FUEL_BOOL_DEFAULT, FUEL_DEFAULTS, FUEL_ID,
    FUEL_PARAM, FUEL_TYPE, I_HI, I_LO, POLY, SNAPSHOT_ASSIGN, SNAPSHOT_CALL, SNAPSHOT_PRE,
    STRSLICE_GET_CHAR, STRSLICE_IS_ASCII, STRSLICE_LEN, STRSLICE_NEW_STRLIT, SUCC,
    SUFFIX_SNAP_JOIN, SUFFIX_SNAP_MUT, SUFFIX_SNAP_WHILE_BEGIN, SUFFIX_SNAP_WHILE_END, U_HI,
};
use crate::inv_masks::MaskSet;
use crate::messages::{error, error_with_label, Span};
use crate::poly::{typ_as_mono, MonoTyp, MonoTypX};
use crate::sst::{
    BndInfo, BndInfoUser, BndX, CallFun, Dest, Exp, ExpX, InternalFun, Stm, StmX, UniqueIdent,
    UnwindSst,
};
use crate::sst::{FuncCheckSst, Pars, PostConditionKind, Stms};
use crate::sst_util::subst_typ_for_datatype;
use crate::sst_vars::{get_loc_var, AssignMap};
use crate::util::{vec_map, vec_map_result};
use air::ast::{
    BindX, Binder, BinderX, Binders, CommandX, Constant, Decl, DeclX, Expr, ExprX, MultiOp, Qid,
    Quant, QueryX, Stmt, StmtX, Trigger, Triggers,
};
use air::ast_util::{
    bool_typ, ident_apply, ident_binder, ident_typ, ident_var, int_typ, mk_and, mk_bind_expr,
    mk_bitvector_option, mk_eq, mk_exists, mk_implies, mk_ite, mk_nat, mk_not, mk_option_command,
    mk_or, mk_sub, mk_unnamed_axiom, mk_xor, str_apply, str_ident, str_typ, str_var, string_var,
};
use air::context::SmtSolver;
use num_bigint::BigInt;
use std::collections::{BTreeMap, HashSet};
use std::mem::swap;
use std::sync::Arc;

pub struct PostConditionInfo {
    /// Identifier that holds the return value.
    /// May be referenced by `ens_exprs` or `ens_spec_precondition_stms`.
    pub dest: Option<VarIdent>,
    /// Post-conditions (only used in non-recommends-checking mode)
    pub ens_exprs: Vec<(Span, Expr)>,
    /// Recommends checks (only used in recommends-checking mode)
    pub ens_spec_precondition_stms: Stms,
    /// Extra info about PostCondition for error reporting
    pub kind: PostConditionKind,
}

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
        IntRange::Int | IntRange::Nat | IntRange::Char => {}
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

pub(crate) fn primitive_path(name: &Primitive) -> Path {
    match name {
        Primitive::Array => crate::def::array_type(),
        Primitive::Slice => crate::def::slice_type(),
        Primitive::StrSlice => crate::def::strslice_type(),
        Primitive::Ptr => crate::def::ptr_type(),
        Primitive::Global => crate::def::global_type(),
    }
}

pub(crate) fn primitive_type_id(name: &Primitive) -> Ident {
    str_ident(match name {
        Primitive::Array => crate::def::TYPE_ID_ARRAY,
        Primitive::Slice => crate::def::TYPE_ID_SLICE,
        Primitive::StrSlice => crate::def::TYPE_ID_STRSLICE,
        Primitive::Ptr => crate::def::TYPE_ID_PTR,
        Primitive::Global => crate::def::TYPE_ID_GLOBAL,
    })
}

pub(crate) fn monotyp_to_path(typ: &MonoTyp) -> Path {
    let id = match &**typ {
        MonoTypX::Bool => str_ident("bool"),
        MonoTypX::Int(range) => match range {
            IntRange::Int => str_ident("int"),
            IntRange::Nat => str_ident("nat"),
            IntRange::Char => str_ident("char"),
            IntRange::U(n) => Arc::new(format!("u{}", n)),
            IntRange::I(n) => Arc::new(format!("i{}", n)),
            IntRange::USize => str_ident("usize"),
            IntRange::ISize => str_ident("isize"),
        },
        MonoTypX::Datatype(path, typs) => {
            return crate::def::monotyp_apply(path, &typs.iter().map(monotyp_to_path).collect());
        }
        MonoTypX::Primitive(name, typs) => {
            return crate::def::monotyp_apply(
                &primitive_path(name),
                &typs.iter().map(monotyp_to_path).collect(),
            );
        }
        MonoTypX::Decorate(dec, typ) => {
            return crate::def::monotyp_decorate(*dec, &monotyp_to_path(typ));
        }
        MonoTypX::Decorate2(dec, typs) => {
            return crate::def::monotyp_decorate2(
                *dec,
                &typs.iter().map(monotyp_to_path).collect(),
            );
        }
    };
    Arc::new(PathX { krate: None, segments: Arc::new(vec![id]) })
}

pub(crate) fn typ_to_air(ctx: &Ctx, typ: &Typ) -> air::ast::Typ {
    match &**typ {
        TypX::Int(_) => int_typ(),
        TypX::Bool => bool_typ(),
        TypX::Tuple(_) => panic!("internal error: Tuple should have been removed by ast_simplify"),
        TypX::SpecFn(..) => Arc::new(air::ast::TypX::Fun),
        TypX::Primitive(Primitive::Array, _) => Arc::new(air::ast::TypX::Fun),
        TypX::AnonymousClosure(..) => {
            panic!("internal error: AnonymousClosure should have been removed by ast_simplify")
        }
        TypX::Datatype(path, _, _) => {
            if ctx.datatype_is_transparent[path] {
                ident_typ(&path_to_air_ident(path))
            } else {
                match typ_as_mono(typ) {
                    None => panic!("abstract datatype should be boxed"),
                    Some(monotyp) => ident_typ(&path_to_air_ident(&monotyp_to_path(&monotyp))),
                }
            }
        }
        TypX::Decorate(_, _, t) => typ_to_air(ctx, t),
        TypX::FnDef(..) => str_typ(crate::def::FNDEF_TYPE),
        TypX::Boxed(_) => str_typ(POLY),
        TypX::TypParam(_) => str_typ(POLY),
        TypX::Primitive(
            Primitive::Slice | Primitive::StrSlice | Primitive::Ptr | Primitive::Global,
            _,
        ) => match typ_as_mono(typ) {
            None => panic!("should be boxed"),
            Some(monotyp) => ident_typ(&path_to_air_ident(&monotyp_to_path(&monotyp))),
        },
        TypX::Projection { .. } => str_typ(POLY),
        TypX::TypeId => str_typ(crate::def::TYPE),
        TypX::ConstInt(_) => panic!("const integer cannot be used as an expression type"),
        TypX::Air(t) => t.clone(),
    }
}

pub fn range_to_id(range: &IntRange) -> Expr {
    match range {
        IntRange::Int => str_var(crate::def::TYPE_ID_INT),
        IntRange::Nat => str_var(crate::def::TYPE_ID_NAT),
        IntRange::Char => str_var(crate::def::TYPE_ID_CHAR),
        IntRange::U(_) | IntRange::USize => {
            apply_range_fun(crate::def::TYPE_ID_UINT, range, vec![])
        }
        IntRange::I(_) | IntRange::ISize => {
            apply_range_fun(crate::def::TYPE_ID_SINT, range, vec![])
        }
    }
}

fn decoration_str(d: TypDecoration) -> &'static str {
    match d {
        TypDecoration::Ref => crate::def::DECORATE_REF,
        TypDecoration::MutRef => crate::def::DECORATE_MUT_REF,
        TypDecoration::Box => crate::def::DECORATE_BOX,
        TypDecoration::Rc => crate::def::DECORATE_RC,
        TypDecoration::Arc => crate::def::DECORATE_ARC,
        TypDecoration::Ghost => crate::def::DECORATE_GHOST,
        TypDecoration::Tracked => crate::def::DECORATE_TRACKED,
        TypDecoration::Never => crate::def::DECORATE_NEVER,
        TypDecoration::ConstPtr => crate::def::DECORATE_CONST_PTR,
    }
}

// return (decorations, typ)
pub fn monotyp_to_id(typ: &MonoTyp) -> Vec<Expr> {
    let mk_id = |t: Expr| -> Vec<Expr> {
        let ds = str_var(crate::def::DECORATE_NIL);
        if crate::context::DECORATE { vec![ds, t] } else { vec![t] }
    };
    match &**typ {
        MonoTypX::Bool => mk_id(str_var(crate::def::TYPE_ID_BOOL)),
        MonoTypX::Int(range) => mk_id(range_to_id(range)),
        MonoTypX::Datatype(path, typs) => {
            let f_name = crate::def::prefix_type_id(path);
            let mut args: Vec<Expr> = Vec::new();
            for t in typs.iter() {
                args.extend(monotyp_to_id(t));
            }
            mk_id(air::ast_util::ident_apply_or_var(&f_name, &Arc::new(args)))
        }
        MonoTypX::Decorate(d, typ) if crate::context::DECORATE => {
            let ds_typ = monotyp_to_id(typ);
            assert!(ds_typ.len() == 2);
            let ds = str_apply(decoration_str(*d), &vec![ds_typ[0].clone()]);
            vec![ds, ds_typ[1].clone()]
        }
        MonoTypX::Decorate2(d, typs) if crate::context::DECORATE => {
            assert!(typs.len() == 2);
            let ds_typ1 = monotyp_to_id(&typs[0]);
            assert!(ds_typ1.len() == 2);
            let ds_typ2 = monotyp_to_id(&typs[1]);
            assert!(ds_typ2.len() == 2);
            let ds = str_apply(
                decoration_str(*d),
                &vec![ds_typ1[0].clone(), ds_typ1[1].clone(), ds_typ2[0].clone()],
            );
            vec![ds, ds_typ2[1].clone()]
        }
        MonoTypX::Decorate(_, typ) => monotyp_to_id(typ),
        MonoTypX::Decorate2(_, typs) => {
            assert!(typs.len() == 2);
            monotyp_to_id(&typs[1])
        }
        MonoTypX::Primitive(name, typs) => {
            let f_name = primitive_type_id(name);
            let mut args: Vec<Expr> = Vec::new();
            for t in typs.iter() {
                args.extend(monotyp_to_id(t));
            }
            mk_id(air::ast_util::ident_apply_or_var(&f_name, &Arc::new(args)))
        }
    }
}

fn big_int_to_expr(i: &BigInt) -> Expr {
    use num_traits::Zero;
    if i >= &BigInt::zero() { mk_nat(i) } else { air::ast_util::mk_neg(&mk_nat(-i)) }
}

// SMT-level type identifiers.
// We currently rely on *undecorated* type identifiers for:
// 1) Axioms about unboxing integer refinement types (nat, u8, etc.)
// 2) The box(unbox(x)) == x axiom
// Furthermore, we rely on *decorated* type identifiers for:
// 3) functions that return different results for T, &T, Rc<T>, etc., such as size_of
// 4) trait resolution
// Most axioms don't care about the decorations (e.g. box(unbox(x)) == x).
// Therefore, to reduce quantifier instantiations, we pass the decorations separately
// from the type identifiers, using the syntax:
//   - type_id ::= INT | BOOL | (DatatypeName dec_id type_id ... dec_id type_id) | ...
//   - dec_id ::= $ | decoration dec_id
//   - decoration ::= REF | RC | ...
// For example, &Rc<Foo<&bool>> would be something like:
//   - (REF (RC $)), (Foo (REF $) BOOL)
// instead of:
//   - (REF (RC (Foo (REF BOOL))))
// typ_to_ids(typ) return [decorations, type]
pub fn typ_to_ids(typ: &Typ) -> Vec<Expr> {
    let mk_id = |t: Expr| -> Vec<Expr> {
        let ds = str_var(crate::def::DECORATE_NIL);
        if crate::context::DECORATE { vec![ds, t] } else { vec![t] }
    };
    match &**typ {
        TypX::Bool => mk_id(str_var(crate::def::TYPE_ID_BOOL)),
        TypX::Int(range) => mk_id(range_to_id(range)),
        TypX::Tuple(_) => panic!("internal error: Tuple should have been removed by ast_simplify"),
        TypX::SpecFn(typs, typ) => mk_id(fun_id(typs, typ)),
        TypX::AnonymousClosure(..) => {
            panic!("internal error: AnonymousClosure should have been removed by ast_simplify")
        }
        TypX::FnDef(fun, typs, _resolved_fun) => mk_id(fndef_id(fun, typs)),
        TypX::Datatype(path, typs, _) => mk_id(datatype_id(path, typs)),
        TypX::Primitive(name, typs) => mk_id(primitive_id(&name, typs)),
        TypX::Decorate(d, None, typ) if crate::context::DECORATE => {
            let ds_typ = typ_to_ids(typ);
            assert!(ds_typ.len() == 2);
            let ds = str_apply(decoration_str(*d), &vec![ds_typ[0].clone()]);
            vec![ds, ds_typ[1].clone()]
        }
        TypX::Decorate(d, Some(TypDecorationArg { allocator_typ }), typ)
            if crate::context::DECORATE =>
        {
            let ds_typ1 = typ_to_ids(allocator_typ);
            assert!(ds_typ1.len() == 2);
            let ds_typ2 = typ_to_ids(typ);
            assert!(ds_typ2.len() == 2);
            let ds = str_apply(
                decoration_str(*d),
                &vec![ds_typ1[0].clone(), ds_typ1[1].clone(), ds_typ2[0].clone()],
            );
            vec![ds, ds_typ2[1].clone()]
        }
        TypX::Decorate(_, _, typ) => typ_to_ids(typ),
        TypX::Boxed(typ) => typ_to_ids(typ),
        TypX::TypParam(x) => {
            suffix_typ_param_ids(x).iter().map(|x| ident_var(&x.lower())).collect()
        }
        TypX::Projection { trait_typ_args, trait_path, name } => {
            let mut args: Vec<Expr> = Vec::new();
            for t in trait_typ_args.iter() {
                args.extend(typ_to_ids(t));
            }
            let pd = ident_apply(&crate::def::projection(true, trait_path, name), &args);
            let pt = ident_apply(&crate::def::projection(false, trait_path, name), &args);
            vec![pd, pt]
        }
        TypX::TypeId => panic!("internal error: typ_to_ids of TypeId"),
        TypX::ConstInt(c) => {
            mk_id(str_apply(crate::def::TYPE_ID_CONST_INT, &vec![big_int_to_expr(c)]))
        }
        TypX::Air(_) => panic!("internal error: typ_to_ids of Air"),
    }
}

pub(crate) fn typ_to_id(typ: &Typ) -> Expr {
    typ_to_ids(typ).last().unwrap().clone()
}

pub(crate) fn fun_id(typs: &Typs, typ: &Typ) -> Expr {
    let f_name = crate::def::prefix_type_id_fun(typs.len());
    let mut args: Vec<Expr> = Vec::new();
    for t in typs.iter() {
        args.extend(typ_to_ids(t));
    }
    args.extend(typ_to_ids(typ));
    air::ast_util::ident_apply_or_var(&f_name, &Arc::new(args))
}

pub(crate) fn datatype_id(path: &Path, typs: &Typs) -> Expr {
    let f_name = crate::def::prefix_type_id(path);
    let mut args: Vec<Expr> = Vec::new();
    for t in typs.iter() {
        args.extend(typ_to_ids(t));
    }
    air::ast_util::ident_apply_or_var(&f_name, &Arc::new(args))
}

pub(crate) fn primitive_id(name: &Primitive, typs: &Typs) -> Expr {
    let f_name = primitive_type_id(name);
    let mut args: Vec<Expr> = Vec::new();
    for t in typs.iter() {
        args.extend(typ_to_ids(t));
    }
    air::ast_util::ident_apply_or_var(&f_name, &Arc::new(args))
}

pub(crate) fn fndef_id(fun: &Fun, typs: &Typs) -> Expr {
    let f_name = crate::def::prefix_fndef_type_id(fun);
    let mut args: Vec<Expr> = Vec::new();
    for t in typs.iter() {
        args.extend(typ_to_ids(t));
    }
    air::ast_util::ident_apply_or_var(&f_name, &Arc::new(args))
}

pub(crate) fn expr_has_type(expr: &Expr, typ: &Expr) -> Expr {
    str_apply(crate::def::HAS_TYPE, &vec![expr.clone(), typ.clone()])
}

pub(crate) fn expr_has_typ(expr: &Expr, typ: &Typ) -> Expr {
    expr_has_type(expr, &typ_to_id(typ))
}

// If expr has type typ, what can we assume to be true about expr?
// For refinement types, transparent datatypes potentially containing refinement types,
// abstract types applied to type variables,
// and type variables potentially instantiated with refinement types, return Some invariant.
// For non-refinement types and abstract monotypes, return None,
// since the SMT sorts for these types can express the types precisely with no need for refinement.
pub(crate) fn typ_invariant(ctx: &Ctx, typ: &Typ, expr: &Expr) -> Option<Expr> {
    // Should be kept in sync with vir::context::datatypes_invs
    match &*undecorate_typ(typ) {
        TypX::Int(IntRange::Int) => None,
        TypX::Int(IntRange::Nat) => {
            let zero = Arc::new(ExprX::Const(Constant::Nat(Arc::new("0".to_string()))));
            Some(Arc::new(ExprX::Binary(air::ast::BinaryOp::Le, zero, expr.clone())))
        }
        TypX::Int(range) => {
            let f_name = match range {
                IntRange::Int => panic!("internal error: Int"),
                IntRange::Nat => panic!("internal error: Int"),
                IntRange::Char => crate::def::CHAR_INV,
                IntRange::U(_) | IntRange::USize => crate::def::U_INV,
                IntRange::I(_) | IntRange::ISize => crate::def::I_INV,
            };
            Some(apply_range_fun(&f_name, &range, vec![expr.clone()]))
        }
        TypX::SpecFn(..) => {
            Some(expr_has_typ(&try_box(ctx, expr.clone(), typ).expect("try_box lambda"), typ))
        }
        TypX::Primitive(Primitive::Array, _) => {
            Some(expr_has_typ(&try_box(ctx, expr.clone(), typ).expect("try_box array"), typ))
        }
        TypX::Datatype(path, _, _) => {
            if ctx.datatype_is_transparent[path] {
                if ctx.datatypes_with_invariant.contains(path) {
                    let box_expr = ident_apply(&prefix_box(&path), &vec![expr.clone()]);
                    Some(expr_has_typ(&box_expr, typ))
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
        TypX::Decorate(..) => unreachable!(),
        TypX::Boxed(_) => Some(expr_has_typ(expr, typ)),
        TypX::TypParam(_) => Some(expr_has_typ(expr, typ)),
        TypX::Projection { .. } => Some(expr_has_typ(expr, typ)),
        TypX::Bool | TypX::AnonymousClosure(..) | TypX::TypeId => None,
        TypX::Tuple(_) | TypX::Air(_) => panic!("typ_invariant"),
        // REVIEW: we could also try to add an IntRange type invariant for TypX::ConstInt
        // (see also context.rs datatypes_invs)
        TypX::ConstInt(_) => None,
        TypX::Primitive(p, _) => {
            match p {
                Primitive::Array | Primitive::Slice | Primitive::Ptr => {
                    // Each of these is like an abstract Datatype
                    if typ_as_mono(typ).is_none() {
                        panic!("abstract datatype should be boxed")
                    }
                }
                Primitive::StrSlice | Primitive::Global => {}
            }
            None
        }
        TypX::FnDef(..) => None,
    }
}

pub(crate) fn datatype_box_prefix(ctx: &Ctx, typ: &Typ) -> Option<Path> {
    match &**typ {
        TypX::Datatype(path, _, _) => {
            if ctx.datatype_is_transparent[path] {
                Some(path.clone())
            } else {
                if let Some(monotyp) = typ_as_mono(typ) {
                    Some(crate::sst_to_air::monotyp_to_path(&monotyp))
                } else {
                    None
                }
            }
        }
        _ => None,
    }
}

fn prefix_typ_as_mono<F: Fn(&Path) -> Ident>(f: F, typ: &Typ, item: &str) -> Option<Ident> {
    if let Some(monotyp) = typ_as_mono(typ) {
        let dpath = crate::sst_to_air::monotyp_to_path(&monotyp);
        Some(f(&dpath))
    } else {
        panic!("{} should be boxed", item)
    }
}

fn try_box(ctx: &Ctx, expr: Expr, typ: &Typ) -> Option<Expr> {
    let f_name = match &**typ {
        TypX::Bool => Some(str_ident(crate::def::BOX_BOOL)),
        TypX::Int(_) => Some(str_ident(crate::def::BOX_INT)),
        TypX::Tuple(_) => None,
        TypX::SpecFn(typs, _) => Some(prefix_box(&prefix_spec_fn_type(typs.len()))),
        TypX::Primitive(Primitive::Array, _) => Some(prefix_box(&crate::def::array_type())),
        TypX::AnonymousClosure(..) => unimplemented!(),
        TypX::Datatype(..) => {
            if let Some(prefix) = datatype_box_prefix(ctx, typ) {
                Some(prefix_box(&prefix))
            } else {
                prefix_typ_as_mono(prefix_box, typ, "abstract datatype")
            }
        }
        TypX::Primitive(_, _) => prefix_typ_as_mono(prefix_box, typ, "primitive type"),
        TypX::FnDef(..) => Some(str_ident(crate::def::BOX_FNDEF)),
        TypX::Decorate(_, _, t) => return try_box(ctx, expr, t),
        TypX::Boxed(_) => None,
        TypX::TypParam(_) => None,
        TypX::Projection { .. } => None,
        TypX::TypeId => None,
        TypX::ConstInt(_) => None,
        TypX::Air(_) => None,
    };
    f_name.map(|f_name| ident_apply(&f_name, &vec![expr]))
}

pub(crate) fn as_box(ctx: &Ctx, expr: Expr, typ: &Typ) -> Expr {
    try_box(ctx, expr.clone(), typ).unwrap_or(expr)
}

fn try_unbox(ctx: &Ctx, expr: Expr, typ: &Typ) -> Option<Expr> {
    let f_name = match &**typ {
        TypX::Bool => Some(str_ident(crate::def::UNBOX_BOOL)),
        TypX::Int(_) => Some(str_ident(crate::def::UNBOX_INT)),
        TypX::Datatype(path, _, _) => {
            if ctx.datatype_is_transparent[path] {
                Some(prefix_unbox(&path))
            } else {
                prefix_typ_as_mono(prefix_unbox, typ, "abstract datatype")
            }
        }
        TypX::Primitive(Primitive::Array, _) => Some(prefix_unbox(&crate::def::array_type())),
        TypX::Primitive(_, _) => prefix_typ_as_mono(prefix_unbox, typ, "primitive type"),
        TypX::FnDef(..) => Some(str_ident(crate::def::UNBOX_FNDEF)),
        TypX::Tuple(_) => None,
        TypX::SpecFn(typs, _) => Some(prefix_unbox(&prefix_spec_fn_type(typs.len()))),
        TypX::AnonymousClosure(..) => unimplemented!(),
        TypX::Decorate(_, _, t) => return try_unbox(ctx, expr, t),
        TypX::Boxed(_) => None,
        TypX::TypParam(_) => None,
        TypX::Projection { .. } => None,
        TypX::TypeId => None,
        TypX::ConstInt(_) => None,
        TypX::Air(_) => None,
    };
    f_name.map(|f_name| ident_apply(&f_name, &vec![expr]))
}

pub fn mask_set_from_spec(spec: &MaskSpec, function_name: &Fun, args: &Vec<Expr>) -> MaskSet {
    match spec {
        MaskSpec::InvariantOpens(exprs) => {
            let mut l = vec![];
            for (i, e) in exprs.iter().enumerate() {
                let expr =
                    ident_apply(&prefix_open_inv(&fun_to_air_ident(function_name), i), &args);
                l.push(crate::inv_masks::MaskSingleton { expr, span: e.span.clone() });
            }
            MaskSet::from_list(l)
        }
        MaskSpec::InvariantOpensExcept(exprs) if exprs.len() == 0 => MaskSet::full(),
        MaskSpec::InvariantOpensExcept(_exprs) => {
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
    let fields = &get_variant(&ctx.global.datatypes[path].1, variant).fields;
    (variant_ident(path, &variant), fields.iter().map(move |f| get_field(binders, &f.name)))
}

fn str_to_const_str(ctx: &Ctx, s: Arc<String>) -> Expr {
    Arc::new(ExprX::Apply(
        str_ident(STRSLICE_NEW_STRLIT),
        Arc::new(vec![Arc::new(ExprX::Const(Constant::Nat({
            use num_bigint::BigUint;
            use sha2::{Digest, Sha512};

            let mut str_hashes = ctx.string_hashes.borrow_mut();

            let mut hasher = Sha512::new();
            hasher.update(&*s);
            let res = hasher.finalize();

            #[cfg(target_endian = "little")]
            let num = BigUint::from_bytes_le(&res[..]);

            #[cfg(target_endian = "big")]
            let num = BigUint::from_bytes_be(&res[..]);

            let num_str = Arc::new(num.to_string());

            if let Some(other_s) = str_hashes.insert(num, s.clone()) {
                if other_s != s {
                    panic!(
                        "sha512 collision detected, choosing to panic over introducing unsoundness"
                    );
                }
            }
            num_str
        })))]),
    ))
}

fn char_to_unicode_repr(c: char) -> u32 {
    c as u32
}

pub(crate) fn constant_to_expr(ctx: &Ctx, constant: &crate::ast::Constant) -> Expr {
    match constant {
        crate::ast::Constant::Bool(b) => Arc::new(ExprX::Const(Constant::Bool(*b))),
        crate::ast::Constant::Int(i) => big_int_to_expr(i),
        crate::ast::Constant::StrSlice(s) => str_to_const_str(ctx, s.clone()),
        crate::ast::Constant::Char(c) => {
            Arc::new(ExprX::Const(Constant::Nat(Arc::new(char_to_unicode_repr(*c).to_string()))))
        }
    }
}

fn exp_get_custom_err(exp: &Exp) -> Option<Arc<String>> {
    match &exp.x {
        ExpX::UnaryOpr(UnaryOpr::Box(_), e) => exp_get_custom_err(e),
        ExpX::UnaryOpr(UnaryOpr::Unbox(_), e) => exp_get_custom_err(e),
        ExpX::UnaryOpr(UnaryOpr::CustomErr(s), _) => Some(s.clone()),
        _ => None,
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
    pub is_singular: bool,
}

impl ExprCtxt {
    pub(crate) fn new() -> Self {
        ExprCtxt { mode: ExprMode::Body, is_singular: false }
    }
    pub(crate) fn new_mode(mode: ExprMode) -> Self {
        ExprCtxt { mode, is_singular: false }
    }
    pub(crate) fn new_mode_singular(mode: ExprMode, is_singular: bool) -> Self {
        ExprCtxt { mode, is_singular }
    }
}

fn clip_bitwise_result(bit_expr: ExprX, exp: &Exp) -> Result<Expr, VirErr> {
    if let TypX::Int(range) = &*undecorate_typ(&exp.typ) {
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
        return Err(error(
            &exp.span,
            format!("In translating Bitwise operator, encountered non-integer operand",),
        ));
    }
}

fn check_bitwidth_typ_matches(typ: &Typ, w: IntegerTypeBitwidth, signed: bool) -> bool {
    if let TypX::Int(range) = &*undecorate_typ(typ) {
        match (range, signed, w) {
            (IntRange::U(w), false, IntegerTypeBitwidth::Width(w2)) if *w == w2 => true,
            (IntRange::I(w), true, IntegerTypeBitwidth::Width(w2)) if *w == w2 => true,
            (IntRange::USize, false, IntegerTypeBitwidth::ArchWordSize) => true,
            (IntRange::ISize, true, IntegerTypeBitwidth::ArchWordSize) => true,
            _ => false,
        }
    } else {
        false
    }
}

// Generate a unique quantifier ID and map it to the quantifier's span
pub(crate) fn new_user_qid(ctx: &Ctx, exp: &Exp) -> Qid {
    let fun_name = fun_as_friendly_rust_name(
        &ctx.fun.as_ref().expect("Expressions are expected to be within a function").current_fun,
    );
    let qcount = ctx.quantifier_count.get();
    let qid = new_user_qid_name(&fun_name, qcount);
    ctx.quantifier_count.set(qcount + 1);
    let trigs = match &exp.x {
        ExpX::Bind(bnd, _) => match &bnd.x {
            BndX::Quant(_, _, trigs) => trigs,
            BndX::Choose(_, trigs, _) => trigs,
            BndX::Lambda(_, trigs) => trigs,
            _ => panic!(
                "internal error: user quantifier expressions should only be Quant, Choose, or Lambda; found {:?}",
                bnd.x
            ),
        },
        _ => panic!(
            "internal error: user quantifier expressions should only be Bind expressions; found {:?}",
            exp.x
        ),
    };
    let bnd_info = BndInfo {
        fun: ctx
            .fun
            .as_ref()
            .expect("expressions are expected to be within a function")
            .current_fun
            .clone(),
        user: Some(BndInfoUser { span: exp.span.clone(), trigs: trigs.clone() }),
    };
    ctx.global.qid_map.borrow_mut().insert(qid.clone(), bnd_info);
    Some(Arc::new(qid))
}

pub(crate) fn exp_to_expr(ctx: &Ctx, exp: &Exp, expr_ctxt: &ExprCtxt) -> Result<Expr, VirErr> {
    let result = match &exp.x {
        ExpX::Const(c) => {
            let expr = constant_to_expr(ctx, c);
            expr
        }
        ExpX::Var(x) => string_var(&suffix_local_unique_id(x)),
        ExpX::VarLoc(x) => string_var(&suffix_local_unique_id(x)),
        ExpX::VarAt(x, VarAt::Pre) => match expr_ctxt.mode {
            ExprMode::Spec => string_var(&prefix_pre_var(&suffix_local_unique_id(x))),
            ExprMode::Body => {
                Arc::new(ExprX::Old(snapshot_ident(SNAPSHOT_PRE), suffix_local_unique_id(x)))
            }
            ExprMode::BodyPre => string_var(&suffix_local_unique_id(x)),
        },
        ExpX::StaticVar(f) => string_var(&static_name(f)),
        ExpX::Loc(e0) => exp_to_expr(ctx, e0, expr_ctxt)?,
        ExpX::Old(span, x) => Arc::new(ExprX::Old(span.clone(), suffix_local_unique_id(x))),
        ExpX::Call(f @ (CallFun::Fun(..) | CallFun::Recursive(_)), typs, args) => {
            let x_name = match f {
                CallFun::Fun(x, _) => x.clone(),
                CallFun::Recursive(x) => crate::def::prefix_recursive_fun(&x),
                _ => panic!(),
            };
            let name = suffix_global_id(&fun_to_air_ident(&x_name));
            let mut exprs: Vec<Expr> = typs.iter().map(typ_to_ids).flatten().collect();
            for arg in args.iter() {
                exprs.push(exp_to_expr(ctx, arg, expr_ctxt)?);
            }
            ident_apply(&name, &exprs)
        }
        ExpX::Call(CallFun::InternalFun(func), typs, args) => {
            // These functions are special-cased to not take a decoration argument for
            // the first type parameter.
            let skip_first_decoration = match func {
                InternalFun::ClosureReq | InternalFun::ClosureEns => true,
                _ => false,
            };

            let mut exprs: Vec<Expr> = typs.iter().map(typ_to_ids).flatten().collect();
            if crate::context::DECORATE && skip_first_decoration {
                exprs.remove(0);
            }
            for arg in args.iter() {
                exprs.push(exp_to_expr(ctx, arg, expr_ctxt)?);
            }
            Arc::new(ExprX::Apply(
                match func {
                    InternalFun::ClosureReq => str_ident(crate::def::CLOSURE_REQ),
                    InternalFun::ClosureEns => str_ident(crate::def::CLOSURE_ENS),
                    InternalFun::CheckDecreaseInt => str_ident(crate::def::CHECK_DECREASE_INT),
                    InternalFun::CheckDecreaseHeight => {
                        str_ident(crate::def::CHECK_DECREASE_HEIGHT)
                    }
                },
                Arc::new(exprs),
            ))
        }
        ExpX::CallLambda(e0, args) => {
            let e0 = exp_to_expr(ctx, e0, expr_ctxt)?;
            let args = vec_map_result(args, |e| exp_to_expr(ctx, e, expr_ctxt))?;
            Arc::new(ExprX::ApplyFun(typ_to_air(ctx, &exp.typ), e0, Arc::new(args)))
        }
        ExpX::Ctor(path, variant, binders) => {
            let (variant, args) = ctor_to_apply(ctx, path, variant, binders);
            let args = args
                .map(|b| exp_to_expr(ctx, &b.a, expr_ctxt))
                .collect::<Result<Vec<_>, VirErr>>()?;
            Arc::new(ExprX::Apply(variant, Arc::new(args)))
        }
        ExpX::ExecFnByName(_fun) => {
            Arc::new(ExprX::Apply(str_ident(crate::def::FNDEF_SINGLETON), Arc::new(vec![])))
        }
        ExpX::ArrayLiteral(es) => {
            let mut exprs: Vec<Expr> = vec![];
            for e in es.iter() {
                exprs.push(exp_to_expr(ctx, e, expr_ctxt)?);
            }
            let typ = match &*exp.typ {
                TypX::Decorate(_dec, _, t) => match &**t {
                    TypX::Boxed(t) => match &**t {
                        TypX::Primitive(Primitive::Array, typs) => typs[0].clone(),
                        _ => {
                            panic!("Failed to extract the array literal element type for {:?}", exp)
                        }
                    },
                    _ => panic!(
                        "Failed to extract the array literal element boxed type for {:?}",
                        exp
                    ),
                },
                TypX::Boxed(t) => match &**t {
                    TypX::Primitive(Primitive::Array, typs) => typs[0].clone(),
                    _ => panic!(
                        "Failed to directly extract the array literal element type for {:?}",
                        exp
                    ),
                },
                _ => panic!(
                    "Failed to extract the decorated array literal element type for {:?}",
                    exp
                ),
            };
            let mut args = typ_to_ids(&typ);
            let len = mk_nat(es.len());
            let array_lit = Arc::new(ExprX::Array(Arc::new(exprs)));
            args.push(len);
            args.push(array_lit);
            str_apply(crate::def::ARRAY_NEW, &args)
        }
        ExpX::NullaryOpr(crate::ast::NullaryOpr::ConstGeneric(c)) => {
            str_apply(crate::def::CONST_INT, &vec![typ_to_id(c)])
        }
        ExpX::NullaryOpr(crate::ast::NullaryOpr::TraitBound(p, ts)) => {
            if let Some(e) = crate::traits::trait_bound_to_air(ctx, p, ts) {
                e
            } else {
                air::ast_util::mk_true()
            }
        }
        ExpX::NullaryOpr(crate::ast::NullaryOpr::TypEqualityBound(p, ts, x, t)) => {
            crate::traits::typ_equality_bound_to_air(ctx, p, ts, x, t)
        }
        ExpX::NullaryOpr(crate::ast::NullaryOpr::ConstTypBound(t1, t2)) => {
            crate::traits::const_typ_bound_to_air(ctx, t1, t2)
        }
        ExpX::NullaryOpr(crate::ast::NullaryOpr::NoInferSpecForLoopIter) => {
            panic!("internal error: NoInferSpecForLoopIter")
        }
        ExpX::Unary(op, exp) => match op {
            UnaryOp::StrLen => Arc::new(ExprX::Apply(
                str_ident(STRSLICE_LEN),
                Arc::new(vec![exp_to_expr(ctx, exp, expr_ctxt)?]),
            )),
            UnaryOp::StrIsAscii => Arc::new(ExprX::Apply(
                str_ident(STRSLICE_IS_ASCII),
                Arc::new(vec![exp_to_expr(ctx, exp, expr_ctxt)?]),
            )),
            UnaryOp::Not => mk_not(&exp_to_expr(ctx, exp, expr_ctxt)?),
            UnaryOp::BitNot(width_opt) => {
                let expr = exp_to_expr(ctx, exp, expr_ctxt)?;
                let expr = try_box(ctx, expr, &exp.typ).expect("Box");
                let bit_expr =
                    ExprX::Apply(Arc::new(crate::def::BIT_NOT.to_string()), Arc::new(vec![expr]));
                if let Some(width) = width_opt {
                    if !check_bitwidth_typ_matches(&exp.typ, *width, false) {
                        return Err(error(
                            &exp.span,
                            format!("Verus Internal Error: BitNot: type doesn't match"),
                        ));
                    }
                    return clip_bitwise_result(bit_expr, exp);
                } else {
                    return Ok(Arc::new(bit_expr));
                }
            }
            UnaryOp::HeightTrigger => {
                str_apply(crate::def::HEIGHT, &vec![exp_to_expr(ctx, exp, expr_ctxt)?])
            }
            UnaryOp::Trigger(_) => exp_to_expr(ctx, exp, expr_ctxt)?,
            UnaryOp::Clip { range: IntRange::Int, .. } => exp_to_expr(ctx, exp, expr_ctxt)?,
            UnaryOp::Clip { range, .. } => {
                let expr = exp_to_expr(ctx, exp, expr_ctxt)?;
                let f_name = match range {
                    IntRange::Int => panic!("internal error: Int"),
                    IntRange::Nat => crate::def::NAT_CLIP,
                    IntRange::Char => crate::def::CHAR_CLIP,
                    IntRange::U(_) | IntRange::USize => crate::def::U_CLIP,
                    IntRange::I(_) | IntRange::ISize => crate::def::I_CLIP,
                };
                apply_range_fun(&f_name, &range, vec![expr])
            }
            UnaryOp::CoerceMode { .. } => {
                panic!("internal error: TupleField should have been removed before here")
            }
            UnaryOp::MustBeFinalized | UnaryOp::MustBeElaborated => {
                panic!("internal error: Exp not finalized: {:?}", exp)
            }
            UnaryOp::InferSpecForLoopIter { .. } => {
                // loop_inference failed to promote to Some, so demote to None
                let exp = crate::loop_inference::make_option_exp(None, &exp.span, &exp.typ);
                exp_to_expr(ctx, &exp, expr_ctxt)?
            }
            UnaryOp::CastToInteger => {
                panic!("internal error: CastToInteger should have been removed before here")
            }
        },
        ExpX::UnaryOpr(op, exp) => match op {
            UnaryOpr::Box(typ) => {
                let expr = exp_to_expr(ctx, exp, expr_ctxt)?;
                try_box(ctx, expr, typ).unwrap_or_else(|| panic!("Box {:?}", typ))
            }
            UnaryOpr::Unbox(typ) => {
                let expr = exp_to_expr(ctx, exp, expr_ctxt)?;
                try_unbox(ctx, expr.clone(), typ).unwrap_or_else(|| panic!("Unbox: {:?}", expr))
            }
            UnaryOpr::HasType(typ) => {
                let expr = exp_to_expr(ctx, exp, expr_ctxt)?;
                if let Some(inv) = typ_invariant(ctx, typ, &expr) {
                    inv
                } else {
                    air::ast_util::mk_true()
                }
            }
            UnaryOpr::IsVariant { datatype, variant } => {
                let expr = exp_to_expr(ctx, exp, expr_ctxt)?;
                let name = is_variant_ident(datatype, variant);
                Arc::new(ExprX::Apply(name, Arc::new(vec![expr])))
            }
            UnaryOpr::TupleField { .. } => {
                panic!("internal error: TupleField should have been removed before here")
            }
            UnaryOpr::IntegerTypeBound(IntegerTypeBoundKind::SignedMin, _) => {
                let expr = exp_to_expr(ctx, exp, expr_ctxt)?;
                let name = Arc::new(I_LO.to_string());
                Arc::new(ExprX::Apply(name, Arc::new(vec![expr])))
            }
            UnaryOpr::IntegerTypeBound(IntegerTypeBoundKind::SignedMax, _) => {
                let expr = exp_to_expr(ctx, exp, expr_ctxt)?;
                let name = Arc::new(I_HI.to_string());
                let x = Arc::new(ExprX::Apply(name, Arc::new(vec![expr])));
                mk_sub(&x, &mk_nat(1))
            }
            UnaryOpr::IntegerTypeBound(IntegerTypeBoundKind::UnsignedMax, _) => {
                let expr = exp_to_expr(ctx, exp, expr_ctxt)?;
                let name = Arc::new(U_HI.to_string());
                let x = Arc::new(ExprX::Apply(name, Arc::new(vec![expr])));
                mk_sub(&x, &mk_nat(1))
            }
            UnaryOpr::IntegerTypeBound(IntegerTypeBoundKind::ArchWordBits, _) => {
                let name = Arc::new(ARCH_SIZE.to_string());
                Arc::new(ExprX::Var(name))
            }
            UnaryOpr::Field(FieldOpr { datatype, variant, field, get_variant: _, check: _ }) => {
                let expr = exp_to_expr(ctx, exp, expr_ctxt)?;
                Arc::new(ExprX::Apply(
                    variant_field_ident(datatype, variant, field),
                    Arc::new(vec![expr]),
                ))
            }
            UnaryOpr::CustomErr(_) => {
                // CustomErr is handled by split_expression. Maybe it could
                // be useful in the 'normal' case too, but right now, we just
                // ignore it here.
                return exp_to_expr(ctx, exp, expr_ctxt);
            }
        },
        ExpX::Binary(op, lhs, rhs) => {
            let wrap_arith = true; // use Add, Sub, etc. wrappers to allow triggers on +, -, etc.
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
                BinaryOp::HeightCompare { strictly_lt, recursive_function_field } => {
                    let lhh = str_apply(crate::def::HEIGHT, &vec![lh]);
                    let rh = if *recursive_function_field {
                        str_apply(crate::def::HEIGHT_REC_FUN, &vec![rh])
                    } else {
                        rh
                    };
                    let rhh = str_apply(crate::def::HEIGHT, &vec![rh]);
                    if *strictly_lt {
                        return Ok(str_apply(crate::def::HEIGHT_LT, &vec![lhh, rhh]));
                    } else {
                        return Ok(mk_eq(&lhh, &rhh));
                    }
                }
                BinaryOp::Arith(ArithOp::Add, _) if wrap_arith => {
                    return Ok(str_apply(crate::def::ADD, &vec![lh, rh]));
                }
                BinaryOp::Arith(ArithOp::Sub, _) if wrap_arith => {
                    return Ok(str_apply(crate::def::SUB, &vec![lh, rh]));
                }
                BinaryOp::Arith(ArithOp::Add, _) => {
                    ExprX::Multi(MultiOp::Add, Arc::new(vec![lh, rh]))
                }
                BinaryOp::Arith(ArithOp::Sub, _) => {
                    ExprX::Multi(MultiOp::Sub, Arc::new(vec![lh, rh]))
                }
                BinaryOp::Arith(ArithOp::Mul, _) if wrap_arith || !has_const => {
                    return Ok(str_apply(crate::def::MUL, &vec![lh, rh]));
                }
                BinaryOp::Arith(ArithOp::EuclideanDiv, _) if wrap_arith || !has_const => {
                    return Ok(str_apply(crate::def::EUC_DIV, &vec![lh, rh]));
                }
                // REVIEW: consider introducing singular_mod more earlier pipeline (e.g. from syntax macro?)
                BinaryOp::Arith(ArithOp::EuclideanMod, _) if expr_ctxt.is_singular => {
                    return Ok(str_apply(crate::def::SINGULAR_MOD, &vec![lh, rh]));
                }
                BinaryOp::Arith(ArithOp::EuclideanMod, _) if wrap_arith || !has_const => {
                    return Ok(str_apply(crate::def::EUC_MOD, &vec![lh, rh]));
                }
                BinaryOp::Arith(ArithOp::Mul, _) => {
                    ExprX::Multi(MultiOp::Mul, Arc::new(vec![lh, rh]))
                }
                BinaryOp::Ne => {
                    let eq = ExprX::Binary(air::ast::BinaryOp::Eq, lh, rh);
                    ExprX::Unary(air::ast::UnaryOp::Not, Arc::new(eq))
                }
                BinaryOp::StrGetChar => ExprX::Apply(
                    str_ident(STRSLICE_GET_CHAR),
                    Arc::new(vec![
                        exp_to_expr(ctx, lhs, expr_ctxt)?,
                        exp_to_expr(ctx, rhs, expr_ctxt)?,
                    ]),
                ),
                BinaryOp::ArrayIndex => {
                    let ts = match &*lhs.typ {
                        TypX::Primitive(Primitive::Array, ts) if ts.len() == 2 => ts,
                        _ => panic!("internal error: unexpected ArrayIndex type"),
                    };
                    let mut args: Vec<Expr> = ts.iter().map(typ_to_ids).flatten().collect();
                    args.push(exp_to_expr(ctx, lhs, expr_ctxt)?);
                    args.push(exp_to_expr(ctx, rhs, expr_ctxt)?);
                    ExprX::Apply(str_ident(crate::def::ARRAY_INDEX), Arc::new(args))
                }
                // here the binary bitvector Ops are translated into the integer versions
                // Similar to typ_invariant(), make obvious range according to bit-width
                BinaryOp::Bitwise(bo, _) => {
                    let box_lh = try_box(ctx, lh, &lhs.typ).expect("Box");
                    let box_rh = try_box(ctx, rh, &rhs.typ).expect("Box");

                    // For XOR, AND, OR, and SHR, the result of the operation should
                    // always be in-bounds. We emit a clip which will trigger an axiom
                    // in the prelude so our solver will know the clip is unnecessary.
                    //
                    // For SHL, the clip *is* meaningful.

                    let fname = match bo {
                        BitwiseOp::BitXor => crate::def::BIT_XOR,
                        BitwiseOp::BitAnd => crate::def::BIT_AND,
                        BitwiseOp::BitOr => crate::def::BIT_OR,
                        BitwiseOp::Shl(width, signed) => {
                            // The clip (below) is based on the type so we need to make
                            // sure that the clip is what we expected based on Shl's arguments
                            if !check_bitwidth_typ_matches(&exp.typ, *width, *signed) {
                                return Err(error(
                                    &exp.span,
                                    format!("Verus Internal Error: BitShl: type doesn't match"),
                                ));
                            }
                            crate::def::BIT_SHL
                        }
                        BitwiseOp::Shr(_) => crate::def::BIT_SHR,
                    };
                    let args = vec![box_lh, box_rh];
                    let bit_expr = ExprX::Apply(Arc::new(fname.to_string()), Arc::new(args));

                    return clip_bitwise_result(bit_expr, exp);
                }
                _ => {
                    let aop = match op {
                        BinaryOp::And => unreachable!(),
                        BinaryOp::Or => unreachable!(),
                        BinaryOp::Xor => unreachable!(),
                        BinaryOp::Implies => unreachable!(),
                        BinaryOp::HeightCompare { .. } => unreachable!(),
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
                        BinaryOp::StrGetChar => unreachable!(),
                        BinaryOp::ArrayIndex => unreachable!(),
                    };
                    ExprX::Binary(aop, lh, rh)
                }
            };
            Arc::new(expx)
        }
        ExpX::BinaryOpr(crate::ast::BinaryOpr::ExtEq(deep, t), lhs, rhs) => {
            let mut args = vec![Arc::new(ExprX::Const(Constant::Bool(*deep))), typ_to_id(t)];
            args.push(exp_to_expr(ctx, lhs, expr_ctxt)?);
            args.push(exp_to_expr(ctx, rhs, expr_ctxt)?);
            str_apply(crate::def::EXT_EQ, &args)
        }
        ExpX::If(e1, e2, e3) => mk_ite(
            &exp_to_expr(ctx, e1, expr_ctxt)?,
            &exp_to_expr(ctx, e2, expr_ctxt)?,
            &exp_to_expr(ctx, e3, expr_ctxt)?,
        ),
        ExpX::WithTriggers(_triggers, body) => exp_to_expr(ctx, body, expr_ctxt)?,
        ExpX::Bind(bnd, e) => match &bnd.x {
            BndX::Let(binders) => {
                let expr = exp_to_expr(ctx, e, expr_ctxt)?;
                let mut bs: Vec<Binder<Expr>> = Vec::new();
                for b in binders.iter() {
                    let e = exp_to_expr(ctx, &b.a, expr_ctxt)?;
                    bs.push(Arc::new(BinderX { name: b.name.lower(), a: e }));
                }
                air::ast_util::mk_let(&bs, &expr)
            }
            BndX::Quant(quant, binders, trigs) => {
                let expr = exp_to_expr(ctx, e, expr_ctxt)?;
                let mut invs: Vec<Expr> = Vec::new();
                for binder in binders.iter() {
                    let typ_inv = typ_invariant(ctx, &binder.a, &ident_var(&binder.name.lower()));
                    if let Some(inv) = typ_inv {
                        invs.push(inv);
                    }
                }
                let inv = mk_and(&invs);
                let expr = match quant.quant {
                    Quant::Forall => mk_implies(&inv, &expr),
                    Quant::Exists => mk_and(&vec![inv, expr]),
                };
                let mut bs: Vec<Binder<air::ast::Typ>> = Vec::new();
                for binder in binders.iter() {
                    let typ = typ_to_air(ctx, &binder.a);
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
                    vec_map_result(trig, |x| exp_to_expr(ctx, x, expr_ctxt)).map(|v| Arc::new(v))
                })?;
                let qid = new_user_qid(ctx, &exp);
                air::ast_util::mk_quantifier(quant.quant, &bs, &triggers, qid, &expr)
            }
            BndX::Lambda(binders, trigs) => {
                let expr = exp_to_expr(ctx, e, expr_ctxt)?;
                let binders = vec_map(&*binders, |b| {
                    Arc::new(BinderX { name: b.name.lower(), a: typ_to_air(ctx, &b.a) })
                });
                let triggers = vec_map_result(&*trigs, |trig| {
                    vec_map_result(trig, |x| exp_to_expr(ctx, x, expr_ctxt)).map(|v| Arc::new(v))
                })?;
                let qid = (triggers.len() > 0).then(|| ()).and_then(|_| new_user_qid(ctx, &exp));
                let lambda = air::ast_util::mk_lambda(&binders, &triggers, qid, &expr);
                str_apply(crate::def::MK_FUN, &vec![lambda])
            }
            BndX::Choose(binders, trigs, cond) => {
                let mut bs: Vec<Binder<air::ast::Typ>> = Vec::new();
                let mut invs: Vec<Expr> = Vec::new();
                for b in binders.iter() {
                    let name = b.name.lower();
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
                        let args = vec![choose_expr, typ_to_id(typ)];
                        choose_expr = str_apply(crate::def::AS_TYPE, &args);
                    }
                    _ => {}
                }
                choose_expr
            }
        },
        ExpX::FuelConst(i) => {
            let mut e = str_var(crate::def::ZERO);
            for _j in 0..*i {
                e = str_apply(SUCC, &vec![e]);
            }
            e
        }
        ExpX::Interp(_) => {
            panic!("Found an interpreter expression {:?} outside the interpreter", exp)
        }
    };
    Ok(result)
}

#[derive(Debug)]
struct LoopInfo {
    loop_isolation: bool,
    is_for_loop: bool,
    label: Option<String>,
    loop_id: u64,
    air_break_label: Ident,
    some_cond: bool,
    invs_entry: Arc<Vec<(Span, Expr, Option<Arc<String>>, bool)>>,
    invs_exit: Arc<Vec<(Span, Expr, Option<Arc<String>>, bool)>>,
    decrease: crate::sst::Exps,
}

enum ReasonForNoUnwind {
    Function,
    OpenInvariant(Span),
}

enum UnwindAir {
    MayUnwind,
    NoUnwind(ReasonForNoUnwind),
    NoUnwindWhen(Expr),
}

struct State {
    local_shared: Vec<Decl>, // shared between all queries for a single function
    may_be_used_in_old: HashSet<UniqueIdent>, // vars that might have a 'PRE' snapshot, needed for while loop generation
    commands: Vec<CommandsWithContext>,
    snapshot_count: u32, // Used to ensure unique Idents for each snapshot
    sids: Vec<Ident>, // a stack of snapshot ids, the top one should dominate the current position in the AST
    snap_map: Vec<(Span, SnapPos)>, // Maps each statement's span to the closest dominating snapshot's ID
    assign_map: AssignMap, // Maps Maps each statement's span to the assigned variables (that can potentially be queried)
    mask: MaskSet,         // set of invariants that are allowed to be opened
    unwind: UnwindAir,
    post_condition_info: PostConditionInfo,
    loop_infos: Vec<LoopInfo>,
    static_prelude: Vec<Stmt>,
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
        let spos = SnapPos { snapshot_id: self.get_current_sid(), kind };
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

pub(crate) fn assume_var(span: &Span, x: &UniqueIdent, exp: &Exp) -> Stm {
    let x_var = SpannedTyped::new(&span, &exp.typ, ExpX::Var(x.clone()));
    let eqx = ExpX::Binary(BinaryOp::Eq(Mode::Spec), x_var, exp.clone());
    let eq = SpannedTyped::new(&span, &Arc::new(TypX::Bool), eqx);
    Spanned::new(span.clone(), StmX::Assume(eq))
}

pub(crate) fn one_stmt(stmts: Vec<Stmt>) -> Stmt {
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
            let FieldOpr { datatype: dt, variant, field: _, get_variant: _, check: _ } =
                &updates[0][0];
            for u in updates {
                assert!(u[0].datatype == *dt && u[0].variant == *variant);
                updated_fields.entry(&u[0].field).or_insert(Vec::new()).push(u[1..].to_vec());
            }
            let datatype = &ctx.datatype_map[dt];
            let datatype_fields = &get_variant(&datatype.x.variants, variant).fields;
            let mut box_unbox_eq: Vec<Expr> = Vec::new();
            let exps_for_fields =
                vec_map_result(&**datatype_fields, |field: &Binder<(Typ, Mode, Visibility)>| {
                    let base_exp = if let TypX::Boxed(base_typ) = &*undecorate_typ(&base.typ) {
                        // TODO this replicates logic from poly, but factoring it out is currently tricky
                        // because we don't have a representation for a variable used as a location in VIR
                        if crate::poly::typ_is_poly(ctx, base_typ) {
                            base.clone()
                        } else {
                            let op = UnaryOpr::Unbox(base_typ.clone());
                            let exprx = ExpX::UnaryOpr(op, base.clone());
                            let unbox = SpannedTyped::new(&base.span, base_typ, exprx);
                            if box_unbox_eq.len() == 0 {
                                // trigger Box(Unbox(base)) so that has_type succeeds on base
                                let box_op = UnaryOpr::Box(base_typ.clone());
                                let exprx = ExpX::UnaryOpr(box_op, unbox.clone());
                                let box_unbox = SpannedTyped::new(&base.span, &base.typ, exprx);
                                let eq = ExprX::Binary(
                                    air::ast::BinaryOp::Eq,
                                    exp_to_expr(ctx, &box_unbox, expr_ctxt)?,
                                    exp_to_expr(ctx, &base, expr_ctxt)?,
                                );
                                box_unbox_eq.push(Arc::new(eq));
                            }
                            unbox
                        }
                    } else {
                        base.clone()
                    };

                    let typ_args = typ_args_for_datatype_typ(&base_exp.typ);
                    let typ = subst_typ_for_datatype(&datatype.x.typ_params, typ_args, &field.a.0);
                    let typ = if crate::poly::typ_is_poly(ctx, &field.a.0) {
                        crate::poly::coerce_typ_to_poly(ctx, &typ)
                    } else {
                        crate::poly::coerce_typ_to_native(ctx, &typ)
                    };

                    let field_exp = SpannedTyped::new(
                        stm_span,
                        &typ,
                        ExpX::UnaryOpr(
                            UnaryOpr::Field(FieldOpr {
                                datatype: dt.clone(),
                                variant: variant.clone(),
                                field: field.name.clone(),
                                get_variant: false,
                                check: VariantCheck::None,
                            }),
                            base_exp,
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
            Ok(exps_for_fields.into_iter().flatten().chain(box_unbox_eq.into_iter()).collect())
        }
    }
}

// fn stm_to_stmts(ctx: &Ctx, state: &mut State, stm: &Stm) -> Result<Vec<Stmt>, VirErr> {
//     let expr_ctxt = ExprCtxt { mode: ExprMode::Body, is_bit_vector: false };
//     let result = match &stm.x {

fn stm_to_stmts(ctx: &Ctx, state: &mut State, stm: &Stm) -> Result<Vec<Stmt>, VirErr> {
    let expr_ctxt = &ExprCtxt::new();
    let result = match &stm.x {
        StmX::Call { fun, resolved_method, mode, typ_args: typs, args, split, dest, assert_id } => {
            assert!(split.is_none());
            let mut stmts: Vec<Stmt> = Vec::new();
            let func = &ctx.func_map[fun];

            let mut req_args: Vec<Expr> = typs.iter().map(typ_to_ids).flatten().collect();
            for arg in args.iter() {
                req_args.push(exp_to_expr(ctx, arg, expr_ctxt)?);
            }
            let req_args = Arc::new(req_args);

            if func.x.require.len() > 0
                && (!ctx.checking_spec_preconditions_for_non_spec() || *mode == Mode::Spec)
                // don't check recommends during decreases checking; these are separate passes:
                && !ctx.checking_spec_decreases()
            {
                let f_req = prefix_requires(&fun_to_air_ident(&func.x.name));

                let e_req = Arc::new(ExprX::Apply(f_req, req_args.clone()));
                let description =
                    match (ctx.checking_spec_preconditions(), &func.x.attrs.custom_req_err) {
                        (true, None) => "recommendation not met".to_string(),
                        (_, None) => crate::def::PRECONDITION_FAILURE.to_string(),
                        (_, Some(s)) => s.clone(),
                    };
                let error = error(&stm.span, description);
                let filter = Some(fun_to_air_ident(&func.x.name));
                stmts.push(Arc::new(StmtX::Assert(assert_id.clone(), error, filter, e_req)));
            }

            let callee_unwind_spec = func.x.unwind_spec_or_default();
            let callee_never_unwinds = matches!(callee_unwind_spec, UnwindSpec::NoUnwind);
            if !matches!(state.unwind, UnwindAir::MayUnwind)
                && !callee_never_unwinds
                && !ctx.checking_spec_preconditions()
            {
                let e1 = match &state.unwind {
                    UnwindAir::MayUnwind => unreachable!(),
                    UnwindAir::NoUnwind(_) => Arc::new(ExprX::Const(Constant::Bool(true))),
                    UnwindAir::NoUnwindWhen(expr) => expr.clone(),
                };
                let e2 = match &callee_unwind_spec {
                    UnwindSpec::MayUnwind => Arc::new(ExprX::Const(Constant::Bool(false))),
                    UnwindSpec::NoUnwind => unreachable!(),
                    UnwindSpec::NoUnwindWhen(_) => {
                        let f_unwind = prefix_no_unwind_when(&fun_to_air_ident(&func.x.name));
                        Arc::new(ExprX::Apply(f_unwind, req_args.clone()))
                    }
                };
                let error = match &state.unwind {
                    UnwindAir::MayUnwind => unreachable!(),
                    UnwindAir::NoUnwind(ReasonForNoUnwind::Function) => error_with_label(
                        &stm.span,
                        "cannot show this call will not unwind, in function marked 'no_unwind'",
                        "this call might unwind",
                    ),
                    UnwindAir::NoUnwind(ReasonForNoUnwind::OpenInvariant(span)) => {
                        error_with_label(
                            &stm.span,
                            "cannot show this call will not unwind",
                            "this call might unwind",
                        )
                        .secondary_label(span, "unwinding is not allowed in this invariant block")
                    }
                    UnwindAir::NoUnwindWhen(_e) => error_with_label(
                        &stm.span,
                        "cannot show this call will not unwind, in function marked 'no_unwind'",
                        "this call might unwind",
                    ),
                };
                let error = if let UnwindSpec::NoUnwindWhen(e) = &callee_unwind_spec {
                    error.secondary_label(
                        &e.span,
                        "this conditition needs to hold to show that the callee will not unwind",
                    )
                } else {
                    error.secondary_label(
                        &func.span,
                        "perhaps you need to mark this function as 'no_unwind'?",
                    )
                };
                let e = mk_implies(&e1, &e2);
                stmts.push(Arc::new(StmtX::Assert(None, error, None, e)));
            }

            let callee_mask_set =
                mask_set_from_spec(&func.x.mask_spec_or_default(), &func.x.name, &req_args);
            if !ctx.checking_spec_preconditions() {
                callee_mask_set.assert_is_contained_in(&state.mask, &stm.span, &mut stmts);
            }

            let typ_args: Vec<Expr> = typs.iter().map(typ_to_ids).flatten().collect();
            if func.x.params.iter().any(|p| p.x.is_mut) && ctx.debug {
                unimplemented!("&mut args are unsupported in debugger mode");
            }
            let mut call_snapshot = false;
            let mut ens_args_wo_typ = Vec::new();
            let mut mutated_fields: BTreeMap<_, LocFieldInfo<Vec<_>>> = BTreeMap::new();
            for (param, arg) in func.x.params.iter().zip(args.iter()) {
                let arg_x = if let Some(Dest { dest, is_init: _ }) = dest {
                    let var = get_loc_var(dest);
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

            let (has_ens, ens_fun, ens_typ_args) = match resolved_method {
                Some((res_fun, res_typs)) if ctx.funcs_with_ensure_predicate[res_fun] => {
                    // Use ens predicate for the statically-resolved function
                    let res_typ_args = res_typs.iter().map(typ_to_ids).flatten().collect();
                    (true, res_fun, res_typ_args)
                }
                _ if ctx.funcs_with_ensure_predicate[&func.x.name] => {
                    // Use ens predicate for the generic function
                    (true, &func.x.name, typ_args)
                }
                _ => {
                    // No ens predicate
                    (false, &func.x.name, typ_args)
                }
            };

            let mut ens_args: Vec<_> =
                ens_typ_args.into_iter().chain(ens_args_wo_typ.into_iter()).collect();
            if func.x.has_return() {
                if let Some(Dest { dest, is_init }) = dest {
                    let var = suffix_local_unique_id(&get_loc_var(dest));
                    ens_args.push(exp_to_expr(ctx, &dest, expr_ctxt)?);
                    if !*is_init {
                        let havoc = StmtX::Havoc(var);
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
            }
            if has_ens {
                let f_ens = prefix_ensures(&fun_to_air_ident(&ens_fun));
                let e_ens = Arc::new(ExprX::Apply(f_ens, Arc::new(ens_args)));
                stmts.push(Arc::new(StmtX::Assume(e_ens)));
            }
            vec![Arc::new(StmtX::Block(Arc::new(stmts)))] // wrap in block for readability
        }
        StmX::Assert(assert_id, error, expr) => {
            let air_expr = exp_to_expr(ctx, &expr, expr_ctxt)?;
            let error = match error {
                Some(error) => error.clone(),
                None => error_with_label(
                    &stm.span,
                    "assertion failed".to_string(),
                    "assertion failed".to_string(),
                ),
            };
            if ctx.debug {
                state.map_span(&stm, SpanKind::Full);
            }
            vec![Arc::new(StmtX::Assert(assert_id.clone(), error, None, air_expr))]
        }
        StmX::AssertCompute(..) => {
            panic!("AssertCompute should be removed by sst_elaborate")
        }
        StmX::Return { base_error, ret_exp, inside_body, assert_id } => {
            let skip = if ctx.checking_spec_preconditions() {
                state.post_condition_info.ens_spec_precondition_stms.len() == 0
            } else {
                state.post_condition_info.ens_exprs.len() == 0
            };

            let mut stmts = if skip {
                vec![]
            } else {
                // Set `dest_id` variable to the returned expression.

                let mut stmts = if let Some(dest_id) = state.post_condition_info.dest.clone() {
                    let ret_exp =
                        ret_exp.as_ref().expect("if dest is provided, expr must be provided");
                    stm_to_stmts(ctx, state, &assume_var(&stm.span, &dest_id, ret_exp))?
                } else {
                    // If there is no `dest_id`, then the returned expression
                    // gets ignored. This should happen for functions that
                    // don't return anything (more technically, that return
                    // implicit unit) or other functions that don't have a name
                    // associated to their return value.
                    vec![]
                };

                if ctx.checking_spec_preconditions() {
                    for stm in state.post_condition_info.ens_spec_precondition_stms.clone().iter() {
                        let mut new_stmts = stm_to_stmts(ctx, state, stm)?;
                        stmts.append(&mut new_stmts);
                    }
                } else {
                    for (span, ens) in state.post_condition_info.ens_exprs.clone().iter() {
                        // The base_error should point to the return-statement or
                        // return-expression. Augment with an additional label pointing
                        // to the 'ensures' clause that fails.
                        let error = match state.post_condition_info.kind {
                            PostConditionKind::Ensures => base_error
                                .secondary_label(&span, crate::def::THIS_POST_FAILED.to_string()),
                            PostConditionKind::DecreasesImplicitLemma => base_error.clone(),
                            PostConditionKind::DecreasesBy => {
                                let mut e = (**base_error).clone();
                                e.note = "unable to show termination via `decreases_by` lemma"
                                    .to_string();
                                e.secondary_label(
                                    &span,
                                    "need to show decreases conditions for this body",
                                )
                            }
                        };

                        let ens_stmt = StmtX::Assert(assert_id.clone(), error, None, ens.clone());
                        stmts.push(Arc::new(ens_stmt));
                    }
                }

                stmts
            };
            if *inside_body {
                stmts.push(Arc::new(StmtX::Assume(air::ast_util::mk_false())));
            }
            stmts
        }
        StmX::AssertQuery { typ_inv_exps: _, typ_inv_vars, body, mode } => {
            if ctx.debug {
                unimplemented!("assert query is unsupported in debugger mode");
            }

            let mut local = state.local_shared.clone();
            for (x, typ) in typ_inv_vars.iter() {
                let typ_inv = typ_invariant(ctx, typ, &ident_var(&suffix_local_unique_id(x)));
                if let Some(expr) = typ_inv {
                    local.push(mk_unnamed_axiom(expr));
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
                        ctx.fun
                            .as_ref()
                            .expect("asserts are expected to be in a function")
                            .current_fun
                            .clone(),
                        stm.span.clone(),
                        "assert_nonlinear_by".to_string(),
                        match ctx.global.solver {
                            SmtSolver::Z3 => Arc::new(vec![
                                mk_option_command("smt.arith.solver", "6"),
                                Arc::new(CommandX::CheckValid(query)),
                            ]),
                            SmtSolver::Cvc5 =>
                            // TODO: What cvc5 settings would help here?
                            // TODO: Can we even adjust the settings at this point?
                            {
                                Arc::new(vec![Arc::new(CommandX::CheckValid(query))])
                            }
                        },
                        ProverChoice::Nonlinear,
                        true,
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

            let queries = bv_to_queries(ctx, requires, ensures)?;

            for (query, error_desc) in queries.into_iter() {
                let mut bv_commands = mk_bitvector_option(&ctx.global.solver);
                bv_commands.push(Arc::new(CommandX::CheckValid(query)));
                state.commands.push(CommandsWithContextX::new(
                    ctx.fun
                        .as_ref()
                        .expect("asserts are expected to be in a function")
                        .current_fun
                        .clone(),
                    stm.span.clone(),
                    error_desc,
                    Arc::new(bv_commands),
                    ProverChoice::BitVector,
                    true,
                ));
            }
            vec![]
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
        StmX::BreakOrContinue { label, is_break } => {
            let loop_info = if label.is_some() {
                state
                    .loop_infos
                    .iter()
                    .rfind(|info| info.label == *label)
                    .expect("missing loop label")
            } else {
                state.loop_infos.last().expect("inside loop")
            };
            let is_air_break = *is_break && !loop_info.loop_isolation;
            let mut stmts: Vec<Stmt> = Vec::new();
            if !ctx.checking_spec_preconditions() && !is_air_break {
                assert!(!loop_info.some_cond); // AST-to-SST conversion must eliminate the cond
                if loop_info.is_for_loop && !*is_break {
                    // At the very least, the syntax macro will need to advance the ghost iterator
                    // at each continue.
                    return Err(error(&stm.span, "for-loops do not yet support continue"));
                }
                let invs = if *is_break {
                    loop_info.invs_exit.clone()
                } else {
                    loop_info.invs_entry.clone()
                };
                let base_error = if *is_break {
                    error_with_label(&stm.span, "loop invariant not satisfied", "at this loop exit")
                } else {
                    error_with_label(&stm.span, "loop invariant not satisfied", "at this continue")
                };
                for (span, inv, msg, both) in invs.iter() {
                    let mut error = base_error.secondary_label(span, "failed this invariant");
                    if let Some(msg) = msg {
                        error = error.secondary_label(span, &**msg);
                    }
                    if *is_break && *both {
                        let msg = "(hint: if this is not supposed to be true at the break, \
                            use 'invariant_except_break' for it instead of 'invariant', \
                            and use 'ensures' for what is true at the break)";
                        error = error.secondary_label(span, msg);
                    }
                    stmts.push(Arc::new(StmtX::Assert(None, error, None, inv.clone())));
                }
                let decrease = &loop_info.decrease;
                if !is_break && decrease.len() > 0 {
                    for info in state.loop_infos.iter().rev() {
                        if info.label == *label {
                            break;
                        }
                        if info.loop_isolation {
                            let s = "decrease checking for labeled continue not supported unless \
                                loop is marked #[verifier::loop_isolation(false)]";
                            return Err(error(&stm.span, s));
                        }
                    }
                    let dec_exp = crate::recursion::check_decrease(
                        ctx,
                        &stm.span,
                        Some(loop_info.loop_id),
                        decrease,
                        decrease.len(),
                    )?;
                    let expr = exp_to_expr(ctx, &dec_exp, expr_ctxt)?;
                    let error = error(&stm.span, crate::def::DEC_FAIL_LOOP_CONTINUE);
                    let dec_stmt = StmtX::Assert(None, error, None, expr);
                    stmts.push(Arc::new(dec_stmt));
                }
            }
            if is_air_break {
                stmts.push(Arc::new(StmtX::Break(loop_info.air_break_label.clone())));
            } else {
                stmts.push(Arc::new(StmtX::Assume(air::ast_util::mk_false())));
            }
            stmts
        }
        StmX::ClosureInner { body, typ_inv_vars } => {
            let mut stmts = vec![];
            for (x, typ) in typ_inv_vars.iter() {
                let typ_inv = typ_invariant(ctx, typ, &ident_var(&suffix_local_unique_id(x)));
                if let Some(expr) = typ_inv {
                    stmts.push(Arc::new(StmtX::Assume(expr)));
                }
            }

            // Right now there is no way to specify an invariant mask on a closure function
            // All closure funcs are assumed to have mask set 'full'
            let mut mask = MaskSet::full();
            std::mem::swap(&mut state.mask, &mut mask);
            // Right now all closures are assumed to unwind
            let mut unwind = UnwindAir::MayUnwind;
            std::mem::swap(&mut state.unwind, &mut unwind);

            let mut body_stmts = stm_to_stmts(ctx, state, body)?;
            std::mem::swap(&mut state.mask, &mut mask);
            std::mem::swap(&mut state.unwind, &mut unwind);

            stmts.append(&mut body_stmts);

            vec![Arc::new(StmtX::DeadEnd(one_stmt(stmts)))]
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
        StmX::Loop {
            loop_isolation,
            is_for_loop,
            id,
            label,
            cond,
            body,
            invs,
            decrease,
            typ_inv_vars,
            modified_vars,
        } => {
            let loop_isolation = *loop_isolation;
            let (cond_stm, pos_assume, neg_assume) = if let Some((cond_stm, cond_exp)) = cond {
                let pos_cond = exp_to_expr(ctx, &cond_exp, expr_ctxt)?;
                let neg_cond = Arc::new(ExprX::Unary(air::ast::UnaryOp::Not, pos_cond.clone()));
                let pos_assume = Arc::new(StmtX::Assume(pos_cond));
                let neg_assume = Arc::new(StmtX::Assume(neg_cond));
                (Some(cond_stm), Some(pos_assume), Some(neg_assume))
            } else {
                (None, None, None)
            };
            let mut invs_entry: Vec<(Span, Expr, Option<Arc<String>>, bool)> = Vec::new();
            let mut invs_exit: Vec<(Span, Expr, Option<Arc<String>>, bool)> = Vec::new();
            let mut hint_message = None;
            for inv in invs.iter() {
                let inv_exp =
                    crate::loop_inference::finalize_inv(modified_vars, &inv.inv, &mut hint_message);
                let msg_opt = exp_get_custom_err(&inv_exp);
                let expr = exp_to_expr(ctx, &inv_exp, expr_ctxt)?;
                if cond.is_some() {
                    assert!(inv.at_entry);
                    assert!(inv.at_exit);
                }
                let both = inv.at_entry && inv.at_exit;
                if inv.at_entry {
                    invs_entry.push((inv.inv.span.clone(), expr.clone(), msg_opt.clone(), both));
                }
                if inv.at_exit {
                    invs_exit.push((inv.inv.span.clone(), expr.clone(), msg_opt.clone(), both));
                }
            }
            let invs_entry = Arc::new(invs_entry);
            let invs_exit = Arc::new(invs_exit);

            let (_, decrease_init) =
                crate::recursion::mk_decreases_at_entry(ctx, &stm.span, Some(*id), &decrease)?;

            let entry_snap_id = if ctx.debug {
                // Add a snapshot to capture the start of the while loop
                // We add the snapshot via Block to avoid copying the entire AST of the loop body
                let entry_snap = state.update_current_sid(SUFFIX_SNAP_WHILE_BEGIN);
                Some(entry_snap)
            } else {
                None
            };

            /*
            When loop_isolation = true:
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

            /*
            Suppose we have:
                loop invs { body }
            When loop_isolation = false, we generate this AIR:
                assert invs
                breakable(break_label) {
                    havoc modified_vars
                    assume typ_inv(modified_vars)
                    assume invs
                    body // "break" inside body turns into break(break_label)
                    assert invs
                    assume false
                }
                // note that we don't assume the invs after the loop,
                // because we may have come from a break statement where the invs don't hold
            When loop_isolation = true:
                We generate this AIR in the outer query:
                    assert invs
                    havoc modified_vars
                    assume typ_invs(modified_vars)
                    assume invs_exit
                We generate this AIR in the spun-off loop query:
                    axiom typ_invs(all_used_vars)
                    assume invs_entry
                    body // "break" inside body turns into assert invs_exit; assume false
                    assert invs_entry
            Suppose we have:
                while cond invs { body }
            When loop_isolation = false, this is represented as a "loop"; see the case above.
            When loop_isolation = true:
                We generate this AIR in the outer query:
                    assert invs
                    havoc modified_vars
                    assume typ_invs(modified_vars)
                    assume invs_exit
                    cond_stm
                    assume !cond_exp
                We generate this AIR in the spun-off loop query:
                    axiom typ_invs(all_used_vars)
                    assume invs_entry
                    cond_stm
                    assume cond_exp
                    body // "break" inside body turns into assert invs_exit; assume false
                    assert invs_entry
            */

            let mut air_body: Vec<Stmt> = state.static_prelude.clone();
            if !loop_isolation {
                for x in modified_vars.iter() {
                    air_body.push(Arc::new(StmtX::Havoc(suffix_local_unique_id(&x))));
                }
                for (x, typ) in typ_inv_vars.iter() {
                    if modified_vars.contains(x) {
                        let typ_inv =
                            typ_invariant(ctx, typ, &ident_var(&suffix_local_unique_id(x)));
                        if let Some(expr) = typ_inv {
                            air_body.push(Arc::new(StmtX::Assume(expr)));
                        }
                    }
                }
            }

            let mut local = state.local_shared.clone();
            if loop_isolation {
                for (x, typ) in typ_inv_vars.iter() {
                    let typ_inv = typ_invariant(ctx, typ, &ident_var(&suffix_local_unique_id(x)));
                    if let Some(expr) = typ_inv {
                        local.push(mk_unnamed_axiom(expr));
                    }
                }
            }

            // For any mutable param `x` to the function, we might refer to either
            // *x or *old(x) within the loop body or invariants.
            // Thus, we need to create a 'pre' snapshot and havoc all these variables
            // so that we can refer to either version of the variable within the body.
            if loop_isolation {
                air_body.push(Arc::new(StmtX::Snapshot(snapshot_ident(SNAPSHOT_PRE))));
            }
            for (x, typ) in typ_inv_vars.iter() {
                if state.may_be_used_in_old.contains(x) {
                    air_body.push(Arc::new(StmtX::Havoc(suffix_local_unique_id(x))));
                    let typ_inv = typ_invariant(ctx, typ, &ident_var(&suffix_local_unique_id(x)));
                    if let Some(expr) = typ_inv {
                        air_body.push(Arc::new(StmtX::Assume(expr)));
                    }
                }
            }

            // Assume invariants for the beginning of the loop body.
            // (These need to go after the above Havoc statements.)
            for (_, inv, _, _) in invs_entry.iter() {
                air_body.push(Arc::new(StmtX::Assume(inv.clone())));
            }
            for dec in decrease_init.iter() {
                air_body.append(&mut stm_to_stmts(ctx, state, dec)?);
            }

            let cond_stmts = cond_stm.map(|s| stm_to_stmts(ctx, state, s)).transpose()?;
            if let Some(cond_stmts) = &cond_stmts {
                assert!(loop_isolation);
                air_body.append(&mut cond_stmts.clone());
            }
            if let Some(pos_assume) = pos_assume {
                assert!(loop_isolation);
                air_body.push(pos_assume);
            }
            let air_break_label = crate::def::break_label(*id);
            let loop_info = LoopInfo {
                loop_isolation,
                is_for_loop: *is_for_loop,
                label: label.clone(),
                loop_id: *id,
                air_break_label: air_break_label.clone(),
                some_cond: cond.is_some(),
                invs_entry: invs_entry.clone(),
                invs_exit: invs_exit.clone(),
                decrease: decrease.clone(),
            };
            state.loop_infos.push(loop_info);
            air_body.append(&mut stm_to_stmts(ctx, state, body)?);
            state.loop_infos.pop();

            if !ctx.checking_spec_preconditions() {
                for (span, inv, msg, _) in invs_entry.iter() {
                    let mut error = error(span, crate::def::INV_FAIL_LOOP_END);
                    if let Some(msg) = msg {
                        error = error.secondary_label(span, &**msg);
                    }
                    let inv_stmt = StmtX::Assert(None, error, None, inv.clone());
                    air_body.push(Arc::new(inv_stmt));
                }
                if decrease.len() > 0 {
                    let dec_exp = crate::recursion::check_decrease(
                        ctx,
                        &stm.span,
                        Some(*id),
                        decrease,
                        decrease.len(),
                    )?;
                    let expr = exp_to_expr(ctx, &dec_exp, expr_ctxt)?;
                    let error = error(&stm.span, crate::def::DEC_FAIL_LOOP_END);
                    let dec_stmt = StmtX::Assert(None, error, None, expr);
                    air_body.push(Arc::new(dec_stmt));
                }
            }
            if !loop_isolation {
                let loop_end = StmtX::Assume(air::ast_util::mk_false());
                air_body.push(Arc::new(loop_end));
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
            if loop_isolation {
                let assertion = assertion.clone();
                let query = Arc::new(QueryX { local: Arc::new(local), assertion });
                let loop_cmd_context = CommandsWithContextX::new(
                    ctx.fun
                        .as_ref()
                        .expect("asserts are expected to be in a function")
                        .current_fun
                        .clone(),
                    stm.span.clone(),
                    "while loop".to_string(),
                    Arc::new(vec![Arc::new(CommandX::CheckValid(query))]),
                    ProverChoice::DefaultProver,
                    false,
                );
                loop_cmd_context.hint_upon_failure.replace(hint_message);
                state.commands.push(loop_cmd_context);
            }

            // At original site of while loop, assert invariant, havoc, assume invariant + neg_cond
            let mut stmts: Vec<Stmt> = Vec::new();
            if !ctx.checking_spec_preconditions() {
                for (span, inv, msg, _) in invs_entry.iter() {
                    let mut error = error(span, crate::def::INV_FAIL_LOOP_FRONT);
                    if let Some(msg) = msg {
                        error = error.secondary_label(span, &**msg);
                    }
                    let inv_stmt = StmtX::Assert(None, error, None, inv.clone());
                    stmts.push(Arc::new(inv_stmt));
                }
            }
            if !loop_isolation {
                let break_label = air_break_label.clone();
                let loop_breakable = Arc::new(StmtX::Breakable(break_label, assertion));
                stmts.push(loop_breakable);
            }
            if loop_isolation {
                for x in modified_vars.iter() {
                    stmts.push(Arc::new(StmtX::Havoc(suffix_local_unique_id(&x))));
                }
                for (x, typ) in typ_inv_vars.iter() {
                    if modified_vars.contains(x) {
                        let typ_inv =
                            typ_invariant(ctx, typ, &ident_var(&suffix_local_unique_id(x)));
                        if let Some(expr) = typ_inv {
                            stmts.push(Arc::new(StmtX::Assume(expr)));
                        }
                    }
                }
                for (_, inv, _, _) in invs_exit.iter() {
                    let inv_stmt = StmtX::Assume(inv.clone());
                    stmts.push(Arc::new(inv_stmt));
                }
            }
            if let Some(cond_stmts) = &cond_stmts {
                assert!(loop_isolation);
                stmts.append(&mut cond_stmts.clone());
            }
            if let Some(neg_assume) = neg_assume {
                assert!(loop_isolation);
                stmts.push(neg_assume);
            }
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
        StmX::OpenInvariant(namespace_exp, body_stm) => {
            let mut stmts = vec![];

            // Build the names_expr. Note: In the SST, this should have been assigned
            // to an expression whose value is constant for the entire block.
            let namespace_expr = exp_to_expr(ctx, namespace_exp, &ExprCtxt::new())?;

            // Assert that the namespace of the inv we are opening is in the mask set
            if !ctx.checking_spec_preconditions() {
                state.mask.assert_contains(&namespace_exp.span, &namespace_expr, &mut stmts, None);
            }

            // process the body
            // first remove the namespace from the mask set so that we cannot re-open
            // the same invariant inside
            let mut inner_mask =
                state.mask.remove_element(namespace_exp.span.clone(), namespace_expr);
            // Disallow unwinding inside the invariant block
            let mut inner_unwind =
                UnwindAir::NoUnwind(ReasonForNoUnwind::OpenInvariant(stm.span.clone()));
            swap(&mut state.mask, &mut inner_mask);
            swap(&mut state.unwind, &mut inner_unwind);
            stmts.append(&mut stm_to_stmts(ctx, state, body_stm)?);
            swap(&mut state.mask, &mut inner_mask);
            swap(&mut state.unwind, &mut inner_unwind);

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
        StmX::RevealString(lit) => {
            let exprs = Arc::new({
                vec![
                    string_is_ascii_to_air(ctx, lit.clone()),
                    string_len_to_air(ctx, lit.clone()),
                    string_indices_to_air(ctx, lit.clone()),
                ]
            });
            let exprx = Arc::new(ExprX::Multi(MultiOp::And, exprs));
            let stmt = Arc::new(StmtX::Assume(exprx));
            vec![stmt]
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
        StmX::Air(s) => {
            let mut parser = sise::Parser::new(s.as_bytes());
            let node = sise::read_into_tree(&mut parser).unwrap();

            let stmt = air::parser::Parser::new(Arc::new(crate::messages::VirMessageInterface {}))
                .node_to_stmt(&node);
            match stmt {
                Ok(stmt) => vec![stmt],
                Err(err) => {
                    return Err(error(&stm.span, format!("Invalid inline AIR statement: {}", err)));
                }
            }
        }
    };
    Ok(result)
}

fn string_len_to_air(ctx: &Ctx, lit: Arc<String>) -> Expr {
    let cnst = str_to_const_str(ctx, lit.clone());
    let lhs = str_apply(&str_ident(STRSLICE_LEN), &vec![cnst]);
    let len_val = Arc::new(ExprX::Const(Constant::Nat(Arc::new(lit.chars().count().to_string()))));
    Arc::new(ExprX::Binary(air::ast::BinaryOp::Eq, lhs, len_val))
}

fn string_index_to_air(cnst: &Expr, index: usize, value: char) -> Expr {
    let index_expr = Arc::new(ExprX::Const(Constant::Nat(Arc::new(index.to_string()))));
    let char_expr =
        Arc::new(ExprX::Const(Constant::Nat(Arc::new((char_to_unicode_repr(value)).to_string()))));
    let lhs = str_apply(&str_ident(STRSLICE_GET_CHAR), &vec![cnst.clone(), index_expr]);
    Arc::new(ExprX::Binary(air::ast::BinaryOp::Eq, lhs, char_expr))
}

fn string_indices_to_air(ctx: &Ctx, lit: Arc<String>) -> Expr {
    let cnst = str_to_const_str(ctx, lit.clone());
    let mut exprs = Vec::new();
    for (i, c) in lit.chars().enumerate() {
        let e = string_index_to_air(&cnst, i, c);
        exprs.push(e);
    }
    let exprs = Arc::new(exprs);
    let exprx = Arc::new(ExprX::Multi(MultiOp::And, exprs));
    exprx
}

fn string_is_ascii_to_air(ctx: &Ctx, lit: Arc<String>) -> Expr {
    let is_ascii = lit.is_ascii();
    let cnst = str_to_const_str(ctx, lit);
    let lhs = str_apply(&str_ident(STRSLICE_IS_ASCII), &vec![cnst]);
    let is_ascii = Arc::new(ExprX::Const(Constant::Bool(is_ascii)));
    Arc::new(ExprX::Binary(air::ast::BinaryOp::Eq, lhs, is_ascii))
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

        let fun_name = fun_as_friendly_rust_name(
            &ctx.fun.as_ref().expect("Missing a current function value").current_fun,
        );
        let qid = new_internal_qid(ctx, format!("{}_nondefault_fuel", fun_name));
        let bind = Arc::new(BindX::Quant(Quant::Forall, binders, triggers, qid));
        let or = Arc::new(ExprX::Multi(air::ast::MultiOp::Or, Arc::new(disjuncts)));
        mk_bind_expr(&bind, &or)
    };
    local.push(mk_unnamed_axiom(fuel_expr));
}

fn mk_static_prelude(ctx: &Ctx, statics: &Vec<Fun>) -> Vec<Stmt> {
    statics
        .iter()
        .filter(|f| ctx.funcs_with_ensure_predicate[&**f])
        .map(|f| {
            let f_ens = prefix_ensures(&fun_to_air_ident(&f));
            let f_static = string_var(&static_name(f));
            let ens_args = vec![f_static];
            let e_ens = Arc::new(ExprX::Apply(f_ens, Arc::new(ens_args)));
            Arc::new(StmtX::Assume(e_ens))
        })
        .collect()
}

pub(crate) fn body_stm_to_air(
    ctx: &Ctx,
    func_span: &Span,
    typ_params: &Idents,
    typ_bounds: &crate::ast::GenericBounds,
    params: &Pars,
    func_check_sst: &FuncCheckSst,
    hidden: &Vec<Fun>,
    is_integer_ring: bool,
    is_bit_vector_mode: bool,
    is_nonlinear: bool,
) -> Result<(Vec<CommandsWithContext>, Vec<(Span, SnapPos)>), VirErr> {
    let FuncCheckSst { reqs, post_condition, mask_set, body: stm, local_decls, statics, unwind } =
        func_check_sst;

    if is_bit_vector_mode {
        if is_integer_ring {
            panic!("Error: integer_ring and bit_vector should not be used together");
        }

        let queries = bv_to_queries(ctx, reqs, &post_condition.ens_exps)?;
        let mut commands = vec![];

        for (query, error_desc) in queries.into_iter() {
            let mut bv_commands = mk_bitvector_option(&ctx.global.solver);
            bv_commands.push(Arc::new(CommandX::CheckValid(query)));
            commands.push(CommandsWithContextX::new(
                ctx.fun.as_ref().expect("function expected here").current_fun.clone(),
                func_span.clone(),
                error_desc,
                Arc::new(bv_commands),
                ProverChoice::BitVector,
                true,
            ));
        }

        return Ok((commands, vec![]));
    }

    // Verifying a single function can generate multiple SMT queries.
    // Some declarations (local_shared) are shared among the queries.
    // Others are private to each query.
    let mut local_shared: Vec<Decl> = Vec::new();

    for x in typ_params.iter() {
        for (x, t) in crate::def::suffix_typ_param_ids_types(x) {
            local_shared.push(Arc::new(DeclX::Const(x.lower(), str_typ(t))));
        }
    }
    for decl in local_decls.iter() {
        local_shared.push(if decl.mutable {
            Arc::new(DeclX::Var(suffix_local_unique_id(&decl.ident), typ_to_air(ctx, &decl.typ)))
        } else {
            Arc::new(DeclX::Const(suffix_local_unique_id(&decl.ident), typ_to_air(ctx, &decl.typ)))
        });
    }

    set_fuel(ctx, &mut local_shared, hidden);

    use indexmap::{IndexMap, IndexSet};
    let mut declared: IndexMap<UniqueIdent, Typ> = IndexMap::new();
    let mut assigned: IndexSet<UniqueIdent> = IndexSet::new();
    let mut has_mut_params = false;
    for param in params.iter() {
        declared.insert(unique_local(&param.x.name), param.x.typ.clone());
        assigned.insert(unique_local(&param.x.name));
        if param.x.is_mut {
            has_mut_params = true;
        }
    }
    for decl in local_decls.iter() {
        declared.insert(decl.ident.clone(), decl.typ.clone());
    }

    let initial_sid = Arc::new("0_entry".to_string());

    let mut ens_exprs: Vec<(Span, Expr)> = Vec::new();
    for ens in post_condition.ens_exps.iter() {
        let expr_ctxt = &ExprCtxt::new_mode(ExprMode::Body);
        let e = exp_to_expr(ctx, &ens, expr_ctxt)?;
        ens_exprs.push((ens.span.clone(), e));
    }

    let unwind_air = match unwind {
        UnwindSst::MayUnwind => UnwindAir::MayUnwind,
        UnwindSst::NoUnwind => UnwindAir::NoUnwind(ReasonForNoUnwind::Function),
        UnwindSst::NoUnwindWhen(exp) => {
            let expr_ctxt = &ExprCtxt::new_mode(ExprMode::Body);
            let e = exp_to_expr(ctx, &exp, expr_ctxt)?;
            UnwindAir::NoUnwindWhen(e)
        }
    };

    let mut may_be_used_in_old = HashSet::<UniqueIdent>::new();
    for param in params.iter() {
        if param.x.is_mut {
            may_be_used_in_old.insert(unique_local(&param.x.name));
        }
    }

    let mut local = local_shared.clone();
    for e in crate::traits::trait_bounds_to_air(ctx, typ_bounds) {
        // The outer query already has this in reqs, but inner queries need it separately:
        local_shared.push(Arc::new(DeclX::Axiom(air::ast::Axiom { named: None, expr: e })));
    }

    let mut state = State {
        local_shared,
        may_be_used_in_old,
        commands: Vec::new(),
        snapshot_count: 0,
        sids: vec![initial_sid.clone()],
        snap_map: Vec::new(),
        assign_map: indexmap::IndexMap::new(),
        mask: (**mask_set).clone(),
        unwind: unwind_air,
        post_condition_info: PostConditionInfo {
            dest: post_condition.dest.clone(),
            ens_exprs,
            ens_spec_precondition_stms: post_condition.ens_spec_precondition_stms.clone(),
            kind: post_condition.kind,
        },
        loop_infos: Vec::new(),
        static_prelude: mk_static_prelude(ctx, statics),
    };

    let mut _modified = IndexSet::new();

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
    if state.static_prelude.len() > 0 {
        stmts.splice(0..0, state.static_prelude.clone());
    }

    if ctx.debug {
        let snapshot = Arc::new(StmtX::Snapshot(initial_sid));
        let mut new_stmts = vec![snapshot];
        new_stmts.append(&mut stmts);
        stmts = new_stmts;
    }

    let assertion = one_stmt(stmts);

    if !is_integer_ring {
        for param in params.iter() {
            let typ_inv = typ_invariant(ctx, &param.x.typ, &ident_var(&param.x.name.lower()));
            if let Some(expr) = typ_inv {
                local.push(mk_unnamed_axiom(expr));
            }
        }
    }

    for req in reqs.iter() {
        let expr_ctxt = &ExprCtxt::new_mode(ExprMode::BodyPre);
        let e = exp_to_expr(ctx, &req, expr_ctxt)?;
        local.push(mk_unnamed_axiom(e));
    }

    if is_integer_ring {
        #[cfg(feature = "singular")]
        {
            // parameters, requires, ensures to Singular Query
            // in the resulting queryX::assertion, the last stmt should be ensure expression
            let mut singular_vars: Vec<Decl> = vec![];
            for param in params.iter() {
                singular_vars.push(Arc::new(DeclX::Var(
                    param.x.name.lower(),
                    typ_to_air(ctx, &param.x.typ),
                )));
            }
            let mut singular_req_stmts: Vec<Stmt> = vec![];
            for req in reqs.iter() {
                let error = error_with_label(
                    &req.span,
                    "Unspported expression in integer_ring".to_string(),
                    "at the require clause".to_string(),
                );
                let air_expr = exp_to_expr(ctx, req, &ExprCtxt::new_mode(ExprMode::BodyPre))?;
                let assert_stm = Arc::new(StmtX::Assert(None, error, None, air_expr));
                singular_req_stmts.push(assert_stm);
            }

            let mut singular_ens_stmts: Vec<Stmt> = vec![];
            for ens in post_condition.ens_exps.iter() {
                let error = error_with_label(
                    &ens.span,
                    "Unspported expression in integer_ring".to_string(),
                    "at the ensure clause".to_string(),
                );
                let air_expr = exp_to_expr(ctx, ens, &ExprCtxt::new_mode(ExprMode::BodyPre))?;
                let assert_stm = Arc::new(StmtX::Assert(None, error, None, air_expr));
                singular_ens_stmts.push(assert_stm);
            }

            // put requires and ensures in the singular query
            let query = Arc::new(air::ast::SingularQueryX {
                local: Arc::new(singular_vars),
                requires: Arc::new(singular_req_stmts),
                ensures: Arc::new(singular_ens_stmts),
            });

            let singular_command = Arc::new(CommandX::CheckSingular(query));

            state.commands.push(CommandsWithContextX::new(
                ctx.fun
                    .as_ref()
                    .expect("asserts are expected to be in a function")
                    .current_fun
                    .clone(),
                func_span.clone(),
                "Singular check valid".to_string(),
                Arc::new(vec![singular_command]),
                ProverChoice::Singular,
                true,
            ));
        }
    } else {
        let query = Arc::new(QueryX { local: Arc::new(local), assertion });
        let commands = if is_nonlinear {
            match ctx.global.solver {
                SmtSolver::Z3 => vec![
                    mk_option_command("smt.arith.solver", "6"),
                    Arc::new(CommandX::CheckValid(query)),
                ],
                SmtSolver::Cvc5 =>
                // TODO: What cvc5 settings would help here?
                // TODO: Can we even adjust the settings at this point?
                {
                    vec![Arc::new(CommandX::CheckValid(query))]
                }
            }
        } else if is_bit_vector_mode {
            let mut bv_commands = mk_bitvector_option(&ctx.global.solver);
            bv_commands.push(Arc::new(CommandX::CheckValid(query)));
            bv_commands
        } else {
            vec![Arc::new(CommandX::CheckValid(query))]
        };
        state.commands.push(CommandsWithContextX::new(
            ctx.fun.as_ref().expect("function expected here").current_fun.clone(),
            func_span.clone(),
            "function body check".to_string(),
            Arc::new(commands),
            if is_nonlinear { ProverChoice::Nonlinear } else { ProverChoice::DefaultProver },
            is_integer_ring || is_nonlinear,
        ));
    }
    Ok((state.commands, state.snap_map))
}
