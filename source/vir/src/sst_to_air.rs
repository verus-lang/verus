use crate::ast::{
    ArithOp, ArrayKind, AssertQueryMode, BinaryOp, BitwiseOp, Dt, FieldOpr, Fun, GenericBoundX,
    Ident, Idents, InequalityOp, IntRange, IntegerTypeBitwidth, IntegerTypeBoundKind, Mode, Path,
    PathX, Primitive, SpannedTyped, Typ, TypDecoration, TypDecorationArg, TypX, Typs, UnaryOp,
    UnaryOpr, UnwindSpec, VarAt, VarIdent, VariantCheck, VirErr, Visibility,
};
use crate::ast_util::{
    LowerUniqueVar, fun_as_friendly_rust_name, get_field, get_variant, typ_args_for_datatype_typ,
    undecorate_typ,
};
use crate::bitvector_to_air::bv_to_queries;
use crate::context::Ctx;
use crate::def::{
    ARCH_SIZE, CommandsWithContext, CommandsWithContextX, FUEL_BOOL, FUEL_BOOL_DEFAULT,
    FUEL_DEFAULTS, FUEL_ID, FUEL_PARAM, FUEL_TYPE, I_HI, I_LO, POLY, ProverChoice, SNAPSHOT_CALL,
    SNAPSHOT_PRE, STRSLICE_GET_CHAR, STRSLICE_IS_ASCII, STRSLICE_LEN, STRSLICE_NEW_STRLIT, SUCC,
    SUFFIX_SNAP_JOIN, SUFFIX_SNAP_MUT, SUFFIX_SNAP_WHILE_BEGIN, SUFFIX_SNAP_WHILE_END, SnapPos,
    SpanKind, Spanned, U_HI, encode_dt_as_path, fun_to_string, is_variant_ident, new_internal_qid,
    new_user_qid_name, path_to_string, prefix_box, prefix_ensures, prefix_fuel_id,
    prefix_no_unwind_when, prefix_open_inv, prefix_pre_var, prefix_requires, prefix_spec_fn_type,
    prefix_unbox, snapshot_ident, static_name, suffix_global_id, suffix_local_unique_id,
    suffix_typ_param_ids, unique_local, variant_field_ident, variant_field_ident_internal,
    variant_ident,
};
use crate::messages::{Span, error, error_with_label};
use crate::poly::{MonoTyp, MonoTypX, MonoTyps, typ_as_mono, typ_is_poly};
use crate::sst::{
    BndInfo, BndInfoUser, BndX, CallFun, Dest, Exp, ExpX, InternalFun, Stm, StmX, UniqueIdent,
    UnwindSst,
};
use crate::sst::{FuncCheckSst, Pars, PostConditionKind, Stms};
use crate::sst_util::subst_typ_for_datatype;
use crate::sst_vars::{AssignMap, get_loc_var};
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
use std::collections::{BTreeMap, HashMap, HashSet};
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

#[inline(always)]
pub(crate) fn dt_to_air_ident(dt: &Dt) -> Ident {
    let path = match dt {
        Dt::Path(path) => path.clone(),
        Dt::Tuple(arity) => crate::def::prefix_tuple_type(*arity),
    };
    path_to_air_ident(&path)
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
        MonoTypX::Real => str_ident("real"),
        MonoTypX::Float(n) => Arc::new(format!("f{}", n)),
        MonoTypX::Datatype(dt, typs) => {
            return crate::def::monotyp_apply(
                &encode_dt_as_path(dt),
                &typs.iter().map(monotyp_to_path).collect(),
            );
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
        TypX::Bool => bool_typ(),
        TypX::Int(_) => int_typ(),
        TypX::Real => Arc::new(air::ast::TypX::Real),
        TypX::Float(_) => int_typ(),
        TypX::SpecFn(..) => Arc::new(air::ast::TypX::Fun),
        TypX::Primitive(Primitive::Array, _) => Arc::new(air::ast::TypX::Fun),
        TypX::AnonymousClosure(..) => {
            panic!("internal error: AnonymousClosure should have been removed by ast_simplify")
        }
        TypX::Datatype(dt, _, _) => {
            if ctx.datatype_is_transparent[dt] {
                ident_typ(&path_to_air_ident(&encode_dt_as_path(dt)))
            } else {
                match typ_as_mono(typ) {
                    None => {
                        // this probably means you forgot to call coerce_typ_to_poly
                        // or coerce_typ_to_native for this type during the poly pass
                        panic!("abstract datatype should be boxed {:?}", typ)
                    }
                    Some(monotyp) => ident_typ(&path_to_air_ident(&monotyp_to_path(&monotyp))),
                }
            }
        }
        TypX::Dyn(..) => str_typ(POLY),
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
        TypX::PointeeMetadata(_) => str_typ(POLY),
        TypX::TypeId => str_typ(crate::def::TYPE),
        TypX::ConstInt(_) => panic!("const integer cannot be used as an expression type"),
        TypX::ConstBool(_) => panic!("const bool cannot be used as an expression type"),
        TypX::Air(t) => t.clone(),
        TypX::MutRef(_) => str_typ(POLY),
        TypX::Opaque { .. } => str_typ(POLY),
    }
}

pub fn range_to_id(range: &IntRange) -> Expr {
    match range {
        IntRange::Int => str_var(crate::def::TYPE_ID_INT),
        IntRange::Nat => str_var(crate::def::TYPE_ID_NAT),
        IntRange::Char => str_var(crate::def::TYPE_ID_CHAR),
        IntRange::USize => str_var(crate::def::TYPE_ID_USIZE),
        IntRange::ISize => str_var(crate::def::TYPE_ID_ISIZE),
        IntRange::U(_) => apply_range_fun(crate::def::TYPE_ID_UINT, range, vec![]),
        IntRange::I(_) => apply_range_fun(crate::def::TYPE_ID_SINT, range, vec![]),
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
pub fn monotyp_to_id(ctx: &Ctx, typ: &MonoTyp) -> Vec<Expr> {
    let mk_id_sized = |t: Expr| -> Vec<Expr> {
        let ds = str_var(crate::def::DECORATE_NIL_SIZED);
        if crate::context::DECORATE { vec![ds, t] } else { vec![t] }
    };
    let mk_id = |t: Expr, base: &str| -> Vec<Expr> {
        let ds = str_var(base);
        if crate::context::DECORATE { vec![ds, t] } else { vec![t] }
    };
    match &**typ {
        MonoTypX::Bool => mk_id_sized(str_var(crate::def::TYPE_ID_BOOL)),
        MonoTypX::Int(range) => mk_id_sized(range_to_id(range)),
        MonoTypX::Real => mk_id_sized(str_var(crate::def::TYPE_ID_REAL)),
        MonoTypX::Float(n) => {
            let bits = Constant::Nat(Arc::new(n.to_string()));
            mk_id_sized(str_apply(crate::def::TYPE_ID_FLOAT, &vec![Arc::new(ExprX::Const(bits))]))
        }
        MonoTypX::Datatype(dt, typs) => {
            let f_name = crate::def::prefix_type_id(&encode_dt_as_path(dt));
            let mut args: Vec<Expr> = Vec::new();
            for t in typs.iter() {
                args.extend(monotyp_to_id(ctx, t));
            }
            let t = air::ast_util::ident_apply_or_var(&f_name, &Arc::new(args));

            if crate::context::DECORATE {
                let ds = decoration_for_datatype_mono(ctx, dt, typs);
                vec![ds, t]
            } else {
                vec![t]
            }
        }
        MonoTypX::Decorate(d, typ) if crate::context::DECORATE => {
            let ds_typ = monotyp_to_id(ctx, typ);
            assert!(ds_typ.len() == 2);
            let ds = str_apply(decoration_str(*d), &vec![ds_typ[0].clone()]);
            vec![ds, ds_typ[1].clone()]
        }
        MonoTypX::Decorate2(d, typs) if crate::context::DECORATE => {
            assert!(typs.len() == 2);
            let ds_typ1 = monotyp_to_id(ctx, &typs[0]);
            assert!(ds_typ1.len() == 2);
            let ds_typ2 = monotyp_to_id(ctx, &typs[1]);
            assert!(ds_typ2.len() == 2);
            let ds = str_apply(
                decoration_str(*d),
                &vec![ds_typ1[0].clone(), ds_typ1[1].clone(), ds_typ2[0].clone()],
            );
            vec![ds, ds_typ2[1].clone()]
        }
        MonoTypX::Decorate(_, typ) => monotyp_to_id(ctx, typ),
        MonoTypX::Decorate2(_, typs) => {
            assert!(typs.len() == 2);
            monotyp_to_id(ctx, &typs[1])
        }
        MonoTypX::Primitive(name, typs) => {
            let f_name = primitive_type_id(name);
            let mut args: Vec<Expr> = Vec::new();
            for t in typs.iter() {
                args.extend(monotyp_to_id(ctx, t));
            }
            let base = decoration_base_for_primitive(*name);
            mk_id(air::ast_util::ident_apply_or_var(&f_name, &Arc::new(args)), base)
        }
    }
}

fn big_int_to_expr(i: &BigInt) -> Expr {
    use num_traits::Zero;
    if i >= &BigInt::zero() { mk_nat(i) } else { air::ast_util::mk_neg(&mk_nat(-i)) }
}

fn decoration_base_for_primitive(name: Primitive) -> &'static str {
    match name {
        Primitive::Array | Primitive::Ptr | Primitive::Global => crate::def::DECORATE_NIL_SIZED,
        Primitive::Slice | Primitive::StrSlice => crate::def::DECORATE_NIL_SLICE,
    }
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
pub fn typ_to_ids(ctx: &Ctx, typ: &Typ) -> Vec<Expr> {
    let mk_id_sized = |t: Expr| -> Vec<Expr> {
        let ds = str_var(crate::def::DECORATE_NIL_SIZED);
        if crate::context::DECORATE { vec![ds, t] } else { vec![t] }
    };
    let mk_id = |t: Expr, base: &str| -> Vec<Expr> {
        let ds = str_var(base);
        if crate::context::DECORATE { vec![ds, t] } else { vec![t] }
    };
    match &**typ {
        TypX::Bool => mk_id_sized(str_var(crate::def::TYPE_ID_BOOL)),
        TypX::Int(range) => mk_id_sized(range_to_id(range)),
        TypX::Real => mk_id_sized(str_var(crate::def::TYPE_ID_REAL)),
        TypX::Float(n) => {
            let bits = Constant::Nat(Arc::new(n.to_string()));
            mk_id_sized(str_apply(crate::def::TYPE_ID_FLOAT, &vec![Arc::new(ExprX::Const(bits))]))
        }
        TypX::SpecFn(typs, typ) => mk_id_sized(fun_id(ctx, typs, typ)),
        TypX::AnonymousClosure(..) => {
            panic!("internal error: AnonymousClosure should have been removed by ast_simplify")
        }
        TypX::FnDef(fun, typs, _resolved_fun) => mk_id_sized(fndef_id(ctx, fun, typs)),
        TypX::Datatype(dt, typs, _) => {
            let t = datatype_id(ctx, &encode_dt_as_path(dt), typs);
            if crate::context::DECORATE {
                let ds = decoration_for_datatype(ctx, dt, typs);
                vec![ds, t]
            } else {
                vec![t]
            }
        }
        TypX::Dyn(name, typs, _) => mk_id(dyn_id(ctx, name, typs), crate::def::DECORATE_NIL_DYN),
        TypX::Primitive(name, typs) => {
            let base = decoration_base_for_primitive(*name);
            mk_id(primitive_id(ctx, &name, typs), base)
        }
        TypX::MutRef(typ) => {
            let f_name = str_ident(crate::def::TYPE_ID_MUT_REF);
            let args = typ_to_ids(ctx, typ);
            mk_id_sized(air::ast_util::ident_apply_or_var(&f_name, &Arc::new(args)))
        }
        TypX::Decorate(d, None, typ) if crate::context::DECORATE => {
            let ds_typ = typ_to_ids(ctx, typ);
            assert!(ds_typ.len() == 2);
            let ds = str_apply(decoration_str(*d), &vec![ds_typ[0].clone()]);
            vec![ds, ds_typ[1].clone()]
        }
        TypX::Decorate(d, Some(TypDecorationArg { allocator_typ }), typ)
            if crate::context::DECORATE =>
        {
            let ds_typ1 = typ_to_ids(ctx, allocator_typ);
            assert!(ds_typ1.len() == 2);
            let ds_typ2 = typ_to_ids(ctx, typ);
            assert!(ds_typ2.len() == 2);
            let ds = str_apply(
                decoration_str(*d),
                &vec![ds_typ1[0].clone(), ds_typ1[1].clone(), ds_typ2[0].clone()],
            );
            vec![ds, ds_typ2[1].clone()]
        }
        TypX::Decorate(_, _, typ) => typ_to_ids(ctx, typ),
        TypX::Boxed(typ) => typ_to_ids(ctx, typ),
        TypX::TypParam(x) => {
            suffix_typ_param_ids(x).iter().map(|x| ident_var(&x.lower())).collect()
        }
        TypX::Projection { trait_typ_args, trait_path, name } => {
            let mut args: Vec<Expr> = Vec::new();
            for t in trait_typ_args.iter() {
                args.extend(typ_to_ids(ctx, t));
            }
            let pd = ident_apply(&crate::def::projection(true, trait_path, name), &args);
            let pt = ident_apply(&crate::def::projection(false, trait_path, name), &args);
            vec![pd, pt]
        }
        TypX::PointeeMetadata(t) => {
            let ids = typ_to_ids(ctx, t);
            let id = ids[0].clone(); // Metadata is a function of just the decoration
            let args = vec![id];

            let pd = ident_apply(&crate::def::projection_pointee_metadata(true), &args);
            let pt = ident_apply(&crate::def::projection_pointee_metadata(false), &args);

            vec![pd, pt]
        }
        TypX::TypeId => panic!("internal error: typ_to_ids of TypeId"),
        TypX::ConstInt(c) => {
            mk_id_sized(str_apply(crate::def::TYPE_ID_CONST_INT, &vec![big_int_to_expr(c)]))
        }
        TypX::ConstBool(b) => mk_id_sized(str_apply(
            crate::def::TYPE_ID_CONST_BOOL,
            &vec![Arc::new(ExprX::Const(Constant::Bool(*b)))],
        )),
        TypX::Air(_) => panic!("internal error: typ_to_ids of Air"),
        TypX::Opaque { def_path, args } => {
            if args.len() != 0 {
                let mut e_args = Vec::new();
                for arg in args.iter() {
                    e_args.extend(typ_to_ids(ctx, arg));
                }
                let self_dcr = ident_apply(&crate::def::prefix_dcr_id(def_path), &e_args);
                let self_type = ident_apply(&crate::def::prefix_type_id(def_path), &e_args);
                vec![self_dcr, self_type]
            } else {
                let self_dcr = str_var(&crate::def::prefix_dcr_id(def_path));
                let self_type = str_var(&crate::def::prefix_type_id(def_path));
                vec![self_dcr, self_type]
            }
        }
    }
}

pub(crate) fn typ_to_id(ctx: &Ctx, typ: &Typ) -> Expr {
    typ_to_ids(ctx, typ).last().unwrap().clone()
}

pub(crate) fn fun_id(ctx: &Ctx, typs: &Typs, typ: &Typ) -> Expr {
    let f_name = crate::def::prefix_type_id_fun(typs.len());
    let mut args: Vec<Expr> = Vec::new();
    for t in typs.iter() {
        args.extend(typ_to_ids(ctx, t));
    }
    args.extend(typ_to_ids(ctx, typ));
    air::ast_util::ident_apply_or_var(&f_name, &Arc::new(args))
}

pub(crate) fn datatype_id(ctx: &Ctx, path: &Path, typs: &Typs) -> Expr {
    let f_name = crate::def::prefix_type_id(path);
    let mut args: Vec<Expr> = Vec::new();
    for t in typs.iter() {
        args.extend(typ_to_ids(ctx, t));
    }
    air::ast_util::ident_apply_or_var(&f_name, &Arc::new(args))
}

fn dyn_id(ctx: &Ctx, tr: &Path, typs: &Typs) -> Expr {
    let f_name = crate::def::prefix_dyn_id(tr);
    let mut args: Vec<Expr> = Vec::new();
    for t in typs.iter() {
        args.extend(typ_to_ids(ctx, t));
    }
    air::ast_util::ident_apply_or_var(&f_name, &Arc::new(args))
}

pub(crate) fn primitive_id(ctx: &Ctx, name: &Primitive, typs: &Typs) -> Expr {
    let f_name = primitive_type_id(name);
    let mut args: Vec<Expr> = Vec::new();
    for t in typs.iter() {
        args.extend(typ_to_ids(ctx, t));
    }
    air::ast_util::ident_apply_or_var(&f_name, &Arc::new(args))
}

pub(crate) fn fndef_id(ctx: &Ctx, fun: &Fun, typs: &Typs) -> Expr {
    let f_name = crate::def::prefix_fndef_type_id(fun);
    let mut args: Vec<Expr> = Vec::new();
    for t in typs.iter() {
        args.extend(typ_to_ids(ctx, t));
    }
    air::ast_util::ident_apply_or_var(&f_name, &Arc::new(args))
}

pub(crate) fn expr_has_type(expr: &Expr, typ: &Expr) -> Expr {
    str_apply(crate::def::HAS_TYPE, &vec![expr.clone(), typ.clone()])
}

pub(crate) fn expr_has_typ(ctx: &Ctx, expr: &Expr, typ: &Typ) -> Expr {
    expr_has_type(expr, &typ_to_id(ctx, typ))
}

pub(crate) fn decoration_for_datatype_mono(ctx: &Ctx, dt: &Dt, monotyps: &MonoTyps) -> Expr {
    let datatype = ctx.datatype_map.get(dt).unwrap();
    match &datatype.x.sized_constraint {
        None => str_var(crate::def::DECORATE_NIL_SIZED),
        Some(constraint) => {
            let typs = Arc::new(vec_map(&**monotyps, crate::poly::monotyp_to_typ));
            let c = subst_typ_for_datatype(&datatype.x.typ_params, &typs, constraint);
            let dec = typ_to_ids(ctx, &c)[0].clone();
            str_apply(crate::def::DECORATE_DST_INHERIT, &vec![dec])
        }
    }
}

pub(crate) fn decoration_for_datatype(ctx: &Ctx, dt: &Dt, typs: &Typs) -> Expr {
    let datatype = ctx.datatype_map.get(dt).unwrap();
    match &datatype.x.sized_constraint {
        None => str_var(crate::def::DECORATE_NIL_SIZED),
        Some(constraint) => {
            let c = subst_typ_for_datatype(&datatype.x.typ_params, typs, constraint);
            let dec = typ_to_ids(ctx, &c)[0].clone();
            str_apply(crate::def::DECORATE_DST_INHERIT, &vec![dec])
        }
    }
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
        TypX::Float(range) => {
            Some(apply_range_fun(&crate::def::U_INV, &IntRange::U(*range), vec![expr.clone()]))
        }
        TypX::SpecFn(..) => {
            Some(expr_has_typ(ctx, &try_box(ctx, expr.clone(), typ).expect("try_box lambda"), typ))
        }
        TypX::Dyn(..) => Some(expr_has_typ(ctx, expr, typ)),
        TypX::Primitive(Primitive::Array, _) => {
            Some(expr_has_typ(ctx, &try_box(ctx, expr.clone(), typ).expect("try_box array"), typ))
        }
        TypX::Datatype(dt, _, _) => {
            if ctx.datatype_is_transparent[dt] {
                if ctx.datatypes_with_invariant.contains(dt) {
                    let box_expr =
                        ident_apply(&prefix_box(&encode_dt_as_path(dt)), &vec![expr.clone()]);
                    Some(expr_has_typ(ctx, &box_expr, typ))
                } else {
                    None
                }
            } else {
                if typ_as_mono(typ).is_none() {
                    // this probably means you forgot to call coerce_typ_to_poly
                    // or coerce_typ_to_native for this type during the poly pass
                    panic!("abstract datatype should be boxed")
                } else {
                    None
                }
            }
        }
        TypX::Decorate(..) => unreachable!(),
        TypX::Boxed(_) => Some(expr_has_typ(ctx, expr, typ)),
        TypX::TypParam(_) => Some(expr_has_typ(ctx, expr, typ)),
        TypX::Projection { .. } => Some(expr_has_typ(ctx, expr, typ)),
        TypX::PointeeMetadata(_) => Some(expr_has_typ(ctx, expr, typ)),
        TypX::Bool | TypX::Real | TypX::AnonymousClosure(..) | TypX::TypeId => None,
        TypX::Air(_) => panic!("typ_invariant"),
        // REVIEW: we could also try to add an IntRange type invariant for TypX::ConstInt
        // (see also context.rs datatypes_invs)
        TypX::ConstInt(_) => None,
        TypX::ConstBool(_) => None,
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
        TypX::Opaque { .. } => Some(expr_has_typ(ctx, expr, typ)),
        TypX::MutRef(_) => Some(expr_has_typ(ctx, expr, typ)),
    }
}

pub(crate) fn datatype_box_prefix(ctx: &Ctx, typ: &Typ) -> Option<Path> {
    match &**typ {
        TypX::Datatype(dt, _, _) => {
            if ctx.datatype_is_transparent[dt] {
                Some(encode_dt_as_path(dt))
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
        TypX::Real => Some(str_ident(crate::def::BOX_REAL)),
        TypX::Float(_) => Some(str_ident(crate::def::BOX_INT)),
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
        TypX::Dyn(..) => None,
        TypX::Primitive(_, _) => prefix_typ_as_mono(prefix_box, typ, "primitive type"),
        TypX::FnDef(..) => Some(str_ident(crate::def::BOX_FNDEF)),
        TypX::Decorate(_, _, t) => return try_box(ctx, expr, t),
        TypX::Boxed(_) => None,
        TypX::TypParam(_) => None,
        TypX::Projection { .. } => None,
        TypX::PointeeMetadata(_) => None,
        TypX::TypeId => None,
        TypX::ConstInt(_) => None,
        TypX::ConstBool(_) => None,
        TypX::Air(_) => None,
        TypX::Opaque { .. } => None,
        TypX::MutRef(_) => None,
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
        TypX::Real => Some(str_ident(crate::def::UNBOX_REAL)),
        TypX::Float(_) => Some(str_ident(crate::def::UNBOX_INT)),
        TypX::Datatype(dt, _, _) => {
            if ctx.datatype_is_transparent[dt] {
                Some(prefix_unbox(&encode_dt_as_path(dt)))
            } else {
                prefix_typ_as_mono(prefix_unbox, typ, "abstract datatype")
            }
        }
        TypX::Dyn(..) => None,
        TypX::Primitive(Primitive::Array, _) => Some(prefix_unbox(&crate::def::array_type())),
        TypX::Primitive(_, _) => prefix_typ_as_mono(prefix_unbox, typ, "primitive type"),
        TypX::FnDef(..) => Some(str_ident(crate::def::UNBOX_FNDEF)),
        TypX::SpecFn(typs, _) => Some(prefix_unbox(&prefix_spec_fn_type(typs.len()))),
        TypX::AnonymousClosure(..) => unimplemented!(),
        TypX::Decorate(_, _, t) => return try_unbox(ctx, expr, t),
        TypX::Boxed(_) => None,
        TypX::TypParam(_) => None,
        TypX::Projection { .. } => None,
        TypX::PointeeMetadata(_) => None,
        TypX::TypeId => None,
        TypX::ConstInt(_) => None,
        TypX::ConstBool(_) => None,
        TypX::Air(_) => None,
        TypX::Opaque { .. } => None,
        TypX::MutRef(_) => None,
    };
    f_name.map(|f_name| ident_apply(&f_name, &vec![expr]))
}

pub(crate) fn ctor_to_apply<'a>(
    ctx: &'a Ctx,
    dt: &Dt,
    variant: &Ident,
    binders: &'a Binders<Exp>,
) -> (Ident, impl Iterator<Item = &'a Arc<BinderX<Exp>>>) {
    let fields = &get_variant(&ctx.datatype_map[dt].x.variants, variant).fields;
    let variant = variant_ident(dt, &variant);
    let field_exps = fields.iter().map(move |f| get_field(binders, &f.name));
    (variant, field_exps)
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
        crate::ast::Constant::Real(r) => air::ast_util::mk_real(r),
        crate::ast::Constant::StrSlice(s) => str_to_const_str(ctx, s.clone()),
        crate::ast::Constant::Char(c) => {
            Arc::new(ExprX::Const(Constant::Nat(Arc::new(char_to_unicode_repr(*c).to_string()))))
        }
        crate::ast::Constant::Float32(c) => mk_nat(c),
        crate::ast::Constant::Float64(c) => mk_nat(c),
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
    let fun_name = match &ctx.fun {
        Some(f) => fun_as_friendly_rust_name(&f.current_fun),
        None => "no_function".to_string(),
    };
    let qcount = ctx.quantifier_count.get();
    let qid = new_user_qid_name(&fun_name, qcount);
    ctx.quantifier_count.set(qcount + 1);
    let trigs = match &exp.x {
        ExpX::Bind(bnd, _) => match &bnd.x {
            BndX::Quant(_, _, trigs, _) => trigs,
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
    match &ctx.fun {
        Some(f) => {
            let bnd_info = BndInfo {
                fun: f.current_fun.clone(),
                user: Some(BndInfoUser { span: exp.span.clone(), trigs: trigs.clone() }),
            };
            ctx.global.qid_map.borrow_mut().insert(qid.clone(), bnd_info);
        }
        None => {}
    }
    Some(Arc::new(qid))
}

pub(crate) fn exp_to_expr(ctx: &Ctx, exp: &Exp, expr_ctxt: &ExprCtxt) -> Result<Expr, VirErr> {
    let typ_to_ids = |typ| typ_to_ids(ctx, typ);

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
        ExpX::Call(CallFun::InternalFun(InternalFun::OpenInvariantMask(f, i)), typs, args) => {
            let mut exprs: Vec<Expr> = typs.iter().map(typ_to_ids).flatten().collect();
            for arg in args.iter() {
                exprs.push(exp_to_expr(ctx, arg, expr_ctxt)?);
            }
            ident_apply(&prefix_open_inv(&fun_to_air_ident(f), *i), &exprs)
        }
        ExpX::Call(CallFun::InternalFun(func), typs, args) => {
            // These functions are special-cased to not take a decoration argument for
            // the first type parameter.
            let skip_first_decoration = match func {
                InternalFun::ClosureReq | InternalFun::ClosureEns | InternalFun::DefaultEns => true,
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
                    InternalFun::DefaultEns => str_ident(crate::def::DEFAULT_ENS),
                    InternalFun::CheckDecreaseInt => str_ident(crate::def::CHECK_DECREASE_INT),
                    InternalFun::CheckDecreaseHeight => {
                        str_ident(crate::def::CHECK_DECREASE_HEIGHT)
                    }
                    InternalFun::OpenInvariantMask(..) => panic!(),
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
                TypX::Primitive(Primitive::Array, typs) => typs[0].clone(),
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
            let f = crate::ast_util::const_generic_to_primitive(&exp.typ);
            str_apply(f, &vec![typ_to_id(ctx, c)])
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
        ExpX::Unary(op, e) => match op {
            UnaryOp::StrLen => Arc::new(ExprX::Apply(
                str_ident(STRSLICE_LEN),
                Arc::new(vec![exp_to_expr(ctx, e, expr_ctxt)?]),
            )),
            UnaryOp::StrIsAscii => Arc::new(ExprX::Apply(
                str_ident(STRSLICE_IS_ASCII),
                Arc::new(vec![exp_to_expr(ctx, e, expr_ctxt)?]),
            )),
            UnaryOp::Not => mk_not(&exp_to_expr(ctx, e, expr_ctxt)?),
            UnaryOp::BitNot(width_opt) => {
                let expr = exp_to_expr(ctx, e, expr_ctxt)?;
                let expr = try_box(ctx, expr, &e.typ).expect("Box");
                let bit_expr =
                    ExprX::Apply(Arc::new(crate::def::BIT_NOT.to_string()), Arc::new(vec![expr]));
                if let Some(width) = width_opt {
                    if !check_bitwidth_typ_matches(&e.typ, *width, false) {
                        return Err(error(
                            &e.span,
                            format!("Verus Internal Error: BitNot: type doesn't match"),
                        ));
                    }
                    return clip_bitwise_result(bit_expr, e);
                } else {
                    return Ok(Arc::new(bit_expr));
                }
            }
            UnaryOp::HeightTrigger => {
                str_apply(crate::def::HEIGHT, &vec![exp_to_expr(ctx, e, expr_ctxt)?])
            }
            UnaryOp::Trigger(_) => exp_to_expr(ctx, e, expr_ctxt)?,
            UnaryOp::Clip { range: IntRange::Int, .. } => exp_to_expr(ctx, e, expr_ctxt)?,
            UnaryOp::Clip { range, .. } => {
                let expr = exp_to_expr(ctx, e, expr_ctxt)?;
                let f_name = match range {
                    IntRange::Int => panic!("internal error: Int"),
                    IntRange::Nat => crate::def::NAT_CLIP,
                    IntRange::Char => crate::def::CHAR_CLIP,
                    IntRange::U(_) | IntRange::USize => crate::def::U_CLIP,
                    IntRange::I(_) | IntRange::ISize => crate::def::I_CLIP,
                };
                apply_range_fun(&f_name, &range, vec![expr])
            }
            UnaryOp::FloatToBits => exp_to_expr(ctx, e, expr_ctxt)?,
            UnaryOp::IntToReal => {
                let expr = exp_to_expr(ctx, e, expr_ctxt)?;
                Arc::new(ExprX::Unary(air::ast::UnaryOp::ToReal, expr))
            }
            UnaryOp::CoerceMode { .. } => {
                panic!("internal error: CoerceMode should have been removed before here")
            }
            UnaryOp::ToDyn => {
                let TypX::Dyn(trait_path, typ_args, _) = &*undecorate_typ(&exp.typ) else {
                    panic!("ToDyn should have type TypX::Dyn: {:?}", exp.typ)
                };
                let inner_self_typ = undecorate_typ(&e.typ); // strip off any Box, etc.
                let mut args: Vec<Expr> = typ_to_ids(&inner_self_typ);
                for t in typ_args.iter() {
                    args.extend(typ_to_ids(t));
                }
                args.push(exp_to_expr(ctx, e, expr_ctxt)?);
                ident_apply(&crate::def::to_dyn(trait_path), &args)
            }
            UnaryOp::MustBeFinalized | UnaryOp::MustBeElaborated => {
                panic!("internal error: Exp not finalized: {:?}", e)
            }
            UnaryOp::InferSpecForLoopIter { .. } => {
                // loop_inference failed to promote to Some, so demote to None
                let e = crate::loop_inference::make_option_exp(None, &e.span, &e.typ);
                exp_to_expr(ctx, &e, expr_ctxt)?
            }
            UnaryOp::CastToInteger => {
                panic!("internal error: CastToInteger should have been removed before here")
            }
            UnaryOp::MutRefCurrent | UnaryOp::MutRefFuture(_) => {
                let expr = exp_to_expr(ctx, e, expr_ctxt)?;
                let exprs = vec![expr];
                let ident = match op {
                    UnaryOp::MutRefCurrent => crate::def::MUT_REF_CURRENT,
                    UnaryOp::MutRefFuture(_) => crate::def::MUT_REF_FUTURE,
                    _ => unreachable!(),
                };
                let ident = Arc::new(ident.to_string());
                Arc::new(ExprX::Apply(ident, Arc::new(exprs)))
            }
            UnaryOp::MutRefFinal => {
                panic!("internal error: MutRefFinal should have been removed before here")
            }
            UnaryOp::Length(kind) => {
                let typ = undecorate_typ(&e.typ);
                let typ = match &*typ {
                    TypX::Boxed(x) => x,
                    _ => &e.typ,
                };
                match &*undecorate_typ(&typ) {
                    TypX::Primitive(Primitive::Array, typ_args) => {
                        // to get the length of an array, we don't actually need to
                        // evaluate the argument, just use the N from the type
                        assert!(*kind == ArrayKind::Array);
                        assert!(typ_args.len() == 2);
                        let n = &typ_args[1];
                        let f = crate::ast_util::const_generic_to_primitive(&exp.typ);
                        str_apply(f, &vec![typ_to_id(ctx, n)])
                    }
                    TypX::Primitive(Primitive::Slice, typ_args) => {
                        assert!(*kind == ArrayKind::Slice);
                        assert!(typ_args.len() == 1);
                        let t = &typ_args[0];
                        let name = crate::def::fn_slice_len(&ctx.global.vstd_crate_name);
                        let name = suffix_global_id(&fun_to_air_ident(&name));
                        let mut exprs = typ_to_ids(t);
                        exprs.push(exp_to_expr(ctx, e, expr_ctxt)?);
                        ident_apply(&name, &exprs)
                    }
                    _ => {
                        return Err(error(
                            &exp.span,
                            format!("Verus Internal Error: ArrayLength expected Array or Slice"),
                        ));
                    }
                }
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
                let (ts, num_variants) = match &*undecorate_typ(&exp.typ) {
                    TypX::Datatype(Dt::Path(p), ts, _) => {
                        let (_, variants) = &ctx.global.datatypes[p];
                        (ts.clone(), variants.len())
                    }
                    TypX::Datatype(Dt::Tuple(_), ts, _) => (ts.clone(), 1),
                    _ => panic!("internal error: expected datatype in field op"),
                };
                let mut exprs: Vec<Expr> =
                    crate::datatype_to_air::field_typ_args(num_variants, || {
                        ts.iter().map(typ_to_ids).flatten().collect()
                    });
                exprs.push(expr);
                Arc::new(ExprX::Apply(
                    variant_field_ident(&encode_dt_as_path(datatype), variant, field),
                    Arc::new(exprs),
                ))
            }
            UnaryOpr::CustomErr(_) => {
                // CustomErr is handled by split_expression. Maybe it could
                // be useful in the 'normal' case too, but right now, we just
                // ignore it here.
                return exp_to_expr(ctx, exp, expr_ctxt);
            }
            UnaryOpr::HasResolved(t) => {
                let mut exprs: Vec<Expr> = typ_to_ids(t);
                exprs.push(exp_to_expr(ctx, exp, expr_ctxt)?);
                Arc::new(ExprX::Apply(str_ident(crate::def::HAS_RESOLVED), Arc::new(exprs)))
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
                BinaryOp::Arith(ArithOp::Add(_)) if wrap_arith => {
                    return Ok(str_apply(crate::def::ADD, &vec![lh, rh]));
                }
                BinaryOp::Arith(ArithOp::Sub(_)) if wrap_arith => {
                    return Ok(str_apply(crate::def::SUB, &vec![lh, rh]));
                }
                BinaryOp::Arith(ArithOp::Add(_)) => {
                    ExprX::Multi(MultiOp::Add, Arc::new(vec![lh, rh]))
                }
                BinaryOp::Arith(ArithOp::Sub(_)) => {
                    ExprX::Multi(MultiOp::Sub, Arc::new(vec![lh, rh]))
                }
                BinaryOp::Arith(ArithOp::Mul(_)) if wrap_arith || !has_const => {
                    return Ok(str_apply(crate::def::MUL, &vec![lh, rh]));
                }
                BinaryOp::Arith(ArithOp::EuclideanDiv(_)) if wrap_arith || !has_const => {
                    return Ok(str_apply(crate::def::EUC_DIV, &vec![lh, rh]));
                }
                // REVIEW: consider introducing singular_mod more earlier pipeline (e.g. from syntax macro?)
                BinaryOp::Arith(ArithOp::EuclideanMod(_)) if expr_ctxt.is_singular => {
                    return Ok(str_apply(crate::def::SINGULAR_MOD, &vec![lh, rh]));
                }
                BinaryOp::Arith(ArithOp::EuclideanMod(_)) if wrap_arith || !has_const => {
                    return Ok(str_apply(crate::def::EUC_MOD, &vec![lh, rh]));
                }
                BinaryOp::Arith(ArithOp::Mul(_)) => {
                    ExprX::Multi(MultiOp::Mul, Arc::new(vec![lh, rh]))
                }
                BinaryOp::RealArith(crate::ast::RealArithOp::Add) => {
                    return Ok(str_apply(crate::def::RADD, &vec![lh, rh]));
                }
                BinaryOp::RealArith(crate::ast::RealArithOp::Sub) => {
                    return Ok(str_apply(crate::def::RSUB, &vec![lh, rh]));
                }
                BinaryOp::RealArith(crate::ast::RealArithOp::Mul) => {
                    return Ok(str_apply(crate::def::RMUL, &vec![lh, rh]));
                }
                BinaryOp::RealArith(crate::ast::RealArithOp::Div) => {
                    return Ok(str_apply(crate::def::RDIV, &vec![lh, rh]));
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
                BinaryOp::Index(kind, _) => {
                    let container_typ = undecorate_typ(&lhs.typ);
                    let container_typ = match &*container_typ {
                        TypX::Boxed(x) => x,
                        _ => &container_typ,
                    };
                    match &*undecorate_typ(container_typ) {
                        TypX::Primitive(Primitive::Array, ts) if ts.len() == 2 => {
                            assert!(*kind == ArrayKind::Array);
                            let mut args: Vec<Expr> = ts.iter().map(typ_to_ids).flatten().collect();
                            args.push(exp_to_expr(ctx, lhs, expr_ctxt)?);
                            args.push(exp_to_expr(ctx, rhs, expr_ctxt)?);
                            ExprX::Apply(str_ident(crate::def::ARRAY_INDEX), Arc::new(args))
                        }
                        TypX::Primitive(Primitive::Slice, ts) if ts.len() == 1 => {
                            assert!(*kind == ArrayKind::Slice);
                            let mut args: Vec<Expr> = ts.iter().map(typ_to_ids).flatten().collect();
                            let lhs_expr = exp_to_expr(ctx, lhs, expr_ctxt)?;
                            let lhs_expr = as_box(ctx, lhs_expr, &lhs.typ);
                            let rhs_expr = exp_to_expr(ctx, rhs, expr_ctxt)?;
                            args.push(lhs_expr);
                            args.push(rhs_expr);
                            let name = crate::def::fn_slice_index(&ctx.global.vstd_crate_name);
                            let name = suffix_global_id(&fun_to_air_ident(&name));
                            ExprX::Apply(name, Arc::new(args))
                        }
                        _ => panic!("internal error: unexpected BinaryOp::Index type"),
                    }
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
                        BinaryOp::Arith(ArithOp::Add(_)) => unreachable!(),
                        BinaryOp::Arith(ArithOp::Sub(_)) => unreachable!(),
                        BinaryOp::Arith(ArithOp::Mul(_)) => unreachable!(),
                        BinaryOp::Arith(ArithOp::EuclideanDiv(_)) => {
                            air::ast::BinaryOp::EuclideanDiv
                        }
                        BinaryOp::Arith(ArithOp::EuclideanMod(_)) => {
                            air::ast::BinaryOp::EuclideanMod
                        }
                        BinaryOp::RealArith(..) => unreachable!(),
                        BinaryOp::Bitwise(..) => unreachable!(),
                        BinaryOp::StrGetChar => unreachable!(),
                        BinaryOp::Index(..) => unreachable!(),
                    };
                    ExprX::Binary(aop, lh, rh)
                }
            };
            Arc::new(expx)
        }
        ExpX::BinaryOpr(crate::ast::BinaryOpr::ExtEq(deep, t), lhs, rhs) => {
            let mut args = vec![Arc::new(ExprX::Const(Constant::Bool(*deep))), typ_to_id(ctx, t)];
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
            BndX::Quant(quant, binders, trigs, _) => {
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
                        let args = vec![choose_expr, typ_to_id(ctx, typ)];
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
    local_decls_decreases_init: Stms,
    may_be_used_in_old: HashSet<UniqueIdent>, // vars that might have a 'PRE' snapshot, needed for while loop generation
    commands: Vec<CommandsWithContext>,
    snapshot_count: u32, // Used to ensure unique Idents for each snapshot
    sids: Vec<Ident>, // a stack of snapshot ids, the top one should dominate the current position in the AST
    snap_map: Vec<(Span, SnapPos)>, // Maps each statement's span to the closest dominating snapshot's ID
    assign_map: AssignMap, // Maps Maps each statement's span to the assigned variables (that can potentially be queried)
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

fn var_locs_to_bare_vars(arg: &Exp) -> Exp {
    crate::sst_visitor::map_exp_visitor(arg, &mut |e| match &e.x {
        ExpX::VarLoc(x) => SpannedTyped::new(&e.span, &e.typ, ExpX::Var(x.clone())),
        _ => e.clone(),
    })
}

enum FieldUpdateDatumOpr {
    Field(FieldOpr),
    MutRefCurrent,
    Index(Exp, Typ, ArrayKind),
}

impl FieldUpdateDatumOpr {
    // Useful for old-mut-ref code that doesn't use the MutRefCurrent projection
    fn expect_field(&self) -> &FieldOpr {
        match self {
            FieldUpdateDatumOpr::Field(opr) => opr,
            _ => panic!("FieldUpdateDatumOpr::expect_field failed"),
        }
    }
}

struct FieldUpdateDatum {
    opr: FieldUpdateDatumOpr,
    field_typ: Typ,
    base_exp: Exp,
}

fn loc_to_field_update_data(loc: &Exp) -> (UniqueIdent, LocFieldInfo<Vec<FieldUpdateDatum>>) {
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
            ExpX::UnaryOpr(UnaryOpr::Field(opr), ee) => {
                fields.push(FieldUpdateDatum {
                    opr: FieldUpdateDatumOpr::Field(opr.clone()),
                    field_typ: e.typ.clone(),
                    base_exp: var_locs_to_bare_vars(ee),
                });
                e = ee;
            }
            ExpX::Unary(UnaryOp::MutRefCurrent, ee) => {
                fields.push(FieldUpdateDatum {
                    opr: FieldUpdateDatumOpr::MutRefCurrent,
                    field_typ: e.typ.clone(),
                    base_exp: var_locs_to_bare_vars(ee),
                });
                e = ee;
            }
            ExpX::Binary(BinaryOp::Index(kind, _), ee, idx) => {
                let container_typ = undecorate_typ(&ee.typ);
                let container_typ = match &*container_typ {
                    TypX::Boxed(x) => x,
                    _ => &container_typ,
                };
                let container_typ = undecorate_typ(&container_typ);
                fields.push(FieldUpdateDatum {
                    opr: FieldUpdateDatumOpr::Index(idx.clone(), container_typ, *kind),
                    field_typ: e.typ.clone(),
                    base_exp: var_locs_to_bare_vars(ee),
                });
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

// REVIEW this function will likely no longer be necessary once we handle mutable references
// using prophecy variables (it is currently used on function call when one of the arguments
// is a mutable reference to a path)
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
    let typ_to_ids = |typ| typ_to_ids(ctx, typ);
    let expr_ctxt = &ExprCtxt::new();
    let result = match &stm.x {
        StmX::Call {
            fun,
            resolved_method,
            is_trait_default,
            mode,
            typ_args: typs,
            args,
            split,
            dest,
            assert_id,
        } => {
            // When we emit the VCs for a call to `f`, we might also want these to include
            // the generic conditions
            // `call_requires(f, (args...))` and `call_ensures(f, (args...), ret)`
            // We don't want to do this all the time though --- only when the generic
            // FnDef types exist post-pruning.
            let emit_generic_conditions = ctx.fndef_types.contains(fun);
            let resolved_fun = resolved_method.clone().map(|r| r.0);

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
                && (!ctx.checking_spec_decreases() || *mode != Mode::Spec)
            {
                let f_req = prefix_requires(&fun_to_air_ident(&func.x.name));

                let mut e_req = Arc::new(ExprX::Apply(f_req, req_args.clone()));

                if emit_generic_conditions {
                    let generic_req_exp = crate::sst_util::sst_call_requires(
                        ctx,
                        &stm.span,
                        fun,
                        typs,
                        func,
                        &resolved_fun,
                        args,
                    );
                    let generic_req_expr = exp_to_expr(ctx, &generic_req_exp, expr_ctxt)?;
                    e_req = mk_implies(&mk_not(&generic_req_expr), &e_req);
                }

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
                        format!("call to {:} might unwind", fun_as_friendly_rust_name(fun)),
                    ),
                    UnwindAir::NoUnwind(ReasonForNoUnwind::OpenInvariant(span)) => {
                        error_with_label(
                            &stm.span,
                            "cannot show this call will not unwind",
                            format!("call to {:} might unwind", fun_as_friendly_rust_name(fun)),
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
                        loc_to_field_update_data(arg);
                    mutated_fields
                        .entry(base_var)
                        .or_insert(LocFieldInfo { base_typ, base_span, a: Vec::new() })
                        .a
                        .push(fields.iter().map(|o| o.opr.expect_field().clone()).collect());
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

            let (has_ens, resolved_ens, ens_fun, ens_typ_args) = match resolved_method {
                Some((res_fun, res_typs)) if ctx.funcs_with_ensure_predicate[res_fun] => {
                    // Use ens predicate for the statically-resolved function
                    let res_typ_args = res_typs.iter().map(typ_to_ids).flatten().collect();
                    (true, true, res_fun, res_typ_args)
                }
                _ if ctx.funcs_with_ensure_predicate[&func.x.name] => {
                    // Use ens predicate for the generic function
                    (true, false, &func.x.name, typ_args)
                }
                _ => {
                    // No ens predicate
                    (false, false, &func.x.name, typ_args)
                }
            };

            let mut ens_args: Vec<_> =
                ens_typ_args.into_iter().chain(ens_args_wo_typ.into_iter()).collect();
            if func.x.ens_has_return {
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
                } else {
                    crate::messages::internal_error(&stm.span, "ens_has_return but no Dest");
                }
            }
            if let Some(is_trait_default) = is_trait_default {
                if !resolved_ens {
                    ens_args.insert(0, air::ast_util::mk_const_bool(*is_trait_default));
                }
            }
            if has_ens {
                let f_ens = prefix_ensures(&fun_to_air_ident(&ens_fun));
                let e_ens = Arc::new(ExprX::Apply(f_ens, Arc::new(ens_args)));
                stmts.push(Arc::new(StmtX::Assume(e_ens)));
            }
            if emit_generic_conditions {
                let dest_exp =
                    if func.x.ens_has_return { Some(dest.clone().unwrap().dest) } else { None };
                let generic_ens_exp = crate::sst_util::sst_call_ensures(
                    ctx,
                    &stm.span,
                    fun,
                    typs,
                    func,
                    &resolved_fun,
                    args,
                    dest_exp,
                );
                let generic_ens_expr = exp_to_expr(ctx, &generic_ens_exp, expr_ctxt)?;
                stmts.push(Arc::new(StmtX::Assume(generic_ens_expr)));
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
                    let ret_exp: &Arc<SpannedTyped<ExpX>> =
                        ret_exp.as_ref().expect("if dest is provided, expr must be provided");

                    let mut stmts =
                        stm_to_stmts(ctx, state, &assume_var(&stm.span, &dest_id, ret_exp))?;

                    // if return value exists, check if we need to emit additional assumes for nested opaque types
                    let ret_op = ctx
                        .fun
                        .as_ref()
                        .and_then(|f| ctx.func_sst_map.get(&f.current_fun))
                        .map_or(None, |fun| Some(fun.x.ret.x.typ.clone()));
                    if ret_op.is_some() {
                        stmts.extend(opaque_ty_additional_stmts(
                            ctx,
                            state,
                            &ret_exp.span,
                            &ret_exp.typ,
                            &ret_op.unwrap(),
                        )?);
                    }

                    stmts
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
                                .primary_label(&span, crate::def::THIS_POST_FAILED.to_string()),
                            PostConditionKind::DecreasesImplicitLemma => {
                                base_error.ensure_primary_label()
                            }
                            PostConditionKind::DecreasesBy => {
                                let mut e = (**base_error).ensure_primary_label();
                                {
                                    let e = Arc::make_mut(&mut e);
                                    e.note = "unable to show termination via `decreases_by` lemma"
                                        .to_string();
                                    e.secondary_label(
                                        &span,
                                        "need to show decreases conditions for this body",
                                    )
                                }
                            }
                            PostConditionKind::EnsuresSafeApiCheck => {
                                crate::safe_api::err_for_trait_ensures(
                                    span,
                                    &ctx.fun.as_ref().unwrap().current_fun,
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
            if ctx.debug {
                unimplemented!("assignments are unsupported in debugger mode");
            }

            let dest = dest;
            let mut value = exp_to_expr(ctx, &rhs, expr_ctxt)?;
            let mut value_typ = rhs.typ.clone();

            let (base_var, LocFieldInfo { base_typ, base_span: _, a: fields }) =
                loc_to_field_update_data(&dest);

            for FieldUpdateDatum { opr, field_typ, base_exp } in fields.iter().rev() {
                // TODO(andrea) move this to poly.rs once we have general support for mutable references
                if typ_is_poly(ctx, field_typ) && !typ_is_poly(ctx, &value_typ) {
                    value = try_box(ctx, value, &value_typ).expect("box field update");
                }
                let base_expr = exp_to_expr(ctx, &base_exp, expr_ctxt)?;
                match opr {
                    FieldUpdateDatumOpr::Field(opr) => {
                        let acc = variant_field_ident_internal(
                            &encode_dt_as_path(&opr.datatype),
                            &opr.variant,
                            &opr.field,
                            true,
                        );
                        let bop = air::ast::BinaryOp::FieldUpdate(acc);
                        value = Arc::new(ExprX::Binary(bop, base_expr, value));
                    }
                    FieldUpdateDatumOpr::MutRefCurrent => {
                        let ident = Arc::new(crate::def::MUT_REF_UPDATE_CURRENT.to_string());
                        let exprs = vec![base_expr, value];
                        value = Arc::new(ExprX::Apply(ident, Arc::new(exprs)));
                    }
                    FieldUpdateDatumOpr::Index(idx, container_typ, kind) => {
                        let idx = exp_to_expr(ctx, idx, expr_ctxt)?;
                        let (fun, typ_args) = match &**container_typ {
                            TypX::Primitive(Primitive::Slice, typ_args) => {
                                assert!(*kind == ArrayKind::Slice);
                                (crate::def::fn_slice_update(&ctx.global.vstd_crate_name), typ_args)
                            }
                            TypX::Primitive(Primitive::Array, typ_args) => {
                                assert!(*kind == ArrayKind::Array);
                                (crate::def::fn_array_update(&ctx.global.vstd_crate_name), typ_args)
                            }
                            _ => {
                                return Err(error(
                                    &stm.span,
                                    format!("Verus Internal Error: Assign expected Array or Slice"),
                                ));
                            }
                        };
                        let name = suffix_global_id(&fun_to_air_ident(&fun));
                        let mut exprs: Vec<Expr> =
                            typ_args.iter().map(typ_to_ids).flatten().collect();
                        // REVIEW: cleaner boxing and unboxing strategy here?
                        // spec_slice_update : Poly -> Poly
                        // spec_array_update : Poly -> native
                        exprs.push(as_box(ctx, base_expr, &base_exp.typ));
                        exprs.push(idx);
                        exprs.push(value);
                        value = Arc::new(ExprX::Apply(name, Arc::new(exprs)));
                        if *kind == ArrayKind::Slice {
                            value = try_unbox(ctx, value.clone(), &base_exp.typ).unwrap_or(value);
                        }
                    }
                }
                value_typ = base_exp.typ.clone();
            }

            // TODO(andrea) move this to poly.rs once we have general support for mutable references
            let boxed = if typ_is_poly(ctx, &base_typ) && !typ_is_poly(ctx, &value_typ) {
                value = try_box(ctx, value, &value_typ).expect("box field update");
                true
            } else {
                false
            };

            let a = Arc::new(StmtX::Assign(suffix_local_unique_id(&base_var), value));
            stmts.push(a);
            if fields.len() > 0 {
                let mut var_exp = ident_var(&suffix_local_unique_id(&base_var));
                if boxed {
                    var_exp = try_unbox(ctx, var_exp, &value_typ).expect("assign try_unbox");
                }
                let typ_inv = typ_invariant(ctx, &value_typ, &var_exp);
                if let Some(expr) = typ_inv {
                    stmts.push(Arc::new(StmtX::Assume(expr)));
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
                assert!(!is_break || !loop_info.some_cond); // AST-to-SST conversion must eliminate the cond
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

            // Right now all closures are assumed to unwind
            let mut unwind = UnwindAir::MayUnwind;
            std::mem::swap(&mut state.unwind, &mut unwind);

            let mut body_stmts = stm_to_stmts(ctx, state, body)?;
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

                // For any mutable param `x` to the function, we might refer to either
                // *x or *old(x) within the loop body or invariants.
                // Thus, we need to create a 'pre' snapshot and havoc all these variables
                // so that we can refer to either version of the variable within the body.
                air_body.push(Arc::new(StmtX::Snapshot(snapshot_ident(SNAPSHOT_PRE))));
                for exp in state.local_decls_decreases_init.clone().iter() {
                    air_body.append(&mut stm_to_stmts(ctx, state, exp)?);
                }
                for (x, typ) in typ_inv_vars.iter() {
                    if state.may_be_used_in_old.contains(x) {
                        air_body.push(Arc::new(StmtX::Havoc(suffix_local_unique_id(x))));
                        let typ_inv =
                            typ_invariant(ctx, typ, &ident_var(&suffix_local_unique_id(x)));
                        if let Some(expr) = typ_inv {
                            air_body.push(Arc::new(StmtX::Assume(expr)));
                        }
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
        StmX::OpenInvariant(body_stm) => {
            let mut stmts = vec![];

            // Build the names_expr. Note: In the SST, this should have been assigned
            // to an expression whose value is constant for the entire block.

            // process the body
            // Disallow unwinding inside the invariant block
            let mut inner_unwind =
                UnwindAir::NoUnwind(ReasonForNoUnwind::OpenInvariant(stm.span.clone()));
            swap(&mut state.unwind, &mut inner_unwind);
            stmts.append(&mut stm_to_stmts(ctx, state, body_stm)?);
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
            let mut stmts: Vec<Stmt> = Vec::new();
            for s in stms.iter() {
                stmts.extend(stm_to_stmts(ctx, state, s)?);
            }
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
    if lit.len() == 0 {
        return Arc::new(ExprX::Const(Constant::Bool(true)));
    }
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
    let FuncCheckSst {
        reqs,
        post_condition,
        body: stm,
        local_decls,
        local_decls_decreases_init,
        statics,
        unwind,
    } = func_check_sst;

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
        local_shared.push(if decl.kind.is_mutable() {
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

    for e in crate::traits::trait_bounds_to_air(ctx, typ_bounds) {
        // The outer query already has this in reqs, but inner queries need it separately:
        local_shared.push(Arc::new(DeclX::Axiom(air::ast::Axiom { named: None, expr: e })));
    }

    let mut local = local_shared.clone();

    let mut state = State {
        local_shared,
        local_decls_decreases_init: local_decls_decreases_init.clone(),
        may_be_used_in_old,
        commands: Vec::new(),
        snapshot_count: 0,
        sids: vec![initial_sid.clone()],
        snap_map: Vec::new(),
        assign_map: indexmap::IndexMap::new(),
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

/// At function returns, we need to tell the SMT solver that the newly created opaque type is indeed the same type
/// as the returned expression.
fn opaque_ty_additional_stmts(
    ctx: &Ctx,
    state: &mut State,
    span: &Span,
    ret_exp_typ: &Typ,
    ret_typ: &Typ,
) -> Result<Vec<Stmt>, VirErr> {
    let mut stmts = vec![];
    let mut emit_eq_stmts = || {
        let ret_expr_typs = typ_to_ids(ctx, &ret_exp_typ);
        let ret_value_typs = typ_to_ids(ctx, &ret_typ);
        let decr = ExprX::Binary(
            air::ast::BinaryOp::Eq,
            ret_expr_typs[0].clone(),
            ret_value_typs[0].clone(),
        );
        let assume_decr = Arc::new(StmtX::Assume(Arc::new(decr)));
        let typ = ExprX::Binary(
            air::ast::BinaryOp::Eq,
            ret_expr_typs[1].clone(),
            ret_value_typs[1].clone(),
        );
        let assume_typ = Arc::new(StmtX::Assume(Arc::new(typ)));
        stmts.push(assume_decr);
        stmts.push(assume_typ);
    };
    match (&**ret_typ, &**ret_exp_typ) {
        (
            TypX::Datatype(dt_ret_typ, items_ret_typ, _impl_paths_ret_typ),
            TypX::Datatype(dt_ret_exp_typ, items_ret_exp_typ, _impl_paths_ret_exp_typ),
        ) => {
            if items_ret_typ.len() != items_ret_exp_typ.len() {
                crate::messages::internal_error(
                    span,
                    "return exp and return value types has different length",
                );
            }
            if dt_ret_exp_typ != dt_ret_typ {
                crate::messages::internal_error(
                    span,
                    "return exp and return value types has different types",
                );
            }
            for (ret_exp_typ, ret_typ) in items_ret_exp_typ.iter().zip(items_ret_typ.iter()) {
                stmts.extend(opaque_ty_additional_stmts(ctx, state, span, ret_exp_typ, ret_typ)?);
            }
        }
        (
            TypX::Opaque { def_path: ret_exp_def_path, args: _ret_exp_args },
            TypX::Opaque { def_path: ret_typ_def_path, args: _ret_typ_args },
        ) => {
            emit_eq_stmts();
            let ret_exp_opaque_typ = &ctx.opaque_type_map[ret_exp_def_path];
            let ret_typ_opaque_typ = &ctx.opaque_type_map[ret_typ_def_path];

            let mut ret_exp_projection_map = HashMap::new();
            let mut ret_typ_projection_map = HashMap::new();

            for (ret_exp_bound, ret_typ_bound) in
                ret_exp_opaque_typ.x.typ_bounds.iter().zip(ret_typ_opaque_typ.x.typ_bounds.iter())
            {
                if let GenericBoundX::TypEquality(trait_path, _, id, proj_typ) = &**ret_exp_bound {
                    ret_exp_projection_map.insert((trait_path.clone(), id.clone()), proj_typ);
                }
                if let GenericBoundX::TypEquality(trait_path, _, id, proj_typ) = &**ret_typ_bound {
                    ret_typ_projection_map.insert((trait_path.clone(), id.clone()), proj_typ);
                }
            }
            for trait_path_id in ret_exp_projection_map.keys() {
                if ret_typ_projection_map.contains_key(trait_path_id) {
                    stmts.extend(opaque_ty_additional_stmts(
                        ctx,
                        state,
                        span,
                        ret_exp_projection_map[trait_path_id],
                        ret_typ_projection_map[trait_path_id],
                    )?);
                }
            }
        }
        (TypX::Opaque { .. }, _) => {
            emit_eq_stmts();
        }
        _ => {}
    }
    Ok(stmts)
}
