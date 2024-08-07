//! Insert Poly types and Box/Unbox expressions to represent polymorphism (generics).

/*
The SMT solver does not support polymorphic types directly,
so polymorphism must be encoded by coercing expressions to and from a universal
Poly type via Box and Unbox coercions.
The predicate has_type describes which underlying type a Box value holds.

In this encoding, we have to decide which expressions have native monomorphic
types (e.g. int, bool) and which expressions have Poly type.
This decision is motivated by three goals:

1) For efficiency, use native types where possible, avoiding unnecessary coercions.
   (For example, to represent 1 + 2 + 3, we wouldn't want to coerce between int and Poly
   around every + operation.)
2) For efficiency, since we've already type-checked the expressions,
   avoid reasoning about has_type unless necessary.
3) For completeness, avoid adding coercions to variables inside quantifier triggers,
   because this can cause expressions to fail to match triggers in some cases.
   For example, if f(g(a)) is encoded without coercions in one place,
   but there's a quantifier that encodes f(x) as f(Box(x)), using a trigger f(Box(x)),
   then f(g(a)) will fail to match the f(Box(x)) trigger for any x,
   whereas without the Box, f(g(a)) matches f(x) via x = g(a).

These goals are in conflict, unfortunately, so we have to compromise.
We prioritize (3) to avoid inexplicable triggering failures, and we
do as best we can with (1) and (2) on a case-by-case basis.

For (2), we introduce sorts to represent monomorphic instantiations of abstract datatypes.
For example, if Set<A> is an abstract datatype, Set<u64> and Set<bool> would each get their own sort.
On the other hand, we represent abstract datatypes applied to type variables as Poly.

REVIEW: We could also introduce sorts to represent integer range types like u64,
but this would lead to extra complexity, so we use int and Poly instead.

Suppose Map<A, B> is an abstract datatype and Pair<A, B> is a transparent datatype.
The following table summarizes what sorts are used for which Rust types in which situations,
where A is a type parameter:

                               bool    int     u64     A       Map<u64, u8>   Map<u64, A>  Pair<u64, u8>  Pair<u64, A>

quantifier variable            Poly    Poly    Poly    Poly    Poly           Poly         Poly           Poly
spec function parameter        Poly    Poly    Poly    Poly    Poly           Poly         Poly           Poly
trait method parameter         Poly    Poly    Poly    Poly    Poly           Poly         Poly           Poly
trait method return type       Poly    Poly    Poly    Poly    Poly           Poly         Poly           Poly

exec/proof function parameter  bool    int     int*    Poly    map_u64_u8     Poly         pair*          pair*
datatype field                 bool    int     int*    Poly    map_u64_u8     Poly         pair*          pair*
return type                    bool    int     int*    Poly    map_u64_u8     Poly         pair*          pair*
local variable / let binding   bool    int     int*    Poly    map_u64_u8     Poly         pair*          pair*

(The "int*" and "pair*" indicate that the values of the types need additional invariants,
such as a u64 being in the range 0..2^64.  In addition, all Poly values need a has_type invariant.)

Because of (3), we represent all quantified variables as Poly types rather than native types.
Thus, a VIR quantifier like:

  forall x: int. f(x, 1)

becomes an AIR quantifier like one of the following, depending on how we translate f:

  forall x: Poly. has_type(x, t) ==> f(x, Box(1))
  forall x: Poly. has_type(x, t) ==> f(Unbox(x), Unbox(Box(1)))

The first version assumes that f's parameters are Poly (as is the case for spec functions),
while the latter assumes that f's parameters are int (as is the case for datatype constructors).
Note that the latter two cases lead to triggers involving "Unbox(x)", not just x.
This can lead to the completeness problems of (3).
Therefore, the expression Unbox(Box(1)) explicitly introduces a superfluous Unbox to handle (3).

Note: in some cases, we can also support int quantifier variables x,
for the purpose of triggering on arithmetic expressions,
as long as *all* the expressions in all the triggers use x for arithmetic.
For example, #[trigger] g(f(x), x + 1) would not be allowed,
because x is used both for f and for +.
*/

use crate::ast::{
    AssocTypeImpl, BinaryOp, CallTarget, Datatype, DatatypeX, Expr, ExprX, Exprs, FieldOpr,
    Function, FunctionKind, FunctionX, IntRange, Krate, KrateX, MaskSpec, Mode, MultiOp, Param,
    ParamX, Path, PatternX, Primitive, SpannedTyped, Stmt, StmtX, Typ, TypDecorationArg, TypX,
    Typs, UnaryOp, UnaryOpr, UnwindSpec, VarBinder, VarIdent, Variant,
};
use crate::context::Ctx;
use crate::def::Spanned;
use crate::util::vec_map;
use air::ast::Binder;
use air::scope_map::ScopeMap;
use std::collections::HashMap;
use std::sync::Arc;

pub type MonoTyp = Arc<MonoTypX>;
pub type MonoTyps = Arc<Vec<MonoTyp>>;
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum MonoTypX {
    Bool,
    Int(IntRange),
    Datatype(Path, MonoTyps),
    Decorate(crate::ast::TypDecoration, MonoTyp),
    Decorate2(crate::ast::TypDecoration, MonoTyps),
    Primitive(Primitive, MonoTyps),
}

struct State {
    types: ScopeMap<VarIdent, Typ>,
    is_trait: bool,
    in_exec_closure: bool,
}

fn monotyps_as_mono(typs: &Typs) -> Option<Vec<MonoTyp>> {
    let mut monotyps: Vec<MonoTyp> = Vec::new();
    for typ in typs.iter() {
        if let Some(monotyp) = typ_as_mono(typ) {
            monotyps.push(monotyp);
        } else {
            return None;
        }
    }
    Some(monotyps)
}

pub(crate) fn typ_as_mono(typ: &Typ) -> Option<MonoTyp> {
    match &**typ {
        TypX::Bool => Some(Arc::new(MonoTypX::Bool)),
        TypX::Int(range) => Some(Arc::new(MonoTypX::Int(*range))),
        TypX::Datatype(path, typs, _impl_paths) => {
            let monotyps = monotyps_as_mono(typs)?;
            Some(Arc::new(MonoTypX::Datatype(path.clone(), Arc::new(monotyps))))
        }
        TypX::Decorate(d, None, t) => typ_as_mono(t).map(|m| Arc::new(MonoTypX::Decorate(*d, m))),
        TypX::Decorate(d, Some(TypDecorationArg { allocator_typ }), t) => {
            let m1 = typ_as_mono(allocator_typ)?;
            let m2 = typ_as_mono(t)?;
            Some(Arc::new(MonoTypX::Decorate2(*d, Arc::new(vec![m1, m2]))))
        }
        TypX::Primitive(Primitive::Array, _) => None,
        TypX::Primitive(name, typs) => {
            let monotyps = monotyps_as_mono(typs)?;
            Some(Arc::new(MonoTypX::Primitive(*name, Arc::new(monotyps))))
        }
        TypX::AnonymousClosure(..) => {
            panic!("internal error: AnonymousClosure should be removed by ast_simplify")
        }
        TypX::Tuple(_) => panic!("internal error: Tuple should be removed by ast_simplify"),
        TypX::TypeId => panic!("internal error: TypeId created too soon"),
        TypX::Air(_) => panic!("internal error: Air type created too soon"),
        TypX::Boxed(..) | TypX::TypParam(..) | TypX::SpecFn(..) | TypX::FnDef(..) => None,
        TypX::ConstInt(_) => None,
        TypX::Projection { .. } => None,
    }
}

pub(crate) fn monotyp_to_typ(monotyp: &MonoTyp) -> Typ {
    match &**monotyp {
        MonoTypX::Bool => Arc::new(TypX::Bool),
        MonoTypX::Int(range) => Arc::new(TypX::Int(*range)),
        MonoTypX::Datatype(path, typs) => {
            let typs = vec_map(&**typs, monotyp_to_typ);
            Arc::new(TypX::Datatype(path.clone(), Arc::new(typs), Arc::new(vec![])))
        }
        MonoTypX::Primitive(name, typs) => {
            let typs = vec_map(&**typs, monotyp_to_typ);
            Arc::new(TypX::Primitive(*name, Arc::new(typs)))
        }
        MonoTypX::Decorate(d, typ) => Arc::new(TypX::Decorate(*d, None, monotyp_to_typ(typ))),
        MonoTypX::Decorate2(d, typs) => {
            assert!(typs.len() == 2);
            let allocator_typ = monotyp_to_typ(&typs[0]);
            let typ = monotyp_to_typ(&typs[1]);
            Arc::new(TypX::Decorate(*d, Some(TypDecorationArg { allocator_typ }), typ))
        }
    }
}

pub(crate) fn typ_is_poly(ctx: &Ctx, typ: &Typ) -> bool {
    match &**typ {
        TypX::Bool | TypX::Int(_) | TypX::SpecFn(..) | TypX::FnDef(..) => false,
        TypX::Primitive(Primitive::Array, _) => false,
        TypX::AnonymousClosure(..) => {
            panic!("internal error: AnonymousClosure should be removed by ast_simplify")
        }
        TypX::Tuple(_) => panic!("internal error: Tuple should be removed by ast_simplify"),
        TypX::Datatype(path, _, _) => {
            if ctx.datatype_is_transparent[path] {
                false
            } else {
                typ_as_mono(typ).is_none()
            }
        }
        TypX::Decorate(_, _, t) => typ_is_poly(ctx, t),
        // Note: we rely on rust_to_vir_base normalizing TypX::Projection { .. }.
        // If it normalized to a projection, it is poly; otherwise it is handled by
        // one of the other TypX::* cases.
        TypX::Boxed(_) | TypX::TypParam(_) | TypX::Projection { .. } => true,
        TypX::Primitive(_, _) => typ_as_mono(typ).is_none(),
        TypX::TypeId => panic!("internal error: TypeId created too soon"),
        TypX::ConstInt(_) => panic!("internal error: expression should not have ConstInt type"),
        TypX::Air(_) => panic!("internal error: Air type created too soon"),
    }
}

pub(crate) fn coerce_typ_to_native(ctx: &Ctx, typ: &Typ) -> Typ {
    match &**typ {
        TypX::Bool | TypX::Int(_) | TypX::SpecFn(..) | TypX::FnDef(..) => typ.clone(),
        TypX::Primitive(Primitive::Array, _) => typ.clone(),
        TypX::AnonymousClosure(..) => {
            panic!("internal error: AnonymousClosure should be removed by ast_simplify")
        }
        TypX::Tuple(_) => panic!("internal error: Tuple should be removed by ast_simplify"),
        TypX::Datatype(path, _, _) => {
            if ctx.datatype_is_transparent[path] {
                typ.clone()
            } else {
                if typ_as_mono(typ).is_none() {
                    Arc::new(TypX::Boxed(typ.clone()))
                } else {
                    typ.clone()
                }
            }
        }
        TypX::Decorate(d, targ, t) => {
            Arc::new(TypX::Decorate(*d, targ.clone(), coerce_typ_to_native(ctx, t)))
        }
        TypX::Boxed(_) | TypX::TypParam(_) | TypX::Projection { .. } => typ.clone(),
        TypX::Primitive(_, _) => {
            if typ_as_mono(typ).is_none() {
                Arc::new(TypX::Boxed(typ.clone()))
            } else {
                typ.clone()
            }
        }
        TypX::TypeId => panic!("internal error: TypeId created too soon"),
        TypX::ConstInt(_) => panic!("internal error: expression should not have ConstInt type"),
        TypX::Air(_) => panic!("internal error: Air type created too soon"),
    }
}

pub(crate) fn coerce_typ_to_poly(_ctx: &Ctx, typ: &Typ) -> Typ {
    match &**typ {
        TypX::Bool | TypX::Int(_) | TypX::SpecFn(..) | TypX::FnDef(..) => {
            Arc::new(TypX::Boxed(typ.clone()))
        }
        TypX::AnonymousClosure(..) => {
            panic!("internal error: AnonymousClosure should be removed by ast_simplify")
        }
        TypX::Tuple(_) => panic!("internal error: Tuple should be removed by ast_simplify"),
        TypX::Datatype(..) | TypX::Primitive(_, _) => Arc::new(TypX::Boxed(typ.clone())),
        TypX::Decorate(d, targ, t) => {
            Arc::new(TypX::Decorate(*d, targ.clone(), coerce_typ_to_poly(_ctx, t)))
        }
        TypX::Boxed(_) | TypX::TypParam(_) | TypX::Projection { .. } => typ.clone(),
        TypX::TypeId => panic!("internal error: TypeId created too soon"),
        TypX::ConstInt(_) => typ.clone(),
        TypX::Air(_) => panic!("internal error: Air type created too soon"),
    }
}

pub(crate) fn coerce_expr_to_native(ctx: &Ctx, expr: &Expr) -> Expr {
    match &*crate::ast_util::undecorate_typ(&expr.typ) {
        TypX::Bool
        | TypX::Int(_)
        | TypX::SpecFn(..)
        | TypX::Datatype(..)
        | TypX::Primitive(_, _)
        | TypX::FnDef(..) => expr.clone(),
        TypX::AnonymousClosure(..) => {
            panic!("internal error: AnonymousClosure should be removed by ast_simplify")
        }
        TypX::Tuple(_) => panic!("internal error: Tuple should be removed by ast_simplify"),
        TypX::Decorate(..) => {
            panic!("internal error: Decorate should be removed by undecorate_typ")
        }
        TypX::Boxed(typ) => {
            if typ_is_poly(ctx, typ) {
                expr.clone()
            } else {
                let op = UnaryOpr::Unbox(typ.clone());
                let exprx = ExprX::UnaryOpr(op, expr.clone());
                SpannedTyped::new(&expr.span, typ, exprx)
            }
        }
        TypX::TypParam(_) | TypX::Projection { .. } => expr.clone(),
        TypX::TypeId => panic!("internal error: TypeId created too soon"),
        TypX::ConstInt(_) => panic!("internal error: expression should not have ConstInt type"),
        TypX::Air(_) => panic!("internal error: Air type created too soon"),
    }
}

pub(crate) fn coerce_exp_to_native(ctx: &Ctx, exp: &crate::sst::Exp) -> crate::sst::Exp {
    match &*crate::ast_util::undecorate_typ(&exp.typ) {
        TypX::Bool
        | TypX::Int(_)
        | TypX::SpecFn(..)
        | TypX::Datatype(..)
        | TypX::Primitive(_, _)
        | TypX::FnDef(..) => exp.clone(),
        TypX::AnonymousClosure(..) => {
            panic!("internal error: AnonymousClosure should be removed by ast_simplify")
        }
        TypX::Tuple(_) => panic!("internal error: Tuple should be removed by ast_simplify"),
        TypX::Decorate(..) => {
            panic!("internal error: Decorate should be removed by undecorate_typ")
        }
        TypX::Boxed(typ) => {
            if typ_is_poly(ctx, typ) {
                exp.clone()
            } else {
                let op = UnaryOpr::Unbox(typ.clone());
                let expx = crate::sst::ExpX::UnaryOpr(op, exp.clone());
                SpannedTyped::new(&exp.span, typ, expx)
            }
        }
        TypX::TypParam(_) | TypX::Projection { .. } => exp.clone(),
        TypX::TypeId => panic!("internal error: TypeId created too soon"),
        TypX::ConstInt(_) => panic!("internal error: expression should not have ConstInt type"),
        TypX::Air(_) => panic!("internal error: Air type created too soon"),
    }
}

pub fn coerce_expr_to_poly(ctx: &Ctx, expr: &Expr) -> Expr {
    if typ_is_poly(ctx, &expr.typ) {
        expr.clone()
    } else {
        let op = UnaryOpr::Box(expr.typ.clone());
        let exprx = ExprX::UnaryOpr(op, expr.clone());
        let typ = Arc::new(TypX::Boxed(expr.typ.clone()));
        SpannedTyped::new(&expr.span, &typ, exprx)
    }
}

pub(crate) fn coerce_exp_to_poly(ctx: &Ctx, exp: &crate::sst::Exp) -> crate::sst::Exp {
    if typ_is_poly(ctx, &exp.typ) {
        exp.clone()
    } else {
        let op = UnaryOpr::Box(exp.typ.clone());
        let expx = crate::sst::ExpX::UnaryOpr(op, exp.clone());
        let typ = Arc::new(TypX::Boxed(exp.typ.clone()));
        SpannedTyped::new(&exp.span, &typ, expx)
    }
}

fn coerce_exprs_to_agree(ctx: &Ctx, expr1: &Expr, expr2: &Expr) -> (Expr, Expr) {
    if typ_is_poly(ctx, &expr1.typ) && typ_is_poly(ctx, &expr2.typ) {
        (expr1.clone(), expr2.clone())
    } else {
        (coerce_expr_to_native(ctx, expr1), coerce_expr_to_native(ctx, expr2))
    }
}

// Recursively coerce subexpressions to native or to Boxed, as needed
fn poly_expr(ctx: &Ctx, state: &mut State, expr: &Expr) -> Expr {
    let mk_expr = |e: ExprX| SpannedTyped::new(&expr.span, &expr.typ, e);
    let mk_expr_typ = |t: &Typ, e: ExprX| SpannedTyped::new(&expr.span, t, e);
    match &expr.x {
        ExprX::Const(_) => expr.clone(),
        ExprX::Var(x) => SpannedTyped::new(&expr.span, &state.types[x], ExprX::Var(x.clone())),
        ExprX::VarLoc(x) => {
            SpannedTyped::new(&expr.span, &state.types[x], ExprX::VarLoc(x.clone()))
        }
        ExprX::VarAt(x, at) => {
            SpannedTyped::new(&expr.span, &state.types[x], ExprX::VarAt(x.clone(), *at))
        }
        ExprX::ConstVar(..) => panic!("ConstVar should already be removed"),
        ExprX::StaticVar(_) => expr.clone(),
        ExprX::Call(target, exprs) => match target {
            CallTarget::Fun(_, name, _, _, _) => {
                let function = &ctx.func_map[name].x;
                let is_spec = function.mode == Mode::Spec;
                let is_trait = !matches!(function.kind, FunctionKind::Static);
                assert!(exprs.len() == function.params.len());
                let mut args: Vec<Expr> = Vec::new();
                for (param, arg) in function.params.iter().zip(exprs.iter()) {
                    let arg = poly_expr(ctx, state, arg);
                    let arg = if is_spec || is_trait || typ_is_poly(ctx, &param.x.typ) {
                        coerce_expr_to_poly(ctx, &arg)
                    } else {
                        coerce_expr_to_native(ctx, &arg)
                    };
                    args.push(arg);
                }
                let typ = if (is_trait || typ_is_poly(ctx, &function.ret.x.typ))
                    && function.has_return()
                {
                    coerce_typ_to_poly(ctx, &expr.typ)
                } else {
                    coerce_typ_to_native(ctx, &expr.typ)
                };
                mk_expr_typ(&typ, ExprX::Call(target.clone(), Arc::new(args)))
            }
            CallTarget::BuiltinSpecFun(..) => {
                let mut args: Vec<Expr> = Vec::new();
                for arg in exprs.iter() {
                    let arg = poly_expr(ctx, state, arg);
                    let arg = coerce_expr_to_poly(ctx, &arg);
                    args.push(arg);
                }
                mk_expr_typ(&expr.typ, ExprX::Call(target.clone(), Arc::new(args)))
            }
            CallTarget::FnSpec(e) => {
                let callee = coerce_expr_to_native(ctx, &poly_expr(ctx, state, e));
                let target = CallTarget::FnSpec(callee);
                let exprs = exprs
                    .iter()
                    .map(|e| coerce_expr_to_poly(ctx, &poly_expr(ctx, state, e)))
                    .collect();
                let typ = coerce_typ_to_poly(ctx, &expr.typ);
                mk_expr_typ(&typ, ExprX::Call(target, Arc::new(exprs)))
            }
        },
        ExprX::Tuple(_) => panic!("internal error: ast_simplify should remove Tuple"),
        ExprX::ArrayLiteral(es) => {
            let mut es1 = vec![];
            for e in es.iter() {
                let e1 = poly_expr(ctx, state, e);
                let e1 = coerce_expr_to_poly(ctx, &e1);
                es1.push(e1);
            }
            let typ = coerce_typ_to_poly(ctx, &expr.typ);
            mk_expr_typ(&typ, ExprX::ArrayLiteral(Arc::new(es1)))
        }
        ExprX::Ctor(path, variant, binders, update) => {
            assert!(update.is_none()); // removed by ast_simplify
            let fields = &ctx.datatype_map[path].x.get_variant(variant).fields;
            let mut bs: Vec<Binder<Expr>> = Vec::new();
            for binder in binders.iter() {
                let field = crate::ast_util::get_field(fields, &binder.name);
                let e = poly_expr(ctx, state, &binder.a);
                let e = if typ_is_poly(ctx, &field.a.0) {
                    coerce_expr_to_poly(ctx, &e)
                } else {
                    // Force an expression of the form unbox(...) to match triggers with unbox:
                    let e = coerce_expr_to_poly(ctx, &e);
                    coerce_expr_to_native(ctx, &e)
                };
                bs.push(binder.new_a(e));
            }
            mk_expr(ExprX::Ctor(path.clone(), variant.clone(), Arc::new(bs), None))
        }
        ExprX::NullaryOpr(crate::ast::NullaryOpr::ConstGeneric(_)) => expr.clone(),
        ExprX::NullaryOpr(crate::ast::NullaryOpr::TraitBound(..)) => expr.clone(),
        ExprX::NullaryOpr(crate::ast::NullaryOpr::TypEqualityBound(..)) => expr.clone(),
        ExprX::NullaryOpr(crate::ast::NullaryOpr::ConstTypBound(..)) => expr.clone(),
        ExprX::NullaryOpr(crate::ast::NullaryOpr::NoInferSpecForLoopIter) => expr.clone(),
        ExprX::Unary(op, e1) => {
            let e1 = poly_expr(ctx, state, e1);
            match op {
                UnaryOp::Not
                | UnaryOp::Clip { .. }
                | UnaryOp::BitNot(_)
                | UnaryOp::StrLen
                | UnaryOp::StrIsAscii => {
                    let e1 = coerce_expr_to_native(ctx, &e1);
                    mk_expr(ExprX::Unary(*op, e1))
                }
                UnaryOp::InferSpecForLoopIter { .. } => {
                    // e1 will be the argument to spec Option::Some(...)
                    let e1 = coerce_expr_to_poly(ctx, &e1);
                    mk_expr(ExprX::Unary(*op, e1))
                }
                UnaryOp::HeightTrigger => panic!("direct access to 'height' is not allowed"),
                UnaryOp::Trigger(_) | UnaryOp::CoerceMode { .. } => {
                    mk_expr_typ(&e1.typ, ExprX::Unary(*op, e1.clone()))
                }
                UnaryOp::MustBeFinalized | UnaryOp::MustBeElaborated => {
                    panic!("internal error: MustBeFinalized in AST")
                }
                UnaryOp::CastToInteger => {
                    let unbox = UnaryOpr::Unbox(Arc::new(TypX::Int(IntRange::Int)));
                    mk_expr(ExprX::UnaryOpr(unbox, e1.clone()))
                }
            }
        }
        ExprX::UnaryOpr(op, e1) => {
            let e1 = poly_expr(ctx, state, e1);
            match op {
                UnaryOpr::Box(_) | UnaryOpr::HasType(_) | UnaryOpr::Unbox(_) => {
                    panic!("internal error: already has Box/Unbox/HasType")
                }
                UnaryOpr::TupleField { .. } => {
                    panic!("internal error: ast_simplify should remove TupleField")
                }
                UnaryOpr::IsVariant { .. } | UnaryOpr::IntegerTypeBound(..) => {
                    let e1 = coerce_expr_to_native(ctx, &e1);
                    mk_expr(ExprX::UnaryOpr(op.clone(), e1))
                }
                UnaryOpr::CustomErr(_) => {
                    let exprx = ExprX::UnaryOpr(op.clone(), e1.clone());
                    SpannedTyped::new(&e1.span, &e1.typ, exprx)
                }
                UnaryOpr::Field(FieldOpr {
                    datatype,
                    variant,
                    field,
                    get_variant: _,
                    check: _,
                }) => {
                    let fields = &ctx.datatype_map[datatype].x.get_variant(variant).fields;
                    let field = crate::ast_util::get_field(fields, field);

                    // Force an expression of the form unbox(...) to match triggers with unbox:
                    let e1 = coerce_expr_to_poly(ctx, &e1);
                    let e1 = coerce_expr_to_native(ctx, &e1);

                    let exprx = ExprX::UnaryOpr(op.clone(), e1);
                    let typ = if typ_is_poly(ctx, &field.a.0) {
                        coerce_typ_to_poly(ctx, &expr.typ)
                    } else {
                        coerce_typ_to_native(ctx, &expr.typ)
                    };
                    mk_expr_typ(&typ, exprx)
                }
            }
        }
        ExprX::Loc(e) => {
            let expr = poly_expr(ctx, state, e);
            let typ = expr.typ.clone();
            mk_expr_typ(&typ, ExprX::Loc(expr))
        }
        ExprX::Binary(BinaryOp::ArrayIndex, e1, e2) => {
            let e1 = poly_expr(ctx, state, e1);
            let e2 = poly_expr(ctx, state, e2);
            let e1 = coerce_expr_to_native(ctx, &e1);
            let e2 = coerce_expr_to_poly(ctx, &e2);
            let typ = coerce_typ_to_poly(ctx, &expr.typ);
            mk_expr_typ(&typ, ExprX::Binary(BinaryOp::ArrayIndex, e1, e2))
        }
        ExprX::Binary(op, e1, e2) => {
            let e1 = poly_expr(ctx, state, e1);
            let e2 = poly_expr(ctx, state, e2);
            use BinaryOp::*;
            let (native, poly) = match op {
                And | Or | Xor | Implies | Inequality(_) => (true, false),
                HeightCompare { .. } => (false, true),
                Arith(..) => (true, false),
                Eq(_) | Ne => (false, false),
                Bitwise(..) => (true, false),
                StrGetChar { .. } => (true, false),
                ArrayIndex => unreachable!("ArrayIndex"),
            };
            if native {
                let e1 = coerce_expr_to_native(ctx, &e1);
                let e2 = coerce_expr_to_native(ctx, &e2);
                mk_expr(ExprX::Binary(*op, e1, e2))
            } else if poly {
                let e1 = coerce_expr_to_poly(ctx, &e1);
                let e2 = coerce_expr_to_poly(ctx, &e2);
                mk_expr(ExprX::Binary(*op, e1, e2))
            } else {
                let (e1, e2) = coerce_exprs_to_agree(ctx, &e1, &e2);
                mk_expr(ExprX::Binary(*op, e1, e2))
            }
        }
        ExprX::BinaryOpr(op @ crate::ast::BinaryOpr::ExtEq(..), e1, e2) => {
            let e1 = poly_expr(ctx, state, e1);
            let e2 = poly_expr(ctx, state, e2);
            let e1 = coerce_expr_to_poly(ctx, &e1);
            let e2 = coerce_expr_to_poly(ctx, &e2);
            mk_expr(ExprX::BinaryOpr(op.clone(), e1, e2))
        }
        ExprX::Multi(MultiOp::Chained(ops), es) => {
            let es =
                es.iter().map(|e| coerce_expr_to_native(ctx, &poly_expr(ctx, state, e))).collect();
            mk_expr(ExprX::Multi(MultiOp::Chained(ops.clone()), Arc::new(es)))
        }
        ExprX::Quant(quant, binders, e1) => {
            let natives = crate::triggers::predict_native_quant_vars(binders, &vec![e1]);
            let mut bs: Vec<VarBinder<Typ>> = Vec::new();
            state.types.push_scope(true);
            for binder in binders.iter() {
                let native = natives.contains(&binder.name);
                let typ = if native {
                    coerce_typ_to_native(ctx, &binder.a)
                } else {
                    coerce_typ_to_poly(ctx, &binder.a)
                };
                let _ = state.types.insert(binder.name.clone(), typ.clone());
                bs.push(binder.new_a(typ));
            }
            let e1 = coerce_expr_to_native(ctx, &poly_expr(ctx, state, e1));
            state.types.pop_scope();
            mk_expr(ExprX::Quant(*quant, Arc::new(bs), e1))
        }
        ExprX::Closure(binders, e1) => {
            let mut bs: Vec<VarBinder<Typ>> = Vec::new();
            state.types.push_scope(true);
            for binder in binders.iter() {
                let typ = coerce_typ_to_poly(ctx, &binder.a);
                let _ = state.types.insert(binder.name.clone(), typ.clone());
                bs.push(binder.new_a(typ));
            }
            let e1 = coerce_expr_to_poly(ctx, &poly_expr(ctx, state, e1));
            state.types.pop_scope();
            mk_expr(ExprX::Closure(Arc::new(bs), e1))
        }
        ExprX::ExecClosure { params, ret, body, requires, ensures, external_spec } => {
            let mut params1: Vec<VarBinder<Typ>> = Vec::new();
            state.types.push_scope(true);
            for binder in params.iter() {
                let typ = coerce_typ_to_native(ctx, &binder.a);
                let _ = state.types.insert(binder.name.clone(), typ.clone());
                params1.push(binder.new_a(typ));
            }

            let requires1 = requires
                .iter()
                .map(|req| coerce_expr_to_native(ctx, &poly_expr(ctx, state, req)))
                .collect();

            state.types.push_scope(true);

            let typ = coerce_typ_to_native(ctx, &ret.a);
            let _ = state.types.insert(ret.name.clone(), typ.clone());
            let ret1 = ret.new_a(typ);

            let ensures1 = ensures
                .iter()
                .map(|ens| coerce_expr_to_native(ctx, &poly_expr(ctx, state, ens)))
                .collect();

            state.types.pop_scope();

            let old_in_closure = state.in_exec_closure;
            state.in_exec_closure = true;
            let body1 = coerce_expr_to_native(ctx, &poly_expr(ctx, state, body));
            state.in_exec_closure = old_in_closure;

            state.types.pop_scope();

            state.types.push_scope(true);
            let (cid, cexpr) = external_spec
                .as_ref()
                .expect("external_spec should have been filled in in ast_simplify");
            let _ = state.types.insert(cid.clone(), expr.typ.clone());
            let cexpr1 = coerce_expr_to_native(ctx, &poly_expr(ctx, state, cexpr));
            state.types.pop_scope();

            mk_expr(ExprX::ExecClosure {
                params: Arc::new(params1),
                ret: ret1,
                body: body1,
                requires: Arc::new(requires1),
                ensures: Arc::new(ensures1),
                external_spec: Some((cid.clone(), cexpr1)),
            })
        }
        ExprX::ExecFnByName(fun) => mk_expr(ExprX::ExecFnByName(fun.clone())),
        ExprX::Choose { params, cond, body } => {
            // body is derived from cond but triggers are selected on the user-provided cond
            let natives = crate::triggers::predict_native_quant_vars(params, &vec![cond]);
            let mut bs: Vec<VarBinder<Typ>> = Vec::new();
            state.types.push_scope(true);
            for binder in params.iter() {
                let native = natives.contains(&binder.name);
                let typ = if native {
                    coerce_typ_to_native(ctx, &binder.a)
                } else {
                    coerce_typ_to_poly(ctx, &binder.a)
                };
                let _ = state.types.insert(binder.name.clone(), typ.clone());
                bs.push(binder.new_a(typ));
            }
            let cond = coerce_expr_to_native(ctx, &poly_expr(ctx, state, cond));
            let body = coerce_expr_to_poly(ctx, &poly_expr(ctx, state, body));
            state.types.pop_scope();
            mk_expr_typ(&body.clone().typ, ExprX::Choose { params: Arc::new(bs), cond, body })
        }
        ExprX::WithTriggers { triggers, body } => {
            let triggers = triggers
                .iter()
                .map(|es| Arc::new(es.iter().map(|e| poly_expr(ctx, state, e)).collect()));
            let triggers = Arc::new(triggers.collect());
            let body = poly_expr(ctx, state, body);
            mk_expr_typ(&body.clone().typ, ExprX::WithTriggers { triggers, body })
        }
        ExprX::Assign { init_not_mut, lhs: e1, rhs: e2, op } => {
            if op.is_some() {
                panic!("op should already be removed");
            }
            let e1 = poly_expr(ctx, state, e1);
            let e2 = if typ_is_poly(ctx, &e1.typ) {
                coerce_expr_to_poly(ctx, &poly_expr(ctx, state, e2))
            } else {
                coerce_expr_to_native(ctx, &poly_expr(ctx, state, e2))
            };
            mk_expr(ExprX::Assign { init_not_mut: *init_not_mut, lhs: e1, rhs: e2, op: *op })
        }
        ExprX::AssertCompute(e, m) => mk_expr(ExprX::AssertCompute(poly_expr(ctx, state, e), *m)),
        ExprX::Fuel(..) => expr.clone(),
        ExprX::RevealString(_) => expr.clone(),
        ExprX::Header(..) => panic!("Header should already be removed"),
        ExprX::AssertAssume { is_assume, expr: e1 } => {
            let e1 = coerce_expr_to_native(ctx, &poly_expr(ctx, state, e1));
            mk_expr(ExprX::AssertAssume { is_assume: *is_assume, expr: e1 })
        }
        ExprX::AssertAssumeUserDefinedTypeInvariant { is_assume, expr: e1, fun } => {
            let e1 = coerce_expr_to_native(ctx, &poly_expr(ctx, state, e1));
            mk_expr(ExprX::AssertAssumeUserDefinedTypeInvariant {
                is_assume: *is_assume,
                expr: e1,
                fun: fun.clone(),
            })
        }
        ExprX::AssertBy { vars, require, ensure, proof } => {
            let mut bs: Vec<VarBinder<Typ>> = Vec::new();
            state.types.push_scope(true);
            let natives = crate::triggers::predict_native_quant_vars(vars, &vec![require, ensure]);
            for binder in vars.iter() {
                let native = natives.contains(&binder.name);
                let typ = if native {
                    coerce_typ_to_native(ctx, &binder.a)
                } else {
                    coerce_typ_to_poly(ctx, &binder.a)
                };
                let _ = state.types.insert(binder.name.clone(), typ.clone());
                bs.push(binder.new_a(typ));
            }
            let require = coerce_expr_to_native(ctx, &poly_expr(ctx, state, require));
            let ensure = coerce_expr_to_native(ctx, &poly_expr(ctx, state, ensure));
            let proof = poly_expr(ctx, state, proof);
            state.types.pop_scope();
            let vars = Arc::new(bs);
            mk_expr(ExprX::AssertBy { vars, require, ensure, proof })
        }
        ExprX::AssertQuery { requires, ensures, proof, mode } => {
            state.types.push_scope(true);
            let requires =
                requires.iter().map(|e| coerce_expr_to_native(ctx, &poly_expr(ctx, state, e)));
            let requires = Arc::new(requires.collect());
            let ensures =
                ensures.iter().map(|e| coerce_expr_to_native(ctx, &poly_expr(ctx, state, e)));
            let ensures = Arc::new(ensures.collect());
            let proof = poly_expr(ctx, state, proof);
            state.types.pop_scope();
            mk_expr(ExprX::AssertQuery { requires, ensures, proof, mode: *mode })
        }
        ExprX::If(e0, e1, None) => {
            let e0 = coerce_expr_to_native(ctx, &poly_expr(ctx, state, e0));
            let e1 = poly_expr(ctx, state, e1);
            mk_expr(ExprX::If(e0, e1, None))
        }
        ExprX::If(e0, e1, Some(e2)) => {
            let e0 = coerce_expr_to_native(ctx, &poly_expr(ctx, state, e0));
            let e1 = poly_expr(ctx, state, e1);
            let e2 = poly_expr(ctx, state, e2);
            let (e1, e2) = coerce_exprs_to_agree(ctx, &e1, &e2);
            let t = if typ_is_poly(ctx, &e1.typ) {
                coerce_typ_to_poly(ctx, &expr.typ)
            } else {
                coerce_typ_to_native(ctx, &expr.typ)
            };
            mk_expr_typ(&t, ExprX::If(e0, e1.clone(), Some(e2)))
        }
        ExprX::Match(..) => panic!("Match should already be removed"),
        ExprX::Loop { loop_isolation, is_for_loop, label, cond, body, invs, decrease } => {
            let cond = cond.as_ref().map(|e| coerce_expr_to_native(ctx, &poly_expr(ctx, state, e)));
            let body = poly_expr(ctx, state, body);
            let invs = invs.iter().map(|inv| crate::ast::LoopInvariant {
                inv: coerce_expr_to_native(ctx, &poly_expr(ctx, state, &inv.inv)),
                ..inv.clone()
            });
            let invs = Arc::new(invs.collect());
            let decrease =
                decrease.iter().map(|e| coerce_expr_to_native(ctx, &poly_expr(ctx, state, e)));
            let decrease = Arc::new(decrease.collect());
            mk_expr(ExprX::Loop {
                loop_isolation: *loop_isolation,
                is_for_loop: *is_for_loop,
                label: label.clone(),
                cond,
                body,
                invs,
                decrease,
            })
        }
        ExprX::OpenInvariant(inv, binder, body, atomicity) => {
            let inv = coerce_expr_to_poly(ctx, &poly_expr(ctx, state, inv));
            state.types.push_scope(true);
            let typ = coerce_typ_to_native(ctx, &binder.a);
            let _ = state.types.insert(binder.name.clone(), typ.clone());
            let body = poly_expr(ctx, state, body);
            state.types.pop_scope();
            let binder = binder.new_a(typ.clone());
            mk_expr(ExprX::OpenInvariant(inv, binder, body, *atomicity))
        }
        ExprX::Return(None) => expr.clone(),
        ExprX::Return(Some(e1)) => {
            let e1 = if state.is_trait && !state.in_exec_closure {
                coerce_expr_to_poly(ctx, &poly_expr(ctx, state, e1))
            } else {
                coerce_expr_to_native(ctx, &poly_expr(ctx, state, e1))
            };
            mk_expr(ExprX::Return(Some(e1.clone())))
        }
        ExprX::BreakOrContinue { label: _, is_break: _ } => expr.clone(),
        ExprX::Ghost { alloc_wrapper, tracked, expr: e1 } => {
            let expr = poly_expr(ctx, state, e1);
            mk_expr(ExprX::Ghost { alloc_wrapper: *alloc_wrapper, tracked: *tracked, expr })
        }
        ExprX::Block(ss, e1) => {
            let mut stmts: Vec<Stmt> = Vec::new();
            for s in ss.iter() {
                match &s.x {
                    StmtX::Expr(_) => {}
                    StmtX::Decl { .. } => state.types.push_scope(true),
                }
                stmts.push(poly_stmt(ctx, state, s));
            }
            let e1 = match e1 {
                None => None,
                Some(e) => Some(poly_expr(ctx, state, e)),
            };
            for s in ss.iter() {
                match &s.x {
                    StmtX::Expr(_) => {}
                    StmtX::Decl { .. } => state.types.pop_scope(),
                }
            }
            match e1.clone() {
                None => mk_expr(ExprX::Block(Arc::new(stmts), e1)),
                Some(e) => mk_expr_typ(&e.typ, ExprX::Block(Arc::new(stmts), e1)),
            }
        }
        ExprX::AirStmt(_) => expr.clone(),
    }
}

fn poly_stmt(ctx: &Ctx, state: &mut State, stmt: &Stmt) -> Stmt {
    match &stmt.x {
        StmtX::Expr(expr) => {
            let stmtx = StmtX::Expr(poly_expr(ctx, state, expr));
            Spanned::new(stmt.span.clone(), stmtx)
        }
        StmtX::Decl { pattern, mode, init } => {
            if let PatternX::Var { name, mutable: _ } = &pattern.x {
                let typ = coerce_typ_to_native(ctx, &pattern.typ);
                let pattern = SpannedTyped::new(&pattern.span, &typ, pattern.x.clone());
                let init = if let Some(init) = init {
                    Some(coerce_expr_to_native(ctx, &poly_expr(ctx, state, init)))
                } else {
                    None
                };
                let _ = state.types.insert(name.clone(), pattern.typ.clone());
                let stmtx = StmtX::Decl { pattern: pattern.clone(), mode: *mode, init };
                Spanned::new(stmt.span.clone(), stmtx)
            } else {
                panic!("internal error: ast_simplify should eliminate patterns")
            }
        }
    }
}

fn poly_function(ctx: &Ctx, function: &Function) -> Function {
    let FunctionX {
        name,
        proxy,
        kind,
        visibility,
        owning_module,
        mode: mut function_mode,
        fuel,
        typ_params,
        typ_bounds,
        params,
        ret,
        require,
        ensure,
        decrease,
        decrease_when,
        decrease_by,
        broadcast_forall,
        fndef_axioms,
        mask_spec,
        unwind_spec,
        item_kind,
        publish,
        attrs,
        body,
        extra_dependencies,
    } = &function.x;

    if attrs.is_decrease_by {
        // This is actually code for a the spec function that has the decreases clause
        function_mode = Mode::Spec;
    }

    let mut types = ScopeMap::new();
    types.push_scope(true);

    let is_trait = !matches!(kind, FunctionKind::Static);

    // Return type is left native (except for trait methods)
    let ret_typ = if is_trait && (function.x.has_return() || function_mode == Mode::Spec) {
        coerce_typ_to_poly(ctx, &ret.x.typ)
    } else {
        coerce_typ_to_native(ctx, &ret.x.typ)
    };
    let ret = Spanned::new(ret.span.clone(), ParamX { typ: ret_typ, ..ret.x.clone() });
    // Parameter types are made Poly for spec functions and trait methods
    let mut new_params: Vec<Param> = Vec::new();
    for param in params.iter() {
        let ParamX { name, typ, mode, is_mut, unwrapped_info } = &param.x;
        let typ = if function_mode == Mode::Spec || is_trait {
            coerce_typ_to_poly(ctx, typ)
        } else {
            coerce_typ_to_native(ctx, typ)
        };
        let _ = types.insert(name.clone(), typ.clone());
        let paramx = ParamX {
            name: name.clone(),
            typ,
            mode: *mode,
            is_mut: *is_mut,
            unwrapped_info: unwrapped_info.clone(),
        };
        new_params.push(Spanned::new(param.span.clone(), paramx));
    }
    let params = Arc::new(new_params);

    let mut state = State { types, is_trait, in_exec_closure: false };

    let native_expr =
        |state: &mut State, e: &Expr| coerce_expr_to_native(ctx, &poly_expr(ctx, state, e));
    let native_exprs = |state: &mut State, es: &Exprs| {
        let mut exprs: Vec<Expr> = Vec::new();
        for e in es.iter() {
            exprs.push(native_expr(state, e));
        }
        Arc::new(exprs)
    };
    let require = native_exprs(&mut state, require);

    state.types.push_scope(true);
    if function.x.has_return_name() {
        let _ = state.types.insert(ret.x.name.clone(), ret.x.typ.clone());
    }
    let ensure = native_exprs(&mut state, ensure);
    state.types.pop_scope();

    let decrease = native_exprs(&mut state, decrease);
    let decrease_when =
        decrease_when.as_ref().map(|e| coerce_expr_to_native(ctx, &poly_expr(ctx, &mut state, e)));

    let mask_spec = match mask_spec {
        Some(MaskSpec::InvariantOpens(es)) => {
            Some(MaskSpec::InvariantOpens(native_exprs(&mut state, es)))
        }
        Some(MaskSpec::InvariantOpensExcept(es)) => {
            Some(MaskSpec::InvariantOpensExcept(native_exprs(&mut state, es)))
        }
        None => None,
    };
    let unwind_spec = match unwind_spec {
        None => None,
        Some(UnwindSpec::MayUnwind) => Some(UnwindSpec::MayUnwind),
        Some(UnwindSpec::NoUnwind) => Some(UnwindSpec::NoUnwind),
        Some(UnwindSpec::NoUnwindWhen(e)) => {
            Some(UnwindSpec::NoUnwindWhen(native_expr(&mut state, e)))
        }
    };

    let body = if let Some(body) = body {
        if is_trait && (function.x.has_return() || function_mode == Mode::Spec) {
            Some(coerce_expr_to_poly(ctx, &poly_expr(ctx, &mut state, body)))
        } else {
            Some(coerce_expr_to_native(ctx, &poly_expr(ctx, &mut state, body)))
        }
    } else {
        None
    };

    state.types.pop_scope();
    assert_eq!(state.types.num_scopes(), 0);

    assert!(broadcast_forall.is_none());
    let broadcast_forall = if attrs.broadcast_forall {
        // Create a coerce_typ_to_poly version of the parameters, requires, ensures
        state.types.push_scope(true);
        let mut bs: Vec<VarBinder<Typ>> = Vec::new();
        for param in params.iter() {
            let ParamX { name, typ, .. } = &param.x;
            bs.push(Arc::new(crate::ast::VarBinderX { name: name.clone(), a: typ.clone() }));
        }
        let all_exps: Vec<&Expr> =
            (function.x.require.iter()).chain(function.x.ensure.iter()).collect();
        let natives = crate::triggers::predict_native_quant_vars(&Arc::new(bs), &all_exps);
        let mut new_params: Vec<Param> = Vec::new();
        for param in params.iter() {
            let ParamX { name, typ, mode, is_mut, unwrapped_info } = &param.x;
            let native = natives.contains(name);
            let typ =
                if native { coerce_typ_to_native(ctx, typ) } else { coerce_typ_to_poly(ctx, typ) };
            let _ = state.types.insert(name.clone(), typ.clone());
            let paramx = ParamX {
                name: name.clone(),
                typ,
                mode: *mode,
                is_mut: *is_mut,
                unwrapped_info: unwrapped_info.clone(),
            };
            new_params.push(Spanned::new(param.span.clone(), paramx));
        }
        let broadcast_params = Arc::new(new_params);

        let span = &function.span;
        let mut reqs: Vec<Expr> = Vec::new();
        reqs.extend(crate::traits::trait_bounds_to_ast(
            ctx,
            &function.span,
            &function.x.typ_bounds,
        ));
        reqs.extend((*function.x.require).clone());
        let req = crate::ast_util::conjoin(span, &reqs);
        let ens = crate::ast_util::conjoin(span, &*function.x.ensure);
        let req_ens = crate::ast_util::mk_implies(span, &req, &ens);
        let req_ens = coerce_expr_to_native(ctx, &poly_expr(ctx, &mut state, &req_ens));

        state.types.pop_scope();
        assert_eq!(state.types.num_scopes(), 0);
        Some((broadcast_params, req_ens))
    } else {
        None
    };

    let fndef_axioms = if let Some(es) = fndef_axioms {
        let mut es2 = vec![];
        for e in es.iter() {
            let e2 = coerce_expr_to_native(ctx, &poly_expr(ctx, &mut state, &e));
            es2.push(e2);
        }
        Some(Arc::new(es2))
    } else {
        None
    };

    let functionx = FunctionX {
        name: name.clone(),
        proxy: proxy.clone(),
        kind: kind.clone(),
        visibility: visibility.clone(),
        owning_module: owning_module.clone(),
        mode: function_mode,
        fuel: *fuel,
        typ_params: typ_params.clone(),
        typ_bounds: typ_bounds.clone(),
        params,
        ret,
        require,
        ensure,
        decrease,
        decrease_when,
        decrease_by: decrease_by.clone(),
        broadcast_forall,
        fndef_axioms,
        mask_spec,
        unwind_spec,
        item_kind: *item_kind,
        publish: *publish,
        attrs: attrs.clone(),
        body,
        extra_dependencies: extra_dependencies.clone(),
    };
    Spanned::new(function.span.clone(), functionx)
}

fn poly_datatype(ctx: &Ctx, datatype: &Datatype) -> Datatype {
    let variants = vec_map(&*datatype.x.variants, |v| Variant {
        fields: Arc::new(vec_map(&v.fields, |f| {
            f.map_a(|(t, m, v)| (coerce_typ_to_native(ctx, t), *m, v.clone()))
        })),
        ..v.clone()
    });
    let variants = Arc::new(variants);
    let datatypex = DatatypeX { variants, ..datatype.x.clone() };
    Spanned::new(datatype.span.clone(), datatypex)
}

fn poly_assoc_type_impl(ctx: &Ctx, assoc: &AssocTypeImpl) -> AssocTypeImpl {
    crate::ast_visitor::map_assoc_type_impl_visitor_env(assoc, &mut (), &|(), t| {
        Ok(coerce_typ_to_poly(ctx, t))
    })
    .expect("poly_assoc_type_impl")
}

pub fn poly_krate_for_module(ctx: &mut Ctx, krate: &Krate) -> Krate {
    let KrateX {
        functions,
        reveal_groups,
        datatypes,
        traits,
        trait_impls,
        assoc_type_impls,
        modules: module_ids,
        external_fns,
        external_types,
        path_as_rust_names,
        arch,
    } = &**krate;
    let kratex = KrateX {
        functions: functions.iter().map(|f| poly_function(ctx, f)).collect(),
        reveal_groups: reveal_groups.clone(),
        datatypes: datatypes.iter().map(|d| poly_datatype(ctx, d)).collect(),
        traits: traits.clone(),
        trait_impls: trait_impls.clone(),
        assoc_type_impls: assoc_type_impls.iter().map(|a| poly_assoc_type_impl(ctx, a)).collect(),
        modules: module_ids.clone(),
        external_fns: external_fns.clone(),
        external_types: external_types.clone(),
        path_as_rust_names: path_as_rust_names.clone(),
        arch: arch.clone(),
    };
    ctx.func_map = HashMap::new();
    for function in kratex.functions.iter() {
        ctx.func_map.insert(function.x.name.clone(), function.clone());
    }
    ctx.datatype_map = HashMap::new();
    for datatype in kratex.datatypes.iter() {
        ctx.datatype_map.insert(datatype.x.path.clone(), datatype.clone());
    }
    Arc::new(kratex)
}
