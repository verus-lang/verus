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
*/

use crate::ast::{
    BinaryOp, CallTarget, Datatype, DatatypeX, Expr, ExprX, Exprs, FieldOpr, Function,
    FunctionKind, FunctionX, Ident, IntRange, Krate, KrateX, MaskSpec, Mode, MultiOp, Param,
    ParamX, Path, PatternX, SpannedTyped, Stmt, StmtX, Typ, TypX, UnaryOp, UnaryOpr,
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
}

struct State {
    types: ScopeMap<Ident, Typ>,
    is_trait: bool,
}

pub(crate) fn typ_as_mono(typ: &Typ) -> Option<MonoTyp> {
    match &**typ {
        TypX::Bool => Some(Arc::new(MonoTypX::Bool)),
        TypX::Int(range) => Some(Arc::new(MonoTypX::Int(*range))),
        TypX::Datatype(path, typs) => {
            let mut monotyps: Vec<MonoTyp> = Vec::new();
            for typ in typs.iter() {
                if let Some(monotyp) = typ_as_mono(typ) {
                    monotyps.push(monotyp);
                } else {
                    return None;
                }
            }
            Some(Arc::new(MonoTypX::Datatype(path.clone(), Arc::new(monotyps))))
        }
        _ => None,
    }
}

pub(crate) fn monotyp_to_typ(monotyp: &MonoTyp) -> Typ {
    match &**monotyp {
        MonoTypX::Bool => Arc::new(TypX::Bool),
        MonoTypX::Int(range) => Arc::new(TypX::Int(*range)),
        MonoTypX::Datatype(path, typs) => {
            let typs = vec_map(&**typs, monotyp_to_typ);
            Arc::new(TypX::Datatype(path.clone(), Arc::new(typs)))
        }
    }
}

pub(crate) fn typ_is_poly(ctx: &Ctx, typ: &Typ) -> bool {
    match &**typ {
        TypX::Bool | TypX::Int(_) | TypX::Lambda(..) => false,
        TypX::Tuple(_) => panic!("internal error: Tuple should be removed by ast_simplify"),
        TypX::Datatype(path, _) => {
            if ctx.datatype_is_transparent[path] {
                false
            } else {
                typ_as_mono(typ).is_none()
            }
        }
        TypX::Boxed(_) | TypX::TypParam(_) => true,
        TypX::TypeId => panic!("internal error: TypeId created too soon"),
        TypX::Air(_) => panic!("internal error: Air type created too soon"),
    }
}

fn coerce_typ_to_native(ctx: &Ctx, typ: &Typ) -> Typ {
    match &**typ {
        TypX::Bool | TypX::Int(_) | TypX::Lambda(..) => typ.clone(),
        TypX::Tuple(_) => panic!("internal error: Tuple should be removed by ast_simplify"),
        TypX::Datatype(path, _) => {
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
        TypX::Boxed(_) | TypX::TypParam(_) => typ.clone(),
        TypX::TypeId => panic!("internal error: TypeId created too soon"),
        TypX::Air(_) => panic!("internal error: Air type created too soon"),
    }
}

fn coerce_typ_to_poly(_ctx: &Ctx, typ: &Typ) -> Typ {
    match &**typ {
        TypX::Bool | TypX::Int(_) | TypX::Lambda(..) => Arc::new(TypX::Boxed(typ.clone())),
        TypX::Tuple(_) => panic!("internal error: Tuple should be removed by ast_simplify"),
        TypX::Datatype(..) => Arc::new(TypX::Boxed(typ.clone())),
        TypX::Boxed(_) | TypX::TypParam(_) => typ.clone(),
        TypX::TypeId => panic!("internal error: TypeId created too soon"),
        TypX::Air(_) => panic!("internal error: Air type created too soon"),
    }
}

fn coerce_expr_to_native(ctx: &Ctx, expr: &Expr) -> Expr {
    match &*expr.typ {
        TypX::Bool | TypX::Int(_) | TypX::Lambda(..) | TypX::Datatype(..) => expr.clone(),
        TypX::Tuple(_) => panic!("internal error: Tuple should be removed by ast_simplify"),
        TypX::Boxed(typ) => {
            if typ_is_poly(ctx, typ) {
                expr.clone()
            } else {
                let op = UnaryOpr::Unbox(typ.clone());
                let exprx = ExprX::UnaryOpr(op, expr.clone());
                SpannedTyped::new(&expr.span, typ, exprx)
            }
        }
        TypX::TypParam(_) => expr.clone(),
        TypX::TypeId => panic!("internal error: TypeId created too soon"),
        TypX::Air(_) => panic!("internal error: Air type created too soon"),
    }
}

fn coerce_expr_to_poly(ctx: &Ctx, expr: &Expr) -> Expr {
    match &*expr.typ {
        TypX::Datatype(path, _)
            if !ctx.datatype_is_transparent[path] && typ_as_mono(&expr.typ).is_none() =>
        {
            expr.clone()
        }
        TypX::Bool | TypX::Int(_) | TypX::Lambda(..) | TypX::Datatype(..) => {
            let op = UnaryOpr::Box(expr.typ.clone());
            let exprx = ExprX::UnaryOpr(op, expr.clone());
            let typ = Arc::new(TypX::Boxed(expr.typ.clone()));
            SpannedTyped::new(&expr.span, &typ, exprx)
        }
        TypX::Tuple(_) => panic!("internal error: Tuple should be removed by ast_simplify"),
        TypX::Boxed(_) | TypX::TypParam(_) => expr.clone(),
        TypX::TypeId => panic!("internal error: TypeId created too soon"),
        TypX::Air(_) => panic!("internal error: Air type created too soon"),
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
        ExprX::Call(target, exprs) => match target {
            CallTarget::Static(name, _) => {
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
                let typ = if is_trait || typ_is_poly(ctx, &function.ret.x.typ) {
                    coerce_typ_to_poly(ctx, &expr.typ)
                } else {
                    coerce_typ_to_native(ctx, &expr.typ)
                };
                mk_expr_typ(&typ, ExprX::Call(target.clone(), Arc::new(args)))
            }
            CallTarget::FnSpec(e) => {
                let target =
                    CallTarget::FnSpec(coerce_expr_to_native(ctx, &poly_expr(ctx, state, e)));
                let exprs = exprs
                    .iter()
                    .map(|e| coerce_expr_to_poly(ctx, &poly_expr(ctx, state, e)))
                    .collect();
                let typ = coerce_typ_to_poly(ctx, &expr.typ);
                mk_expr_typ(&typ, ExprX::Call(target, Arc::new(exprs)))
            }
        },
        ExprX::Tuple(_) => panic!("internal error: ast_simplify should remove Tuple"),
        ExprX::Ctor(path, variant, binders, update) => {
            assert!(update.is_none()); // removed by ast_simplify
            let fields = &ctx.datatype_map[path].x.get_variant(variant).a;
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
        ExprX::Unary(op, e1) => {
            let e1 = poly_expr(ctx, state, e1);
            match op {
                UnaryOp::Not | UnaryOp::Clip(_) | UnaryOp::BitNot => {
                    let e1 = coerce_expr_to_native(ctx, &e1);
                    mk_expr(ExprX::Unary(*op, e1))
                }
                UnaryOp::Trigger(_) => mk_expr_typ(&e1.typ, ExprX::Unary(*op, e1.clone())),
            }
        }
        ExprX::UnaryOpr(op, e1) => {
            let e1 = poly_expr(ctx, state, e1);
            match op {
                UnaryOpr::Box(_) | UnaryOpr::Unbox(_) | UnaryOpr::HasType(_) => {
                    panic!("internal error: already has Box/Unbox/HasType")
                }
                UnaryOpr::TupleField { .. } => {
                    panic!("internal error: ast_simplify should remove TupleField")
                }
                UnaryOpr::IsVariant { .. } => {
                    let e1 = coerce_expr_to_native(ctx, &e1);
                    mk_expr(ExprX::UnaryOpr(op.clone(), e1))
                }
                UnaryOpr::Field(FieldOpr { datatype, variant, field }) => {
                    let fields = &ctx.datatype_map[datatype].x.get_variant(variant).a;
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
        ExprX::Binary(op, e1, e2) => {
            let e1 = poly_expr(ctx, state, e1);
            let e2 = poly_expr(ctx, state, e2);
            use BinaryOp::*;
            let native = match op {
                And | Or | Xor | Implies | Inequality(_) => true,
                Arith(..) => true,
                Eq(_) | Ne => false,
                Bitwise(..) => true,
            };
            if native {
                let e1 = coerce_expr_to_native(ctx, &e1);
                let e2 = coerce_expr_to_native(ctx, &e2);
                mk_expr(ExprX::Binary(*op, e1, e2))
            } else {
                let (e1, e2) = coerce_exprs_to_agree(ctx, &e1, &e2);
                mk_expr(ExprX::Binary(*op, e1, e2))
            }
        }
        ExprX::Multi(MultiOp::Chained(ops), es) => {
            let es =
                es.iter().map(|e| coerce_expr_to_native(ctx, &poly_expr(ctx, state, e))).collect();
            mk_expr(ExprX::Multi(MultiOp::Chained(ops.clone()), Arc::new(es)))
        }
        ExprX::Quant(quant, binders, e1) => {
            let mut bs: Vec<Binder<Typ>> = Vec::new();
            state.types.push_scope(true);
            for binder in binders.iter() {
                let typ = if quant.boxed_params {
                    coerce_typ_to_poly(ctx, &binder.a)
                } else {
                    coerce_typ_to_native(ctx, &binder.a)
                };
                let _ = state.types.insert(binder.name.clone(), typ.clone());
                bs.push(binder.new_a(typ));
            }
            let e1 = coerce_expr_to_native(ctx, &poly_expr(ctx, state, e1));
            state.types.pop_scope();
            mk_expr(ExprX::Quant(*quant, Arc::new(bs), e1))
        }
        ExprX::Closure(binders, e1) => {
            let mut bs: Vec<Binder<Typ>> = Vec::new();
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
        ExprX::Choose { params, cond, body } => {
            let mut bs: Vec<Binder<Typ>> = Vec::new();
            state.types.push_scope(true);
            for binder in params.iter() {
                let typ = coerce_typ_to_poly(ctx, &binder.a);
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
            mk_expr(ExprX::WithTriggers { triggers, body })
        }
        ExprX::Assign { init_not_mut, lhs: e1, rhs: e2 } => {
            let e1 = poly_expr(ctx, state, e1);
            let e2 = if typ_is_poly(ctx, &e1.typ) {
                coerce_expr_to_poly(ctx, &poly_expr(ctx, state, e2))
            } else {
                coerce_expr_to_native(ctx, &poly_expr(ctx, state, e2))
            };
            mk_expr(ExprX::Assign { init_not_mut: *init_not_mut, lhs: e1, rhs: e2 })
        }
        ExprX::AssertBV(e) => mk_expr(ExprX::AssertBV(poly_expr(ctx, state, e))),
        ExprX::Fuel(..) => expr.clone(),
        ExprX::Header(..) => panic!("Header should already be removed"),
        ExprX::Admit => expr.clone(),
        ExprX::Forall { vars, require, ensure, proof } => {
            let mut bs: Vec<Binder<Typ>> = Vec::new();
            state.types.push_scope(true);
            for binder in vars.iter() {
                let typ = coerce_typ_to_poly(ctx, &binder.a);
                let _ = state.types.insert(binder.name.clone(), typ.clone());
                bs.push(binder.new_a(typ));
            }
            let require = coerce_expr_to_native(ctx, &poly_expr(ctx, state, require));
            let ensure = coerce_expr_to_native(ctx, &poly_expr(ctx, state, ensure));
            let proof = poly_expr(ctx, state, proof);
            state.types.pop_scope();
            let vars = Arc::new(bs);
            mk_expr(ExprX::Forall { vars, require, ensure, proof })
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
            mk_expr_typ(&e1.typ, ExprX::If(e0, e1.clone(), Some(e2)))
        }
        ExprX::Match(..) => panic!("Match should already be removed"),
        ExprX::While { cond, body, invs } => {
            let cond = coerce_expr_to_native(ctx, &poly_expr(ctx, state, cond));
            let body = poly_expr(ctx, state, body);
            let invs = invs.iter().map(|e| coerce_expr_to_native(ctx, &poly_expr(ctx, state, e)));
            let invs = Arc::new(invs.collect());
            mk_expr(ExprX::While { cond, body, invs })
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
            let e1 = if state.is_trait {
                coerce_expr_to_poly(ctx, &poly_expr(ctx, state, e1))
            } else {
                coerce_expr_to_native(ctx, &poly_expr(ctx, state, e1))
            };
            mk_expr(ExprX::Return(Some(e1.clone())))
        }
        ExprX::Ghost { alloc_wrapper, tracked, expr: e1 } => {
            let expr = poly_expr(ctx, state, e1);
            mk_expr(ExprX::Ghost { alloc_wrapper: alloc_wrapper.clone(), tracked: *tracked, expr })
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
        kind,
        visibility,
        mode: mut function_mode,
        fuel,
        typ_bounds,
        params,
        ret,
        require,
        ensure,
        decrease,
        decrease_when,
        decrease_by,
        broadcast_forall,
        mask_spec,
        is_const,
        is_string_literal,
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
    let ret_typ = if is_trait && function.x.has_return() {
        coerce_typ_to_poly(ctx, &ret.x.typ)
    } else {
        coerce_typ_to_native(ctx, &ret.x.typ)
    };
    let ret = Spanned::new(ret.span.clone(), ParamX { typ: ret_typ, ..ret.x.clone() });
    // Parameter types are made Poly for spec functions and trait methods
    let mut new_params: Vec<Param> = Vec::new();
    for param in params.iter() {
        let ParamX { name, typ, mode, is_mut } = &param.x;
        let typ = if function_mode == Mode::Spec || is_trait {
            coerce_typ_to_poly(ctx, typ)
        } else {
            coerce_typ_to_native(ctx, typ)
        };
        let _ = types.insert(name.clone(), typ.clone());
        let paramx = ParamX { name: name.clone(), typ, mode: *mode, is_mut: *is_mut };
        new_params.push(Spanned::new(param.span.clone(), paramx));
    }
    let params = Arc::new(new_params);

    let mut state = State { types, is_trait };

    let native_exprs = |state: &mut State, es: &Exprs| {
        let mut exprs: Vec<Expr> = Vec::new();
        for e in es.iter() {
            exprs.push(coerce_expr_to_native(ctx, &poly_expr(ctx, state, e)));
        }
        Arc::new(exprs)
    };
    let require = native_exprs(&mut state, require);

    state.types.push_scope(true);
    if function.x.has_return() {
        let _ = state.types.insert(ret.x.name.clone(), ret.x.typ.clone());
    }
    let ensure = native_exprs(&mut state, ensure);
    state.types.pop_scope();

    let decrease = native_exprs(&mut state, decrease);
    let decrease_when =
        decrease_when.as_ref().map(|e| coerce_expr_to_native(ctx, &poly_expr(ctx, &mut state, e)));

    let mask_spec = match mask_spec {
        MaskSpec::InvariantOpens(es) => MaskSpec::InvariantOpens(native_exprs(&mut state, es)),
        MaskSpec::InvariantOpensExcept(es) => {
            MaskSpec::InvariantOpensExcept(native_exprs(&mut state, es))
        }
        MaskSpec::NoSpec => MaskSpec::NoSpec,
    };

    let body = if let Some(body) = body {
        if is_trait && function.x.has_return() {
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
        let mut new_params: Vec<Param> = Vec::new();
        for param in params.iter() {
            let ParamX { name, typ, mode, is_mut } = &param.x;
            let typ = coerce_typ_to_poly(ctx, typ);
            let _ = state.types.insert(name.clone(), typ.clone());
            let paramx = ParamX { name: name.clone(), typ, mode: *mode, is_mut: *is_mut };
            new_params.push(Spanned::new(param.span.clone(), paramx));
        }
        let broadcast_params = Arc::new(new_params);

        let span = &function.span;
        let req = crate::ast_util::conjoin(span, &*function.x.require);
        let ens = crate::ast_util::conjoin(span, &*function.x.ensure);
        let req_ens = crate::ast_util::mk_implies(span, &req, &ens);
        let req_ens = coerce_expr_to_native(ctx, &poly_expr(ctx, &mut state, &req_ens));

        state.types.pop_scope();
        assert_eq!(state.types.num_scopes(), 0);
        Some((broadcast_params, req_ens))
    } else {
        None
    };

    let functionx = FunctionX {
        name: name.clone(),
        kind: kind.clone(),
        visibility: visibility.clone(),
        mode: function_mode,
        fuel: *fuel,
        typ_bounds: typ_bounds.clone(),
        params,
        ret,
        require,
        ensure,
        decrease,
        decrease_when,
        decrease_by: decrease_by.clone(),
        broadcast_forall,
        mask_spec,
        is_const: *is_const,
        is_string_literal: *is_string_literal,
        publish: *publish,
        attrs: attrs.clone(),
        body,
        extra_dependencies: extra_dependencies.clone(),
    };
    Spanned::new(function.span.clone(), functionx)
}

fn poly_datatype(ctx: &Ctx, datatype: &Datatype) -> Datatype {
    let variants = vec_map(&*datatype.x.variants, |v| {
        v.map_a(|fields| {
            Arc::new(vec_map(fields, |f| {
                f.map_a(|(t, m, v)| (coerce_typ_to_native(ctx, t), *m, v.clone()))
            }))
        })
    });
    let variants = Arc::new(variants);
    let datatypex = DatatypeX { variants, ..datatype.x.clone() };
    Spanned::new(datatype.span.clone(), datatypex)
}

pub fn poly_krate_for_module(ctx: &mut Ctx, krate: &Krate) -> Krate {
    let KrateX { functions, datatypes, traits, module_ids } = &**krate;
    let kratex = KrateX {
        functions: functions.iter().map(|f| poly_function(ctx, f)).collect(),
        datatypes: datatypes.iter().map(|d| poly_datatype(ctx, d)).collect(),
        traits: traits.clone(),
        module_ids: module_ids.clone(),
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
