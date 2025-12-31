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

For triggers on arithmetic expressions like #[trigger] (x * y),
we use int instead of Poly for the arithmetic variables in the trigger.
(This is an exception to the table above.)
Otherwise, an expression like 3 * 4 would fail to match the trigger (Unbox(x) * Unbox(y)).

Note that if a variable x is used *both* as a function argument and an arithmetic argument,
as in #[trigger] g(f(x), x + 1), we have more flexibility, because any term passed to both
the function and the arithmetic must be boxed or unboxed in one or the other.
For example, in g(f(3), 3 + 1) would be represented as g(f(Box(3)), Box(3 + 1)),
so that Box(3) triggers the unbox-box axiom yielding Unbox(Box(3)) = 3.
In this case, a trigger of g(f(x), Unbox(x) + 1) for x: Poly e-matches the expanded term
g(f(Box(3)), Box(Unbox(Box(3)) + 1)).
We take advantage of this to support mixed function-arithmetic triggers with Poly variables
(native variables would also work if we wanted, relying on Box(Unbox(x)) axioms.)
*/

use crate::ast::{
    AssocTypeImpl, BinaryOp, Datatype, DatatypeX, Dt, FieldOpr, FunctionKind, IntRange, Mode,
    NullaryOpr, Primitive, SpannedTyped, Typ, TypDecorationArg, TypX, Typs, UnaryOp, UnaryOpr,
    VarBinder, VarBinderX, VarBinders, VarIdent, Variant,
};
use crate::context::Ctx;
use crate::def::Spanned;
use crate::sst::{
    BndX, CallFun, Dest, Exp, ExpX, Exps, FuncCheckSst, FuncDeclSst, FunctionSst, FunctionSstX,
    InternalFun, KrateSst, KrateSstX, LocalDecl, LocalDeclKind, Par, ParX, Pars, PostConditionSst,
    Stm, StmX, Stms, Trigs, UnwindSst,
};
use crate::triggers::native_quant_vars;
use crate::util::vec_map;
use air::ast::Binder;
use air::scope_map::ScopeMap;
use std::collections::{HashMap, HashSet};
use std::sync::Arc;

pub type MonoTyp = Arc<MonoTypX>;
pub type MonoTyps = Arc<Vec<MonoTyp>>;
#[derive(Clone, Debug, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub enum MonoTypX {
    Bool,
    Int(IntRange),
    Real,
    Float(u32),
    Datatype(Dt, MonoTyps),
    Decorate(crate::ast::TypDecoration, MonoTyp),
    Decorate2(crate::ast::TypDecoration, MonoTyps),
    Primitive(Primitive, MonoTyps),
}

struct State {
    remaining_temps: HashSet<VarIdent>,
    types: ScopeMap<VarIdent, Typ>,
    temp_types: HashMap<VarIdent, Typ>,
    is_trait: bool,
    in_exec_closure: bool,
    // is the function return type an opaque type?
    is_ret_opaque: bool,
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
        TypX::Real => Some(Arc::new(MonoTypX::Real)),
        TypX::Float(range) => Some(Arc::new(MonoTypX::Float(*range))),
        TypX::Datatype(path, typs, _impl_paths) => {
            let monotyps = monotyps_as_mono(typs)?;
            Some(Arc::new(MonoTypX::Datatype(path.clone(), Arc::new(monotyps))))
        }
        TypX::Dyn(..) => None,
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
        TypX::TypeId => panic!("internal error: TypeId created too soon"),
        TypX::Air(_) => panic!("internal error: Air type created too soon"),
        TypX::Boxed(..) | TypX::TypParam(..) | TypX::SpecFn(..) | TypX::FnDef(..) => None,
        TypX::ConstInt(_) => None,
        TypX::ConstBool(_) => None,
        TypX::Projection { .. } => None,
        TypX::PointeeMetadata(_) => None,
        TypX::MutRef(_) => None,
        TypX::Opaque { .. } => None,
    }
}

pub(crate) fn monotyp_to_typ(monotyp: &MonoTyp) -> Typ {
    match &**monotyp {
        MonoTypX::Bool => Arc::new(TypX::Bool),
        MonoTypX::Int(range) => Arc::new(TypX::Int(*range)),
        MonoTypX::Real => Arc::new(TypX::Real),
        MonoTypX::Float(range) => Arc::new(TypX::Float(*range)),
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
        TypX::Bool | TypX::Int(_) | TypX::Real | TypX::Float(_) => false,
        TypX::SpecFn(..) | TypX::FnDef(..) => false,
        TypX::Primitive(Primitive::Array, _) => false,
        TypX::AnonymousClosure(..) => {
            panic!("internal error: AnonymousClosure should be removed by ast_simplify")
        }
        TypX::Datatype(path, _, _) => {
            if ctx.datatype_is_transparent[path] {
                false
            } else {
                typ_as_mono(typ).is_none()
            }
        }
        TypX::Dyn(..) => true,
        TypX::Decorate(_, _, t) => typ_is_poly(ctx, t),
        // Note: we rely on rust_to_vir_base normalizing TypX::Projection { .. }.
        // If it normalized to a projection, it is poly; otherwise it is handled by
        // one of the other TypX::* cases.
        TypX::Boxed(_) | TypX::TypParam(_) | TypX::Projection { .. } | TypX::PointeeMetadata(_) => {
            true
        }
        TypX::Primitive(_, _) => typ_as_mono(typ).is_none(),
        TypX::TypeId => panic!("internal error: TypeId created too soon"),
        TypX::ConstInt(_) => panic!("internal error: expression should not have ConstInt type"),
        TypX::ConstBool(_) => panic!("internal error: expression should not have ConstBool type"),
        TypX::Air(_) => panic!("internal error: Air type created too soon"),
        TypX::MutRef(_) => true,
        TypX::Opaque { .. } => true,
    }
}

/// Intended to be called on the pre-Poly SST
pub(crate) fn coerce_typ_to_native(ctx: &Ctx, typ: &Typ) -> Typ {
    match &**typ {
        TypX::Bool | TypX::Int(_) | TypX::Real | TypX::Float(_) => typ.clone(),
        TypX::SpecFn(..) | TypX::FnDef(..) => typ.clone(),
        TypX::Primitive(Primitive::Array, _) => typ.clone(),
        TypX::AnonymousClosure(..) => {
            panic!("internal error: AnonymousClosure should be removed by ast_simplify")
        }
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
        TypX::Dyn(..) => typ.clone(),
        TypX::Decorate(d, targ, t) => {
            Arc::new(TypX::Decorate(*d, targ.clone(), coerce_typ_to_native(ctx, t)))
        }
        TypX::Boxed(_) => panic!("Boxed unexpected here"),
        TypX::TypParam(_) | TypX::Projection { .. } | TypX::PointeeMetadata(_) => typ.clone(),
        TypX::Primitive(_, _) => {
            if typ_as_mono(typ).is_none() {
                Arc::new(TypX::Boxed(typ.clone()))
            } else {
                typ.clone()
            }
        }
        TypX::TypeId => panic!("internal error: TypeId created too soon"),
        TypX::ConstInt(_) => panic!("internal error: expression should not have ConstInt type"),
        TypX::ConstBool(_) => panic!("internal error: expression should not have ConstBool type"),
        TypX::Air(_) => panic!("internal error: Air type created too soon"),
        TypX::MutRef(_) => typ.clone(),
        TypX::Opaque { .. } => typ.clone(),
    }
}

pub(crate) fn coerce_typ_to_poly(_ctx: &Ctx, typ: &Typ) -> Typ {
    match &**typ {
        TypX::Bool | TypX::Int(_) => Arc::new(TypX::Boxed(typ.clone())),
        TypX::Real | TypX::Float(_) => Arc::new(TypX::Boxed(typ.clone())),
        TypX::SpecFn(..) | TypX::FnDef(..) => Arc::new(TypX::Boxed(typ.clone())),
        TypX::AnonymousClosure(..) => {
            panic!("internal error: AnonymousClosure should be removed by ast_simplify")
        }
        TypX::Datatype(..) | TypX::Primitive(_, _) => Arc::new(TypX::Boxed(typ.clone())),
        TypX::Dyn(..) => typ.clone(),
        TypX::Decorate(d, targ, t) => {
            Arc::new(TypX::Decorate(*d, targ.clone(), coerce_typ_to_poly(_ctx, t)))
        }
        TypX::Boxed(_) | TypX::TypParam(_) | TypX::Projection { .. } | TypX::PointeeMetadata(_) => {
            typ.clone()
        }
        TypX::TypeId => panic!("internal error: TypeId created too soon"),
        TypX::ConstInt(_) => typ.clone(),
        TypX::ConstBool(_) => typ.clone(),
        TypX::Air(_) => panic!("internal error: Air type created too soon"),
        TypX::MutRef(_) => typ.clone(),
        TypX::Opaque { .. } => typ.clone(),
    }
}

pub(crate) fn coerce_exp_to_native(ctx: &Ctx, exp: &Exp) -> Exp {
    match &*crate::ast_util::undecorate_typ(&exp.typ) {
        TypX::Bool
        | TypX::Int(_)
        | TypX::Real
        | TypX::Float(_)
        | TypX::SpecFn(..)
        | TypX::Datatype(..)
        | TypX::Dyn(..)
        | TypX::Primitive(_, _)
        | TypX::FnDef(..) => exp.clone(),
        TypX::AnonymousClosure(..) => {
            panic!("internal error: AnonymousClosure should be removed by ast_simplify")
        }
        TypX::Decorate(..) => {
            panic!("internal error: Decorate should be removed by undecorate_typ")
        }
        TypX::Boxed(typ) => {
            if typ_is_poly(ctx, typ) {
                exp.clone()
            } else {
                let op = UnaryOpr::Unbox(typ.clone());
                let expx = ExpX::UnaryOpr(op, exp.clone());
                SpannedTyped::new(&exp.span, typ, expx)
            }
        }
        TypX::TypParam(_)
        | TypX::Projection { .. }
        | TypX::PointeeMetadata(_)
        | TypX::MutRef(_) => exp.clone(),
        TypX::Opaque { .. } => exp.clone(),
        TypX::TypeId => panic!("internal error: TypeId created too soon"),
        TypX::ConstInt(_) => panic!("internal error: expression should not have ConstInt type"),
        TypX::ConstBool(_) => panic!("internal error: expression should not have ConstBool type"),
        TypX::Air(_) => panic!("internal error: Air type created too soon"),
    }
}

pub(crate) fn coerce_exp_to_poly(ctx: &Ctx, exp: &Exp) -> Exp {
    if typ_is_poly(ctx, &exp.typ) {
        exp.clone()
    } else {
        let op = UnaryOpr::Box(exp.typ.clone());
        let expx = ExpX::UnaryOpr(op, exp.clone());
        let typ = Arc::new(TypX::Boxed(exp.typ.clone()));
        SpannedTyped::new(&exp.span, &typ, expx)
    }
}

fn coerce_exps_to_agree(ctx: &Ctx, exp1: &Exp, exp2: &Exp) -> (Exp, Exp) {
    if typ_is_poly(ctx, &exp1.typ) && typ_is_poly(ctx, &exp2.typ) {
        (exp1.clone(), exp2.clone())
    } else {
        (coerce_exp_to_native(ctx, exp1), coerce_exp_to_native(ctx, exp2))
    }
}

// Rewrite VarBinders and insert into types into the ScopeMap's current scope.
// (The caller must make sure that the ScopeMap has a pushed scope,
// and the caller is responsible for eventually popping the scope.)
fn visit_and_insert_binders(
    ctx: &Ctx,
    types: &mut ScopeMap<VarIdent, Typ>,
    natives: &HashSet<VarIdent>,
    bs: &VarBinders<Typ>,
) -> VarBinders<Typ> {
    let mut new_bs: Vec<VarBinder<Typ>> = Vec::new();
    for b in bs.iter() {
        let typ = match &*b.a {
            TypX::TypeId => b.a.clone(),
            _ if natives.contains(&b.name) => coerce_typ_to_native(ctx, &b.a),
            _ => coerce_typ_to_poly(ctx, &b.a),
        };
        let _ = types.insert(b.name.clone(), typ.clone());
        let bx = VarBinderX { name: b.name.clone(), a: typ };
        new_bs.push(Arc::new(bx));
    }
    Arc::new(new_bs)
}

enum InsertPars {
    Native,
    Poly,
    NativeFor(HashSet<VarIdent>),
}

// Rewrite Pars and insert into types into the ScopeMap's current scope.
// (The caller must make sure that the ScopeMap has a pushed scope,
// and the caller is responsible for eventually popping the scope.)
fn visit_and_insert_pars(
    ctx: &Ctx,
    types: &mut ScopeMap<VarIdent, Typ>,
    poly: &InsertPars,
    pars: &Pars,
) -> Pars {
    // Parameter types are made Poly for spec functions and trait methods
    let mut new_pars: Vec<Par> = Vec::new();
    for par in pars.iter() {
        let ParX { name, typ, mode, is_mut, purpose } = &par.x;
        let is_poly = match poly {
            InsertPars::Native => false,
            InsertPars::Poly => true,
            InsertPars::NativeFor(natives) => !natives.contains(name),
        };
        let typ =
            if is_poly { coerce_typ_to_poly(ctx, typ) } else { coerce_typ_to_native(ctx, typ) };
        let _ = types.insert(name.clone(), typ.clone());
        let parx =
            ParX { name: name.clone(), typ, mode: *mode, is_mut: *is_mut, purpose: *purpose };
        new_pars.push(Spanned::new(par.span.clone(), parx));
    }
    Arc::new(new_pars)
}

fn return_typ(ctx: &Ctx, function: &FunctionSstX, is_trait: bool, typ: &Typ) -> Typ {
    if (is_trait || typ_is_poly(ctx, &function.ret.x.typ))
        && (function.ens_has_return || function.mode == Mode::Spec)
    {
        coerce_typ_to_poly(ctx, typ)
    } else {
        coerce_typ_to_native(ctx, typ)
    }
}

pub(crate) fn ret_needs_native(
    ctx: &Ctx,
    kind: &FunctionKind,
    ret_typ: &Typ,
    dest_typ: &Typ,
) -> bool {
    let is_trait = !matches!(kind, FunctionKind::Static);
    let ret_typ = if is_trait {
        coerce_typ_to_poly(ctx, ret_typ)
    } else {
        coerce_typ_to_native(ctx, ret_typ)
    };
    let dest_typ = coerce_typ_to_native(ctx, dest_typ);
    typ_is_poly(ctx, &ret_typ) && !typ_is_poly(ctx, &dest_typ)
}

pub(crate) fn arg_is_poly(ctx: &Ctx, kind: &FunctionKind, mode: Mode, arg_typ: &Typ) -> bool {
    let is_spec = mode == Mode::Spec;
    let is_trait = !matches!(kind, FunctionKind::Static);
    is_spec || is_trait || typ_is_poly(ctx, arg_typ)
}

fn visit_exp(ctx: &Ctx, state: &mut State, exp: &Exp) -> Exp {
    let mk_exp = |e: ExpX| SpannedTyped::new(&exp.span, &exp.typ, e);
    let mk_exp_typ = |t: &Typ, e: ExpX| SpannedTyped::new(&exp.span, t, e);
    match &exp.x {
        ExpX::Const(_) => exp.clone(),
        ExpX::Var(x) => SpannedTyped::new(&exp.span, &state.types[x], ExpX::Var(x.clone())),
        ExpX::VarLoc(x) => SpannedTyped::new(&exp.span, &state.types[x], ExpX::VarLoc(x.clone())),
        ExpX::VarAt(x, at) => {
            SpannedTyped::new(&exp.span, &state.types[x], ExpX::VarAt(x.clone(), *at))
        }
        ExpX::StaticVar(_) => exp.clone(),
        ExpX::Loc(e) => {
            let exp = visit_exp(ctx, state, e);
            mk_exp_typ(&exp.clone().typ, ExpX::Loc(exp))
        }
        ExpX::Old(..) => panic!("internal error: unexpected ExpX::Old"),
        ExpX::Call(call_fun, typs, exps) => match call_fun {
            CallFun::Fun(name, _) | CallFun::Recursive(name) => {
                let function = &ctx.func_sst_map[name].x;
                let is_spec = function.mode == Mode::Spec;
                let is_trait = !matches!(function.kind, FunctionKind::Static);
                let mut args: Vec<Exp> = Vec::new();
                for (par, arg) in function.pars.iter().zip(exps.iter()) {
                    let arg = if is_spec || is_trait || typ_is_poly(ctx, &par.x.typ) {
                        visit_exp_poly(ctx, state, arg)
                    } else {
                        visit_exp_native(ctx, state, arg)
                    };
                    args.push(arg);
                }
                match call_fun {
                    CallFun::Fun(..) => {
                        assert!(exps.len() == function.pars.len());
                    }
                    CallFun::Recursive(_) => {
                        assert!(exps.len() == function.pars.len() + 1);
                        let last = exps.last().unwrap();
                        // The last argument is the fuel parameter
                        assert!(matches!(&last.x, ExpX::Var(_)));
                        args.push(last.clone());
                    }
                    _ => unreachable!(),
                };
                let typ = return_typ(ctx, function, is_trait, &exp.typ);
                mk_exp_typ(&typ, ExpX::Call(call_fun.clone(), typs.clone(), Arc::new(args)))
            }
            CallFun::InternalFun(InternalFun::OpenInvariantMask(name, _i)) => {
                let function = &ctx.func_sst_map[name].x;
                let is_spec = function.mode == Mode::Spec;
                let is_trait = !matches!(function.kind, FunctionKind::Static);
                let mut args: Vec<Exp> = Vec::new();
                for (par, arg) in function.pars.iter().zip(exps.iter()) {
                    let arg = if is_spec || is_trait || typ_is_poly(ctx, &par.x.typ) {
                        visit_exp_poly(ctx, state, arg)
                    } else {
                        visit_exp_native(ctx, state, arg)
                    };
                    args.push(arg);
                }
                mk_exp(ExpX::Call(call_fun.clone(), typs.clone(), Arc::new(args)))
            }
            CallFun::InternalFun(
                InternalFun::ClosureReq | InternalFun::ClosureEns | InternalFun::DefaultEns,
            ) => {
                let exps = visit_exps_poly(ctx, state, exps);
                mk_exp(ExpX::Call(call_fun.clone(), typs.clone(), exps))
            }
            CallFun::InternalFun(InternalFun::CheckDecreaseInt) => {
                assert!(exps.len() == 3);
                let e0 = visit_exp_native(ctx, state, &exps[0]);
                let e1 = visit_exp_native(ctx, state, &exps[1]);
                let e2 = visit_exp_native(ctx, state, &exps[2]);
                mk_exp(ExpX::Call(call_fun.clone(), typs.clone(), Arc::new(vec![e0, e1, e2])))
            }
            CallFun::InternalFun(InternalFun::CheckDecreaseHeight) => {
                assert!(exps.len() == 3);
                let e0 = visit_exp_poly(ctx, state, &exps[0]);
                let e1 = visit_exp_poly(ctx, state, &exps[1]);
                let e2 = visit_exp_native(ctx, state, &exps[2]);
                mk_exp(ExpX::Call(call_fun.clone(), typs.clone(), Arc::new(vec![e0, e1, e2])))
            }
        },
        ExpX::CallLambda(callee, args) => {
            let callee = visit_exp_native(ctx, state, callee);
            let args = visit_exps_poly(ctx, state, args);
            let typ = coerce_typ_to_poly(ctx, &exp.typ);
            mk_exp_typ(&typ, ExpX::CallLambda(callee, args))
        }
        ExpX::Ctor(path, variant, binders) => {
            let fields = &ctx.datatype_map[path].x.get_variant(variant).fields;
            let mut bs: Vec<Binder<Exp>> = Vec::new();
            for binder in binders.iter() {
                let field = crate::ast_util::get_field(fields, &binder.name);
                let e = if typ_is_poly(ctx, &field.a.0) {
                    visit_exp_poly(ctx, state, &binder.a)
                } else {
                    // Force an expression of the form unbox(...) to match triggers with unbox:
                    let e = visit_exp_poly(ctx, state, &binder.a);
                    coerce_exp_to_native(ctx, &e)
                };
                bs.push(binder.new_a(e));
            }
            mk_exp(ExpX::Ctor(path.clone(), variant.clone(), Arc::new(bs)))
        }
        ExpX::NullaryOpr(NullaryOpr::ConstGeneric(_)) => exp.clone(),
        ExpX::NullaryOpr(NullaryOpr::TraitBound(..)) => exp.clone(),
        ExpX::NullaryOpr(NullaryOpr::TypEqualityBound(..)) => exp.clone(),
        ExpX::NullaryOpr(NullaryOpr::ConstTypBound(..)) => exp.clone(),
        ExpX::NullaryOpr(NullaryOpr::NoInferSpecForLoopIter) => exp.clone(),
        ExpX::Unary(op, e1) => {
            let e1 = visit_exp(ctx, state, e1);
            match op {
                UnaryOp::Not
                | UnaryOp::Clip { .. }
                | UnaryOp::FloatToBits
                | UnaryOp::IntToReal
                | UnaryOp::BitNot(_)
                | UnaryOp::StrLen
                | UnaryOp::StrIsAscii => {
                    let e1 = coerce_exp_to_native(ctx, &e1);
                    mk_exp(ExpX::Unary(*op, e1))
                }
                UnaryOp::InferSpecForLoopIter { .. } => {
                    // e1 will be the argument to spec Option::Some(...)
                    let e1 = coerce_exp_to_poly(ctx, &e1);
                    mk_exp(ExpX::Unary(*op, e1))
                }
                UnaryOp::HeightTrigger | UnaryOp::Length(_) => {
                    let e1 = coerce_exp_to_poly(ctx, &e1);
                    mk_exp(ExpX::Unary(*op, e1))
                }
                UnaryOp::ToDyn => {
                    let e1 = coerce_exp_to_poly(ctx, &e1);
                    mk_exp(ExpX::Unary(*op, e1))
                }
                UnaryOp::Trigger(_) | UnaryOp::CoerceMode { .. } => {
                    mk_exp_typ(&e1.typ, ExpX::Unary(*op, e1.clone()))
                }
                UnaryOp::MustBeFinalized | UnaryOp::MustBeElaborated => {
                    panic!("internal error: MustBeFinalized in SST")
                }
                UnaryOp::CastToInteger => {
                    let unbox = UnaryOpr::Unbox(Arc::new(TypX::Int(IntRange::Int)));
                    mk_exp(ExpX::UnaryOpr(unbox, e1.clone()))
                }
                UnaryOp::MutRefCurrent | UnaryOp::MutRefFuture(_) => {
                    let e1 = coerce_exp_to_native(ctx, &e1);
                    mk_exp_typ(&coerce_typ_to_poly(ctx, &exp.typ), ExpX::Unary(*op, e1.clone()))
                }
                UnaryOp::MutRefFinal => {
                    panic!("internal error: MustBeFinalized in SST")
                }
            }
        }
        ExpX::UnaryOpr(op, e1) => {
            let e1 = visit_exp(ctx, state, e1);
            match op {
                UnaryOpr::Box(_) | UnaryOpr::Unbox(_) => {
                    panic!("internal error: {:?} already has Box/Unbox", e1)
                }
                UnaryOpr::HasType(t) => {
                    // REVIEW: not clear that typ_to_poly is appropriate here for abstract datatypes
                    let (e1, t) = match (typ_is_poly(ctx, &e1.typ), typ_is_poly(ctx, t)) {
                        (false, true) => (coerce_exp_to_poly(ctx, &e1), t.clone()),
                        (true, _) => (e1.clone(), coerce_typ_to_poly(ctx, t)),
                        _ => (e1.clone(), t.clone()),
                    };
                    mk_exp(ExpX::UnaryOpr(UnaryOpr::HasType(t), e1))
                }
                UnaryOpr::IsVariant { .. } | UnaryOpr::IntegerTypeBound(..) => {
                    let e1 = coerce_exp_to_native(ctx, &e1);
                    mk_exp(ExpX::UnaryOpr(op.clone(), e1))
                }
                UnaryOpr::CustomErr(_) => {
                    mk_exp_typ(&e1.typ, ExpX::UnaryOpr(op.clone(), e1.clone()))
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
                    let e1 = coerce_exp_to_poly(ctx, &e1);
                    let e1 = coerce_exp_to_native(ctx, &e1);

                    let exprx = ExpX::UnaryOpr(op.clone(), e1);
                    let typ = if typ_is_poly(ctx, &field.a.0) {
                        coerce_typ_to_poly(ctx, &exp.typ)
                    } else {
                        coerce_typ_to_native(ctx, &exp.typ)
                    };
                    mk_exp_typ(&typ, exprx)
                }
                UnaryOpr::HasResolved(_t) => {
                    let e = coerce_exp_to_poly(ctx, &e1);
                    mk_exp(ExpX::UnaryOpr(op.clone(), e.clone()))
                }
            }
        }
        ExpX::Binary(BinaryOp::Index(kind, bc), e1, e2) => {
            let e1 = visit_exp(ctx, state, e1);
            let e2 = visit_exp(ctx, state, e2);
            let e1 = coerce_exp_to_native(ctx, &e1);
            let e2 = coerce_exp_to_poly(ctx, &e2);
            let typ = coerce_typ_to_poly(ctx, &exp.typ);
            mk_exp_typ(&typ, ExpX::Binary(BinaryOp::Index(*kind, *bc), e1, e2))
        }
        ExpX::Binary(op, e1, e2) => {
            let e1 = visit_exp(ctx, state, e1);
            let e2 = visit_exp(ctx, state, e2);
            let (native, poly) = match op {
                BinaryOp::And | BinaryOp::Or | BinaryOp::Xor => (true, false),
                BinaryOp::Implies | BinaryOp::Inequality(_) => (true, false),
                BinaryOp::HeightCompare { .. } => (false, true),
                BinaryOp::Arith(..) => (true, false),
                BinaryOp::RealArith(..) => (true, false),
                BinaryOp::Eq(_) | BinaryOp::Ne => (false, false),
                BinaryOp::Bitwise(..) => (true, false),
                BinaryOp::StrGetChar { .. } => (true, false),
                BinaryOp::Index(..) => unreachable!("Index"),
            };
            if native {
                let e1 = coerce_exp_to_native(ctx, &e1);
                let e2 = coerce_exp_to_native(ctx, &e2);
                mk_exp(ExpX::Binary(*op, e1, e2))
            } else if poly {
                let e1 = coerce_exp_to_poly(ctx, &e1);
                let e2 = coerce_exp_to_poly(ctx, &e2);
                mk_exp(ExpX::Binary(*op, e1, e2))
            } else {
                let (e1, e2) = coerce_exps_to_agree(ctx, &e1, &e2);
                mk_exp(ExpX::Binary(*op, e1, e2))
            }
        }
        ExpX::BinaryOpr(op @ crate::ast::BinaryOpr::ExtEq(..), e1, e2) => {
            let e1 = visit_exp_poly(ctx, state, e1);
            let e2 = visit_exp_poly(ctx, state, e2);
            mk_exp(ExpX::BinaryOpr(op.clone(), e1, e2))
        }
        ExpX::If(e0, e1, e2) => {
            let e0 = visit_exp_native(ctx, state, e0);
            let e1 = visit_exp(ctx, state, e1);
            let e2 = visit_exp(ctx, state, e2);
            let (e1, e2) = coerce_exps_to_agree(ctx, &e1, &e2);
            let t = if typ_is_poly(ctx, &e1.typ) {
                coerce_typ_to_poly(ctx, &exp.typ)
            } else {
                coerce_typ_to_native(ctx, &exp.typ)
            };
            mk_exp_typ(&t, ExpX::If(e0, e1, e2))
        }
        ExpX::WithTriggers(trigs, body) => {
            let trigs = visit_trigs(ctx, state, trigs);
            let body = visit_exp(ctx, state, body);
            mk_exp_typ(&body.clone().typ, ExpX::WithTriggers(trigs, body))
        }
        ExpX::Bind(bnd, e1) => match &bnd.x {
            BndX::Let(bs) => {
                state.types.push_scope(true);
                let mut new_bs: Vec<VarBinder<Exp>> = Vec::new();
                for b in bs.iter() {
                    // TODO: this might be better as just visit_exp:
                    let a = visit_exp_native(ctx, state, &b.a);
                    let _ = state.types.insert(b.name.clone(), a.typ.clone());
                    let bx = VarBinderX { name: b.name.clone(), a };
                    new_bs.push(Arc::new(bx));
                }
                let e1 = visit_exp(ctx, state, e1);
                state.types.pop_scope();
                mk_exp_typ(&e1.typ, ExpX::Bind(bnd.new_x(BndX::Let(Arc::new(new_bs))), e1.clone()))
            }
            BndX::Quant(quant, bs, trigs, _) => {
                let natives = native_quant_vars(bs, trigs);
                state.types.push_scope(true);
                let bs = visit_and_insert_binders(ctx, &mut state.types, &natives, bs);
                let trigs = visit_trigs(ctx, state, trigs);
                let e1 = visit_exp_native(ctx, state, e1);
                state.types.pop_scope();
                mk_exp(ExpX::Bind(bnd.new_x(BndX::Quant(*quant, bs, trigs, None)), e1))
            }
            BndX::Lambda(bs, trigs) => {
                let natives = native_quant_vars(bs, trigs);
                state.types.push_scope(true);
                let bs = visit_and_insert_binders(ctx, &mut state.types, &natives, bs);
                let trigs = visit_trigs(ctx, state, trigs);
                let e1 = visit_exp_poly(ctx, state, e1);
                state.types.pop_scope();
                mk_exp(ExpX::Bind(bnd.new_x(BndX::Lambda(bs, trigs)), e1))
            }
            BndX::Choose(bs, trigs, e2) => {
                let natives = native_quant_vars(bs, trigs);
                state.types.push_scope(true);
                let bs = visit_and_insert_binders(ctx, &mut state.types, &natives, bs);
                let trigs = visit_trigs(ctx, state, trigs);
                let e1 = visit_exp_poly(ctx, state, e1);
                let e2 = visit_exp_native(ctx, state, e2);
                state.types.pop_scope();
                mk_exp_typ(&e1.clone().typ, ExpX::Bind(bnd.new_x(BndX::Choose(bs, trigs, e2)), e1))
            }
        },
        ExpX::ExecFnByName(_) => exp.clone(),
        ExpX::ArrayLiteral(es) => {
            let es = visit_exps_poly(ctx, state, es);
            let typ = coerce_typ_to_poly(ctx, &exp.typ);
            mk_exp_typ(&typ, ExpX::ArrayLiteral(es))
        }
        ExpX::Interp(_) => panic!("unexpected ExpX::Interp"),
        ExpX::FuelConst(_) => exp.clone(),
    }
}

fn visit_exps(ctx: &Ctx, state: &mut State, exps: &Exps) -> Exps {
    Arc::new(exps.iter().map(|e| visit_exp(ctx, state, e)).collect())
}

fn visit_exp_native(ctx: &Ctx, state: &mut State, exp: &Exp) -> Exp {
    coerce_exp_to_native(ctx, &visit_exp(ctx, state, exp))
}

fn visit_exp_poly(ctx: &Ctx, state: &mut State, exp: &Exp) -> Exp {
    coerce_exp_to_poly(ctx, &visit_exp(ctx, state, exp))
}

fn visit_exps_native(ctx: &Ctx, state: &mut State, exps: &Exps) -> Exps {
    Arc::new(exps.iter().map(|e| visit_exp_native(ctx, state, e)).collect())
}

fn visit_exps_poly(ctx: &Ctx, state: &mut State, exps: &Exps) -> Exps {
    Arc::new(exps.iter().map(|e| visit_exp_poly(ctx, state, e)).collect())
}

fn visit_trigs(ctx: &Ctx, state: &mut State, trigs: &Trigs) -> Trigs {
    Arc::new(trigs.iter().map(|e| visit_exps(ctx, state, e)).collect())
}

pub(crate) fn visit_exp_native_for_pure_exp(ctx: &Ctx, exp: &Exp) -> Exp {
    let mut state = State {
        remaining_temps: HashSet::new(),
        types: ScopeMap::new(),
        temp_types: HashMap::new(),
        is_trait: false,
        in_exec_closure: false,
        is_ret_opaque: false,
    };
    visit_exp_native(ctx, &mut state, exp)
}

fn take_temp(state: &mut State, dest: &Dest) -> Option<VarIdent> {
    if dest.is_init {
        if let ExpX::VarLoc(x) = &dest.dest.x {
            if state.remaining_temps.contains(x) {
                state.remaining_temps.remove(x);
                return Some(x.clone());
            }
        }
    }
    None
}

fn visit_stm(ctx: &Ctx, state: &mut State, stm: &Stm) -> Stm {
    let mk_stm = |s: StmX| Spanned::new(stm.span.clone(), s);
    match &stm.x {
        StmX::Call {
            fun,
            resolved_method,
            is_trait_default,
            mode,
            typ_args,
            args,
            split,
            dest,
            assert_id,
        } => {
            let function = &ctx.func_sst_map[fun].x;
            let is_spec = function.mode == Mode::Spec;
            let is_trait = !matches!(function.kind, FunctionKind::Static);
            let mut new_args: Vec<Exp> = Vec::new();
            assert!(function.pars.len() == args.len());
            for (par, arg) in function.pars.iter().zip(args.iter()) {
                let arg = if is_spec || is_trait || typ_is_poly(ctx, &par.x.typ) {
                    visit_exp_poly(ctx, state, arg)
                } else {
                    visit_exp_native(ctx, state, arg)
                };
                new_args.push(arg);
            }
            let dest = if let Some(dest) = dest {
                if let Some(x) = take_temp(state, dest) {
                    let typ = return_typ(ctx, function, is_trait, &dest.dest.typ);
                    assert!(!state.temp_types.contains_key(&x));
                    assert!(!state.types.contains_key(&x));
                    let _ = state.temp_types.insert(x.clone(), typ.clone());
                    let _ = state.types.insert(x, typ);
                }
                let dst = visit_exp(ctx, state, &dest.dest);
                Some(Dest { dest: dst, is_init: dest.is_init })
            } else {
                None
            };
            let callx = StmX::Call {
                fun: fun.clone(),
                resolved_method: resolved_method.clone(),
                is_trait_default: *is_trait_default,
                mode: *mode,
                typ_args: typ_args.clone(),
                args: Arc::new(new_args),
                split: split.clone(),
                dest,
                assert_id: assert_id.clone(),
            };
            mk_stm(callx)
        }
        StmX::Assert(id, msg, e1) => {
            let e1 = visit_exp_native(ctx, state, e1);
            mk_stm(StmX::Assert(id.clone(), msg.clone(), e1))
        }
        StmX::AssertBitVector { requires, ensures } => {
            let requires = visit_exps_native(ctx, state, requires);
            let ensures = visit_exps_native(ctx, state, ensures);
            mk_stm(StmX::AssertBitVector { requires, ensures })
        }
        StmX::AssertQuery { mode, typ_inv_exps, typ_inv_vars, body } => {
            let body = visit_stm(ctx, state, body);
            let typ_inv_exps = visit_exps(ctx, state, typ_inv_exps);
            let typ_inv_vars =
                typ_inv_vars.iter().map(|(x, _)| (x.clone(), state.types[x].clone())).collect();
            mk_stm(StmX::AssertQuery {
                mode: *mode,
                typ_inv_exps,
                typ_inv_vars: Arc::new(typ_inv_vars),
                body,
            })
        }
        StmX::AssertCompute(..) => panic!("AssertCompute should be removed by sst_elaborate"),
        StmX::Assume(e1) => {
            let e1 = visit_exp_native(ctx, state, e1);
            mk_stm(StmX::Assume(e1))
        }
        StmX::Assign { lhs, rhs } => {
            let (e1, rhs) = if let Some(x) = take_temp(state, lhs) {
                let rhs = visit_exp(ctx, state, rhs);
                // x needs to be in types before we can visit e1:
                assert!(!state.temp_types.contains_key(&x));
                assert!(!state.types.contains_key(&x));
                let _ = state.temp_types.insert(x.clone(), rhs.typ.clone());
                let _ = state.types.insert(x, rhs.typ.clone());
                let e1 = visit_exp(ctx, state, &lhs.dest);
                (e1, rhs)
            } else {
                let e1 = visit_exp(ctx, state, &lhs.dest);
                let rhs = if typ_is_poly(ctx, &e1.typ) {
                    visit_exp_poly(ctx, state, rhs)
                } else {
                    visit_exp_native(ctx, state, rhs)
                };
                (e1, rhs)
            };
            let lhs = Dest { dest: e1, is_init: lhs.is_init };
            mk_stm(StmX::Assign { lhs, rhs })
        }
        StmX::Fuel(_, _) => stm.clone(),
        StmX::RevealString(_) => stm.clone(),
        StmX::DeadEnd(stm) => {
            let stm = visit_stm(ctx, state, stm);
            mk_stm(StmX::DeadEnd(stm))
        }
        StmX::Return { assert_id, base_error, ret_exp, inside_body } => {
            let ret_exp = if let Some(e1) = ret_exp {
                let e1 = if state.is_trait && !state.in_exec_closure {
                    visit_exp_poly(ctx, state, e1)
                } else {
                    visit_exp_native(ctx, state, e1)
                };

                // opaque type has to be poly
                if state.is_ret_opaque {
                    Some(crate::poly::coerce_exp_to_poly(ctx, &e1))
                } else {
                    Some(e1)
                }
            } else {
                None
            };

            mk_stm(StmX::Return {
                assert_id: assert_id.clone(),
                base_error: base_error.clone(),
                ret_exp,
                inside_body: *inside_body,
            })
        }
        StmX::BreakOrContinue { .. } => stm.clone(),
        StmX::If(e, s1, s2) => {
            let e = visit_exp_native(ctx, state, e);
            let s1 = visit_stm(ctx, state, s1);
            let s2 = s2.as_ref().map(|s| visit_stm(ctx, state, s));
            mk_stm(StmX::If(e, s1, s2))
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
            let cond = cond
                .as_ref()
                .map(|(s, e)| (visit_stm(ctx, state, s), visit_exp_native(ctx, state, e)));
            let body = visit_stm(ctx, state, body);
            let invs = invs.iter().map(|inv| crate::sst::LoopInv {
                inv: visit_exp_native(ctx, state, &inv.inv),
                ..inv.clone()
            });
            let invs = Arc::new(invs.collect());
            let decrease = visit_exps_native(ctx, state, decrease);
            mk_stm(StmX::Loop {
                loop_isolation: *loop_isolation,
                is_for_loop: *is_for_loop,
                id: *id,
                label: label.clone(),
                cond,
                body,
                invs,
                decrease,
                typ_inv_vars: typ_inv_vars.clone(),
                modified_vars: modified_vars.clone(),
            })
        }
        StmX::OpenInvariant(s) => {
            let s = visit_stm(ctx, state, s);
            mk_stm(StmX::OpenInvariant(s))
        }
        StmX::ClosureInner { body, typ_inv_vars } => {
            let typ_inv_vars = Arc::new(
                typ_inv_vars
                    .iter()
                    .map(|(uid, typ)| (uid.clone(), coerce_typ_to_native(ctx, typ)))
                    .collect::<Vec<_>>(),
            );

            state.types.push_scope(true);
            for (name, typ) in typ_inv_vars.iter() {
                let _ = state.types.insert(name.clone(), typ.clone());
            }
            let body = visit_stm(ctx, state, body);
            state.types.pop_scope();
            mk_stm(StmX::ClosureInner { body, typ_inv_vars: typ_inv_vars })
        }
        StmX::Air(_) => stm.clone(),
        StmX::Block(stms) => mk_stm(StmX::Block(visit_stms(ctx, state, stms))),
    }
}

fn visit_stms(ctx: &Ctx, state: &mut State, stms: &Stms) -> Stms {
    let mut ss: Vec<Stm> = Vec::new();
    for s in stms.iter() {
        ss.push(visit_stm(ctx, state, s));
    }
    Arc::new(ss)
}

fn visit_func_decl_sst(
    ctx: &Ctx,
    state: &mut State,
    poly_pars: &InsertPars,
    function: &FuncDeclSst,
) -> FuncDeclSst {
    let FuncDeclSst {
        req_inv_pars,
        ens_pars,
        reqs,
        enss: (enss0, enss1),
        inv_masks,
        unwind_condition,
        fndef_axioms,
    } = function;

    state.types.push_scope(true);
    let req_inv_pars = visit_and_insert_pars(ctx, &mut state.types, poly_pars, req_inv_pars);
    let reqs = visit_exps_native(ctx, state, reqs);
    let inv_masks =
        Arc::new(inv_masks.iter().map(|es| visit_exps_native(ctx, state, es)).collect());
    let unwind_condition = unwind_condition.as_ref().map(|e| visit_exp_native(ctx, state, e));
    state.types.pop_scope();

    state.types.push_scope(true);
    let ens_pars = visit_and_insert_pars(ctx, &mut state.types, poly_pars, ens_pars);
    let enss0 = visit_exps_native(ctx, state, enss0);
    let enss1 = visit_exps_native(ctx, state, enss1);
    state.types.pop_scope();

    let fndef_axioms = visit_exps_native(ctx, state, fndef_axioms);
    FuncDeclSst {
        req_inv_pars,
        ens_pars,
        reqs,
        enss: (enss0, enss1),
        inv_masks,
        unwind_condition,
        fndef_axioms,
    }
}

fn update_temp_locals(
    state: &mut State,
    locals: &mut Vec<LocalDecl>,
    updated_temps: &mut HashSet<VarIdent>,
) {
    for l in locals.iter_mut() {
        if matches!(l.kind, LocalDeclKind::TempViaAssign) {
            if !state.remaining_temps.contains(&l.ident) && !updated_temps.contains(&l.ident) {
                let typ = state.temp_types[&l.ident].clone();
                Arc::make_mut(l).typ = typ;
                updated_temps.insert(l.ident.clone());
            }
        }
    }
}

fn visit_func_check_sst(
    ctx: &Ctx,
    state: &mut State,
    function: &FuncCheckSst,
    poly_pars: &InsertPars,
    poly_ret: &InsertPars,
    ret_typ: &Typ,
) -> FuncCheckSst {
    let FuncCheckSst {
        reqs,
        post_condition,
        unwind,
        body,
        local_decls,
        local_decls_decreases_init,
        statics,
    } = function;

    state.temp_types.clear();

    let reqs = visit_exps_native(ctx, state, reqs);

    let unwind = match &unwind {
        UnwindSst::MayUnwind | UnwindSst::NoUnwind => unwind.clone(),
        UnwindSst::NoUnwindWhen(e) => {
            let e = visit_exp_native(ctx, state, e);
            UnwindSst::NoUnwindWhen(e)
        }
    };

    state.types.push_scope(true);
    let mut locals: Vec<LocalDecl> = Vec::new();
    for l in local_decls.iter() {
        let typ = match (l.kind, poly_pars, poly_ret) {
            (_, InsertPars::NativeFor(..), _) => panic!("unexpected NativeFor"),
            (_, _, InsertPars::NativeFor(..)) => panic!("unexpected NativeFor"),
            (LocalDeclKind::Param { .. }, InsertPars::Poly, _)
            | (LocalDeclKind::Return, _, InsertPars::Poly)
            | (LocalDeclKind::StmCallArg { native: false }, _, _)
            | (LocalDeclKind::AssertByVar { native: false }, _, _)
            | (LocalDeclKind::QuantBinder, _, _)
            | (LocalDeclKind::ChooseBinder, _, _)
            | (LocalDeclKind::ClosureBinder, _, _) => coerce_typ_to_poly(ctx, &l.typ),
            (LocalDeclKind::Param { .. }, InsertPars::Native, _)
            | (LocalDeclKind::Return, _, InsertPars::Native)
            | (LocalDeclKind::StmtLet { .. }, _, _)
            | (LocalDeclKind::StmCallArg { native: true }, _, _)
            | (LocalDeclKind::Assert, _, _)
            | (LocalDeclKind::AssertByVar { native: true }, _, _)
            | (LocalDeclKind::LetBinder, _, _)
            | (LocalDeclKind::OpenInvariantBinder, _, _)
            | (LocalDeclKind::ExecClosureId, _, _)
            | (LocalDeclKind::ExecClosureParam, _, _)
            | (LocalDeclKind::Nondeterministic, _, _)
            | (LocalDeclKind::BorrowMut, _, _)
            | (LocalDeclKind::ExecClosureRet, _, _)
            | (LocalDeclKind::Decreases, _, _)
            | (LocalDeclKind::MutableTemporary, _, _) => coerce_typ_to_native(ctx, &l.typ),
            (LocalDeclKind::TempViaAssign, _, _) => l.typ.clone(),
        };
        match l.kind {
            LocalDeclKind::TempViaAssign => {
                state.remaining_temps.insert(l.ident.clone());
            }
            _ => {
                let _ = state.types.insert(l.ident.clone(), typ.clone());
            }
        }
        let l = Arc::new(crate::sst::LocalDeclX { ident: l.ident.clone(), typ, kind: l.kind });
        locals.push(l);
    }

    let mut updated_temps: HashSet<VarIdent> = HashSet::new();

    state.types.push_scope(true);
    if let Some(ret) = &post_condition.dest {
        let _ = state.types.insert(ret.clone(), ret_typ.clone());
    }
    let post_condition = Arc::new(PostConditionSst {
        dest: post_condition.dest.clone(),
        ens_exps: visit_exps_native(ctx, state, &post_condition.ens_exps),
        ens_spec_precondition_stms: visit_stms(
            ctx,
            state,
            &post_condition.ens_spec_precondition_stms,
        ),
        kind: post_condition.kind,
    });
    state.types.pop_scope();

    let body = visit_stm(ctx, state, body);

    let local_decls_decreases_init = visit_stms(ctx, state, local_decls_decreases_init);

    update_temp_locals(state, &mut locals, &mut updated_temps);
    state.remaining_temps.clear();
    state.types.pop_scope();

    FuncCheckSst {
        reqs,
        post_condition,
        unwind,
        body,
        local_decls: Arc::new(locals),
        local_decls_decreases_init,
        statics: statics.clone(),
    }
}

fn visit_function(ctx: &Ctx, function: &FunctionSst) -> FunctionSst {
    let FunctionSstX {
        name,
        kind,
        body_visibility,
        opaqueness,
        owning_module,
        mode: mut function_mode,
        typ_params,
        typ_bounds,
        pars,
        ret,
        ens_has_return,
        item_kind,
        attrs,
        has,
        decl,
        axioms,
        exec_proof_check,
        recommends_check,
        safe_api_check,
    } = &function.x;

    if attrs.is_decrease_by {
        // This is actually code for a the spec function that has the decreases clause
        function_mode = Mode::Spec;
    }

    let types = ScopeMap::new();
    let is_trait = !matches!(kind, FunctionKind::Static);
    let poly_pars =
        if function_mode == Mode::Spec || is_trait { InsertPars::Poly } else { InsertPars::Native };
    let poly_ret = if is_trait && (*ens_has_return || function_mode == Mode::Spec) {
        InsertPars::Poly
    } else {
        InsertPars::Native
    };
    let mut state = State {
        types,
        temp_types: HashMap::new(),
        is_trait,
        in_exec_closure: false,
        remaining_temps: HashSet::new(),
        is_ret_opaque: matches!(*ret.x.typ, TypX::Opaque { .. }),
    };

    let decl = Arc::new(visit_func_decl_sst(ctx, &mut state, &poly_pars, decl));

    let proof_exec_axioms = if let Some((pars, body, trigs)) = &axioms.proof_exec_axioms {
        let mut bs: Vec<VarBinder<Typ>> = Vec::new();
        for par in pars.iter() {
            let ParX { name, typ, .. } = &par.x;
            bs.push(Arc::new(crate::ast::VarBinderX { name: name.clone(), a: typ.clone() }));
        }
        let natives = native_quant_vars(&Arc::new(bs), trigs);
        state.types.push_scope(true);
        let pars =
            visit_and_insert_pars(ctx, &mut state.types, &InsertPars::NativeFor(natives), pars);
        let body = visit_exp_native(ctx, &mut state, body);
        let trigs = visit_trigs(ctx, &mut state, trigs);
        state.types.pop_scope();
        Some((pars, body, trigs))
    } else {
        None
    };

    // Return type is left native (except for trait methods)
    let ret_typ = match poly_ret {
        InsertPars::Poly => coerce_typ_to_poly(ctx, &ret.x.typ),
        InsertPars::Native => coerce_typ_to_native(ctx, &ret.x.typ),
        _ => unreachable!(),
    };
    let ret = Spanned::new(ret.span.clone(), ParX { typ: ret_typ, ..ret.x.clone() });

    state.types.push_scope(true);
    let pars = visit_and_insert_pars(ctx, &mut state.types, &poly_pars, pars);

    let spec_axioms = if let Some(spec_body) = &axioms.spec_axioms {
        let decrease_when =
            spec_body.decrease_when.as_ref().map(|e| visit_exp_native(ctx, &mut state, e));
        let termination_check = spec_body
            .termination_check
            .as_ref()
            .map(|f| visit_func_check_sst(ctx, &mut state, f, &poly_pars, &poly_ret, &ret.x.typ));
        let body_exp = if is_trait && (function.x.ens_has_return || function_mode == Mode::Spec) {
            visit_exp_poly(ctx, &mut state, &spec_body.body_exp)
        } else {
            visit_exp_native(ctx, &mut state, &spec_body.body_exp)
        };
        let spec_body = crate::sst::FuncSpecBodySst { decrease_when, termination_check, body_exp };
        Some(spec_body)
    } else {
        None
    };
    let axioms = Arc::new(crate::sst::FuncAxiomsSst { spec_axioms, proof_exec_axioms });

    let exec_proof_check = exec_proof_check.as_ref().map(|f| {
        Arc::new(visit_func_check_sst(ctx, &mut state, f, &poly_pars, &poly_ret, &ret.x.typ))
    });
    let recommends_check = recommends_check.as_ref().map(|f| {
        Arc::new(visit_func_check_sst(ctx, &mut state, f, &poly_pars, &poly_ret, &ret.x.typ))
    });
    let safe_api_check = safe_api_check.as_ref().map(|f| {
        Arc::new(visit_func_check_sst(ctx, &mut state, f, &poly_pars, &poly_ret, &ret.x.typ))
    });

    state.types.pop_scope();
    assert_eq!(state.types.num_scopes(), 0);

    let functionx = FunctionSstX {
        name: name.clone(),
        kind: kind.clone(),
        body_visibility: body_visibility.clone(),
        opaqueness: opaqueness.clone(),
        owning_module: owning_module.clone(),
        mode: function_mode,
        typ_params: typ_params.clone(),
        typ_bounds: typ_bounds.clone(),
        pars,
        ret,
        ens_has_return: *ens_has_return,
        item_kind: *item_kind,
        attrs: attrs.clone(),
        has: has.clone(),
        decl,
        axioms,
        exec_proof_check,
        recommends_check,
        safe_api_check,
    };
    Spanned::new(function.span.clone(), functionx)
}

fn visit_datatype(ctx: &Ctx, datatype: &Datatype) -> Datatype {
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

fn visit_assoc_type_impl(ctx: &Ctx, assoc: &AssocTypeImpl) -> AssocTypeImpl {
    crate::ast_visitor::map_assoc_type_impl_visitor_env(assoc, &mut (), &|(), t| {
        Ok(coerce_typ_to_poly(ctx, t))
    })
    .expect("visit_assoc_type_impl")
}

pub fn poly_krate_for_module(ctx: &mut Ctx, krate: &KrateSst) -> KrateSst {
    let KrateSstX {
        functions,
        datatypes,
        opaque_types,
        traits,
        trait_impls,
        assoc_type_impls,
        reveal_groups,
    } = &**krate;
    let kratex = KrateSstX {
        functions: functions.iter().map(|f| visit_function(ctx, f)).collect(),
        datatypes: datatypes.iter().map(|d| visit_datatype(ctx, d)).collect(),
        opaque_types: opaque_types.clone(),
        traits: traits.clone(),
        trait_impls: trait_impls.clone(),
        assoc_type_impls: assoc_type_impls.iter().map(|a| visit_assoc_type_impl(ctx, a)).collect(),
        reveal_groups: reveal_groups.clone(),
    };
    ctx.func_sst_map = HashMap::new();
    for function in kratex.functions.iter() {
        ctx.func_sst_map.insert(function.x.name.clone(), function.clone());
    }
    ctx.datatype_map = HashMap::new();
    for datatype in kratex.datatypes.iter() {
        ctx.datatype_map.insert(datatype.x.name.clone(), datatype.clone());
    }
    Arc::new(kratex)
}
