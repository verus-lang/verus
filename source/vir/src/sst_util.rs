use crate::ast::{
    BinaryOpr, BitwiseOp, Constant, CrateId, CtorPrintStyle, Dt, Fun, GenericBound, GenericBoundX,
    GenericBounds, Ident, InequalityOp, IntRange, IntegerTypeBitwidth, IntegerTypeBoundKind,
    ProofNoteLabel, Quant, SpannedTyped, Typ, TypX, Typs, UnaryOp, UnaryOpr, VarAt, VarBinder,
    VarBinderX, VarBinders, VarIdent, VarIdentDisambiguate,
};
use crate::ast_util::{get_variant, undecorate_typ, unit_typ};
use crate::context::GlobalCtx;
use crate::def::{Spanned, user_local_name};
use crate::interpreter::InterpExp;
use crate::messages::Span;
use crate::sst::{
    ArithOp, BinaryOp, BndX, CallFun, Exp, ExpX, Exps, FuncCheckSst, FunctionSst, InternalFun,
    LocalDeclKind, Stm, StmX, UniqueIdent,
};
use crate::sst_visitor::{NoScoper, Visitor, VisitorScopeMap, Walk};
use std::collections::{HashMap, HashSet};
use std::sync::Arc;

fn free_vars_exp_scope(
    exp: &Exp,
    scope_map: &mut crate::sst_visitor::VisitorScopeMap,
    vars: &mut HashMap<UniqueIdent, Typ>,
    allow_unfinalized: bool,
) {
    crate::sst_visitor::exp_visitor_dfs::<(), _>(exp, scope_map, &mut |e, scope_map| {
        match &e.x {
            ExpX::Var(x) | ExpX::VarLoc(x) if !scope_map.contains_key(x) => {
                vars.insert(x.clone(), e.typ.clone());
            }
            ExpX::Unary(UnaryOp::MustBeFinalized, _) if !allow_unfinalized => {
                // Var won't match binders if we're not finalized
                // (special case allow_unfinalized = true for type-only substitution)
                panic!("MustBeFinalized")
            }
            _ => (),
        }
        crate::sst_visitor::VisitorControlFlow::Recurse
    });
}

pub(crate) fn free_vars_exp(exp: &Exp) -> HashMap<UniqueIdent, Typ> {
    let mut vars: HashMap<UniqueIdent, Typ> = HashMap::new();
    free_vars_exp_scope(exp, &mut crate::sst_visitor::VisitorScopeMap::new(), &mut vars, false);
    vars
}

pub(crate) fn free_vars_exps(exps: &[Exp]) -> HashMap<UniqueIdent, Typ> {
    let mut vars: HashMap<UniqueIdent, Typ> = HashMap::new();
    for exp in exps {
        free_vars_exp_scope(exp, &mut crate::sst_visitor::VisitorScopeMap::new(), &mut vars, false);
    }
    vars
}

pub(crate) fn subst_pre_local_decl(
    typ_substs: &HashMap<Ident, Typ>,
    pre_local_decl: &crate::ast_to_sst::PreLocalDecl,
) -> crate::ast_to_sst::PreLocalDecl {
    crate::ast_to_sst::PreLocalDecl {
        ident: pre_local_decl.ident.clone(),
        typ: subst_typ(typ_substs, &pre_local_decl.typ),
        kind: pre_local_decl.kind.clone(),
    }
}

pub fn free_vars_typ_insert(typ: &Typ, vars: &mut HashSet<Ident>) {
    let _ = crate::ast_visitor::typ_visitor_dfs(typ, &mut |t: &Typ| match &**t {
        TypX::TypParam(x) => {
            vars.insert(x.clone());
            crate::visitor::VisitorControlFlow::Recurse::<()>
        }
        _ => crate::visitor::VisitorControlFlow::Recurse::<()>,
    });
}

pub fn free_vars_typ(typ: &Typ) -> HashSet<Ident> {
    let mut vars: HashSet<Ident> = HashSet::new();
    free_vars_typ_insert(typ, &mut vars);
    vars
}

pub fn free_vars_typs(typs: &Typs) -> HashSet<Ident> {
    let mut vars: HashSet<Ident> = HashSet::new();
    for typ in typs.iter() {
        free_vars_typ_insert(typ, &mut vars);
    }
    vars
}

pub fn subst_typ(typ_substs: &HashMap<Ident, Typ>, typ: &Typ) -> Typ {
    crate::ast_visitor::map_typ_visitor(typ, &|t: &Typ| match &**t {
        TypX::TypParam(x) => match typ_substs.get(x) {
            Some(t) => Ok(t.clone()),
            None => Ok(t.clone()),
        },
        _ => Ok(t.clone()),
    })
    .expect("subst_typ")
}

pub fn subst_typ_in_bound(typ_substs: &HashMap<Ident, Typ>, bound: &GenericBound) -> GenericBound {
    let gbx = match &**bound {
        GenericBoundX::Trait(path, typs) => {
            let typs = typs.iter().map(|typ| subst_typ(&typ_substs, typ)).collect();
            GenericBoundX::Trait(path.clone(), Arc::new(typs))
        }
        GenericBoundX::TypEquality(path, typs, name, typ) => {
            let typs = typs.iter().map(|typ| subst_typ(&typ_substs, typ)).collect();
            let typ = subst_typ(&typ_substs, typ);
            GenericBoundX::TypEquality(path.clone(), Arc::new(typs), name.clone(), typ)
        }
        GenericBoundX::ConstTyp(t1, t2) => {
            let t1 = subst_typ(&typ_substs, t1);
            let t2 = subst_typ(&typ_substs, t2);
            GenericBoundX::ConstTyp(t1, t2)
        }
    };
    Arc::new(gbx)
}

pub fn subst_typ_in_bounds(
    typ_substs: &HashMap<Ident, Typ>,
    bounds: &GenericBounds,
) -> GenericBounds {
    Arc::new(bounds.iter().map(|bound| subst_typ_in_bound(typ_substs, bound)).collect())
}

pub fn subst_typ_for_datatype(
    typ_params: &crate::ast::TypPositives,
    args: &Typs,
    typ: &Typ,
) -> Typ {
    assert!(typ_params.len() == args.len());
    let mut typ_substs: HashMap<Ident, Typ> = HashMap::new();
    for (typ_param, arg) in typ_params.iter().zip(args.iter()) {
        typ_substs.insert(typ_param.0.clone(), arg.clone());
    }
    subst_typ(&typ_substs, typ)
}

/// Generates variable names that are guaranteed not to collide with any name
/// (free or bound) in the expressions passed to `avoid_names_in_exp`.
pub(crate) struct FreshNameGenerator {
    used: HashSet<VarIdent>,
    next: u64,
}

impl FreshNameGenerator {
    pub(crate) fn new() -> Self {
        FreshNameGenerator { used: HashSet::new(), next: 0 }
    }

    /// Record every variable name that is used or bound anywhere in `exp`
    pub(crate) fn avoid_names_in_exp(&mut self, exp: &Exp) {
        let used = &mut self.used;
        crate::sst_visitor::exp_visitor_dfs::<(), _>(
            exp,
            &mut crate::sst_visitor::VisitorScopeMap::new(),
            &mut |e, _| {
                match &e.x {
                    ExpX::Var(x) | ExpX::VarLoc(x) | ExpX::VarAt(x, _) | ExpX::Old(_, x) => {
                        used.insert(x.clone());
                    }
                    ExpX::Bind(bnd, _) => match &bnd.x {
                        BndX::Let(bs) => used.extend(bs.iter().map(|b| b.name.clone())),
                        BndX::Quant(_, bs, _, _) | BndX::Lambda(bs, _) | BndX::Choose(bs, _, _) => {
                            used.extend(bs.iter().map(|b| b.name.clone()))
                        }
                    },
                    ExpX::Const(..)
                    | ExpX::StaticVar(..)
                    | ExpX::Loc(..)
                    | ExpX::Call(..)
                    | ExpX::CallLambda(..)
                    | ExpX::Ctor(..)
                    | ExpX::NullaryOpr(..)
                    | ExpX::Unary(..)
                    | ExpX::UnaryOpr(..)
                    | ExpX::Binary(..)
                    | ExpX::BinaryOpr(..)
                    | ExpX::If(..)
                    | ExpX::WithTriggers(..)
                    | ExpX::ExecFnByName(..)
                    | ExpX::ArrayLiteral(..)
                    | ExpX::Interp(..)
                    | ExpX::FuelConst(..) => {}
                }
                crate::sst_visitor::VisitorControlFlow::Recurse
            },
        );
    }

    /// Return a name not recorded by avoid_names_in_exp and not returned by a previous get_fresh.
    /// The new name keeps the identifier part of x; the VirSubst disambiguator makes it fresh.
    pub(crate) fn get_fresh(&mut self, x: &VarIdent) -> VarIdent {
        loop {
            let n = self.next;
            self.next += 1;
            let y = VarIdent(x.0.clone(), VarIdentDisambiguate::VirSubst(n));
            if self.used.insert(y.clone()) {
                return y;
            }
        }
    }
}

/// Rename every binder in e1 whose name is in avoid_set to a fresh name
/// (and rename the corresponding bound occurrences).
/// Every binder named x (for x in avoid_set) is renamed to the same fresh name f(x).
/// Since f(x) occurs nowhere else, this preserves the binding structure of e1.
/// Free occurrences of x are left unchanged.
pub(crate) fn rebind_to_avoid(
    e1: &Exp,
    avoid_set: &HashSet<VarIdent>,
    names: &mut FreshNameGenerator,
) -> Exp {
    if avoid_set.is_empty() {
        return e1.clone();
    }
    struct Env<'a> {
        names: &'a mut FreshNameGenerator,
        renames: HashMap<VarIdent, VarIdent>,
    }
    impl<'a> Env<'a> {
        fn rename(&mut self, x: &VarIdent) -> VarIdent {
            let names = &mut self.names;
            self.renames.entry(x.clone()).or_insert_with(|| names.get_fresh(x)).clone()
        }
    }
    // Is x a bound occurrence of a variable that must be renamed?
    let must_rename = |x: &VarIdent, scope_map: &VisitorScopeMap| {
        avoid_set.contains(x) && scope_map.contains_key(x)
    };
    fn rename_binders<A: Clone>(
        bs: &VarBinders<A>,
        avoid_set: &HashSet<VarIdent>,
        env: &mut Env,
    ) -> VarBinders<A> {
        let rename = |b: &VarBinder<A>| {
            if avoid_set.contains(&b.name) {
                Arc::new(VarBinderX { name: env.rename(&b.name), a: b.a.clone() })
            } else {
                b.clone()
            }
        };
        Arc::new(bs.iter().map(rename).collect())
    }
    let mut fe = |e: &Exp, env: &mut Env, scope_map: &mut VisitorScopeMap| -> Result<Exp, ()> {
        let mk_exp = |x: ExpX| SpannedTyped::new(&e.span, &e.typ, x);
        match &e.x {
            ExpX::Var(x) if must_rename(x, scope_map) => Ok(mk_exp(ExpX::Var(env.rename(x)))),
            ExpX::VarLoc(x) if must_rename(x, scope_map) => {
                panic!("rebind_to_avoid: found VarLoc referring to bound variable")
            }
            ExpX::VarAt(x, a) if must_rename(x, scope_map) => {
                panic!("rebind_to_avoid: found VarAt referring to bound variable")
            }
            ExpX::Old(_, x) if must_rename(x, scope_map) => {
                panic!("rebind_to_avoid: found Old referring to bound variable")
            }
            ExpX::Bind(bnd, body) => {
                let bndx = match &bnd.x {
                    BndX::Let(bs) => BndX::Let(rename_binders(bs, avoid_set, env)),
                    BndX::Quant(quant, bs, ts, ab) => BndX::Quant(
                        *quant,
                        rename_binders(bs, avoid_set, env),
                        ts.clone(),
                        ab.clone(),
                    ),
                    BndX::Lambda(bs, ts) => {
                        BndX::Lambda(rename_binders(bs, avoid_set, env), ts.clone())
                    }
                    BndX::Choose(bs, ts, cond) => {
                        BndX::Choose(rename_binders(bs, avoid_set, env), ts.clone(), cond.clone())
                    }
                };
                let bnd = Spanned::new(bnd.span.clone(), bndx);
                Ok(mk_exp(ExpX::Bind(bnd, body.clone())))
            }
            ExpX::Interp(_) => {
                panic!("Found an interpreter expression {:?} outside the interpreter", e)
            }
            ExpX::Var(..)
            | ExpX::VarLoc(..)
            | ExpX::VarAt(..)
            | ExpX::Old(..)
            | ExpX::Const(..)
            | ExpX::StaticVar(..)
            | ExpX::Loc(..)
            | ExpX::Call(..)
            | ExpX::CallLambda(..)
            | ExpX::Ctor(..)
            | ExpX::NullaryOpr(..)
            | ExpX::Unary(..)
            | ExpX::UnaryOpr(..)
            | ExpX::Binary(..)
            | ExpX::BinaryOpr(..)
            | ExpX::If(..)
            | ExpX::WithTriggers(..)
            | ExpX::ExecFnByName(..)
            | ExpX::ArrayLiteral(..)
            | ExpX::FuelConst(..) => Ok(e.clone()),
        }
    };
    let mut ft =
        |t: &Typ, _: &mut Env, _: &mut VisitorScopeMap| -> Result<Typ, ()> { Ok(t.clone()) };
    let mut env = Env { names, renames: HashMap::new() };
    crate::sst_visitor::exp_typ_visitor_map(
        e1,
        &mut VisitorScopeMap::new(),
        &mut env,
        &mut fe,
        &mut ft,
    )
    .expect("rebind_to_avoid")
}

/// Substitution that does NOT avoid capture.
/// Callers must ensure that no binder in exp captures a free variable of substs.
/// (Variables shadowed by binders in exp are not substituted.)
fn subst_exp_no_capture_check(
    typ_substs: &HashMap<Ident, Typ>,
    substs: &HashMap<UniqueIdent, Exp>,
    allow_unfinalized: bool,
    exp: &Exp,
) -> Exp {
    // Returns the substitution for x, unless x is shadowed by an enclosing binder
    let get_subst = |x: &UniqueIdent, scope_map: &VisitorScopeMap| {
        if scope_map.contains_key(x) { None } else { substs.get(x) }
    };
    let mut fe = |e: &Exp, _: &mut (), scope_map: &mut VisitorScopeMap| -> Result<Exp, ()> {
        match &e.x {
            ExpX::Unary(UnaryOp::MustBeFinalized, _) if !allow_unfinalized => {
                // Var won't match binders if we're not finalized
                // (special case allow_unfinalized = true for type-only substitution)
                panic!("MustBeFinalized")
            }
            ExpX::Var(x) => match get_subst(x, scope_map) {
                Some(v) => Ok(v.clone()),
                None => Ok(e.clone()),
            },
            ExpX::VarLoc(x) => match get_subst(x, scope_map) {
                Some(_) => panic!("cannot substitute for VarLoc"),
                None => Ok(e.clone()),
            },
            ExpX::VarAt(x, _) => match get_subst(x, scope_map) {
                Some(_) => panic!("cannot substitute for VarAt"),
                None => Ok(e.clone()),
            },
            ExpX::Interp(_) => {
                panic!("Found an interpreter expression {:?} outside the interpreter", e)
            }
            ExpX::Const(..)
            | ExpX::StaticVar(..)
            | ExpX::Loc(..)
            | ExpX::Old(..)
            | ExpX::Call(..)
            | ExpX::CallLambda(..)
            | ExpX::Ctor(..)
            | ExpX::NullaryOpr(..)
            | ExpX::Unary(..)
            | ExpX::UnaryOpr(..)
            | ExpX::Binary(..)
            | ExpX::BinaryOpr(..)
            | ExpX::If(..)
            | ExpX::WithTriggers(..)
            | ExpX::Bind(..)
            | ExpX::ExecFnByName(..)
            | ExpX::ArrayLiteral(..)
            | ExpX::FuelConst(..) => Ok(e.clone()),
        }
    };
    // Children have already been mapped bottom-up, so only replace TypParam leaves
    let mut ft = |t: &Typ, _: &mut (), _: &mut VisitorScopeMap| -> Result<Typ, ()> {
        match &**t {
            TypX::TypParam(x) => match typ_substs.get(x) {
                Some(t2) => Ok(t2.clone()),
                None => Ok(t.clone()),
            },
            _ => Ok(t.clone()),
        }
    };
    crate::sst_visitor::exp_typ_visitor_map(
        exp,
        &mut VisitorScopeMap::new(),
        &mut (),
        &mut fe,
        &mut ft,
    )
    .expect("subst_exp_no_capture_check")
}

/// Capture-avoiding substitution of types and variables in exp
pub(crate) fn subst_exp(
    typ_substs: &HashMap<Ident, Typ>,
    substs: &HashMap<UniqueIdent, Exp>,
    exp: &Exp,
) -> Exp {
    if typ_substs.len() == 0 && substs.len() == 0 {
        return exp.clone();
    }
    let allow_unfinalized = substs.len() == 0;

    // Collect the free variables of the expressions being substituted
    let mut free_vars: HashSet<VarIdent> = HashSet::new();
    for e in substs.values() {
        free_vars.extend(free_vars_exp(e).into_keys());
    }

    // Rename any binders in exp that would capture one of these free variables
    let exp = if free_vars.is_empty() {
        exp.clone()
    } else {
        let mut names = FreshNameGenerator::new();
        names.avoid_names_in_exp(exp);
        for e in substs.values() {
            names.avoid_names_in_exp(e);
        }
        rebind_to_avoid(exp, &free_vars, &mut names)
    };

    subst_exp_no_capture_check(typ_substs, substs, allow_unfinalized, &exp)
}

pub(crate) fn subst_stm(
    typ_substs: &HashMap<Ident, Typ>,
    substs: &HashMap<UniqueIdent, Exp>,
    stm: &Stm,
) -> Stm {
    let stm = crate::sst_visitor::map_stm_visitor(&stm, &mut |stm| {
        crate::sst_visitor::map_shallow_stm_typ(&stm, &|typ| Ok(subst_typ(typ_substs, typ)))
    })
    .unwrap();
    crate::sst_visitor::map_stm_exp_visitor(&stm, &|exp| Ok(subst_exp(typ_substs, substs, exp)))
        .unwrap()
}

///////////////////////////////////////
// Printing for SST expressions
///////////////////////////////////////

impl BinaryOp {
    // Based on the "Expression precedence" table here:
    // https://doc.rust-lang.org/reference/expressions.html
    fn prec_of_binary_op(&self) -> (u32, u32, u32) {
        use ArithOp::*;
        use BinaryOp::*;
        use BitwiseOp::*;
        match &self {
            And => (8, 8, 9),
            Or => (6, 6, 7),
            Xor => (22, 22, 23), // Rust doesn't have a logical XOR, so this is consistent with BitXor
            Implies => (3, 4, 3),
            HeightCompare { .. } => (90, 5, 5),
            Eq | Ne => (10, 11, 11),
            Inequality(_) => (10, 10, 10),
            Arith(o) => match o {
                Add | Sub => (30, 30, 31),
                Mul | EuclideanDiv | EuclideanMod => (40, 40, 41),
            },
            RealArith(o) => match o {
                crate::ast::RealArithOp::Add | crate::ast::RealArithOp::Sub => (30, 30, 31),
                crate::ast::RealArithOp::Mul | crate::ast::RealArithOp::Div => (40, 40, 41),
            },
            Bitwise(o) => match o {
                BitXor => (22, 22, 23),
                BitAnd => (24, 24, 25),
                BitOr => (20, 20, 21),
                Shr | Shl(..) => (26, 26, 27),
            },
            IeeeFloat(_) => (5, 90, 90),
            StrGetChar => (90, 90, 90),
            Index(_) => (90, 90, 90),
        }
    }
}

fn prec_of_in() -> (u32, u32, u32) {
    (30, 30, 31)
}

impl ExpX {
    pub fn to_user_string(&self, global: &GlobalCtx) -> String {
        self.to_string_prec(global, 5)
    }

    fn to_string_prec(&self, global: &GlobalCtx, precedence: u32) -> String {
        use ExpX::*;
        let (s, inner_precedence) = match &self {
            Const(c) => match c {
                Constant::Bool(b) => (format!("{}", b), 99),
                Constant::Int(i) => (format!("{}", i), 99),
                Constant::Real(r) => (format!("{}", r), 99),
                Constant::StrSlice(s) => (format!("\"{}\"", s), 99),
                Constant::ByteStr(bytes) => {
                    let escaped = bytes
                        .iter()
                        .flat_map(|byte| std::ascii::escape_default(*byte))
                        .map(char::from)
                        .collect::<String>();
                    (format!("b\"{}\"", escaped), 99)
                }
                Constant::Char(c) => (format!("'{}'", c), 99),
                Constant::Float32(c) => (format!("'{}'", c), 99),
                Constant::Float64(c) => (format!("'{}'", c), 99),
            },
            Var(id) | VarLoc(id) => (format!("{}", user_local_name(id)), 99),
            VarAt(id, _at) => (format!("old({})", user_local_name(id)), 99),
            StaticVar(fun) => (format!("{}", fun.path.segments.last().unwrap()), 99),
            Loc(exp) => {
                return exp.x.to_string_prec(global, precedence);
            }
            Call(cf @ (CallFun::Fun(fun, _) | CallFun::Recursive(fun)), _, exps) => {
                let (zero_args, is_method) = match global.fun_attrs.get(fun) {
                    Some(attrs) => (attrs.print_zero_args, attrs.print_as_method),
                    None => (false, false),
                };

                let exps = if matches!(cf, CallFun::Recursive(..)) {
                    &exps[0..exps.len() - 1]
                } else {
                    &exps
                };

                let fun_name = fun.path.segments.last().unwrap();

                if is_method && exps.len() > 0 {
                    let receiver = exps[0].x.to_user_string(global);
                    let args = exps
                        .iter()
                        .skip(1)
                        .map(|e| e.x.to_user_string(global))
                        .collect::<Vec<_>>()
                        .join(", ");
                    (format!("{}.{}({})", receiver, fun_name, args), 90)
                } else {
                    let args = if zero_args {
                        "".to_string()
                    } else {
                        exps.iter()
                            .map(|e| e.x.to_user_string(global))
                            .collect::<Vec<_>>()
                            .join(", ")
                    };
                    (format!("{}({})", fun_name, args), 90)
                }
            }
            Call(CallFun::InternalFun(func), _, exps) => {
                let args =
                    exps.iter().map(|e| e.x.to_user_string(global)).collect::<Vec<_>>().join(", ");
                (format!("{:?}({})", func, args), 90)
            }
            ExecFnByName(func) => (format!("{:?}", func), 99),
            NullaryOpr(crate::ast::NullaryOpr::ConstGeneric(c)) => {
                (format!("const_generic({:?})", c).to_string(), 99)
            }
            NullaryOpr(crate::ast::NullaryOpr::TraitBound(..)) => ("".to_string(), 99),
            NullaryOpr(crate::ast::NullaryOpr::TypEqualityBound(..)) => ("".to_string(), 99),
            NullaryOpr(crate::ast::NullaryOpr::ConstTypBound(..)) => ("".to_string(), 99),
            Unary(op, exp) => match op {
                UnaryOp::Not | UnaryOp::BitNot(_) => {
                    (format!("!{}", exp.x.to_string_prec(global, 99)), 90)
                }
                UnaryOp::Clip { range, .. } => (
                    format!(
                        "clip({}, {})",
                        crate::ast_util::int_range_to_type_string(range),
                        exp.x.to_user_string(global)
                    ),
                    99,
                ),
                UnaryOp::IntToReal => {
                    (format!("int_to_real({})", exp.x.to_user_string(global)), 99)
                }
                UnaryOp::RealToInt => {
                    (format!("real_to_int({})", exp.x.to_user_string(global)), 99)
                }
                UnaryOp::FloatToBits => {
                    (format!("float_to_bits({})", exp.x.to_user_string(global)), 99)
                }
                UnaryOp::IeeeFloat(_) => {
                    (format!("ieee_float({})", exp.x.to_user_string(global)), 99)
                }
                UnaryOp::HeightTrigger => {
                    (format!("height_trigger({})", exp.x.to_user_string(global)), 99)
                }
                UnaryOp::NewStrLit => {
                    (format!("new_strlit({})", exp.x.to_string_prec(global, 99)), 90)
                }
                UnaryOp::StrLen => (format!("{}.len()", exp.x.to_string_prec(global, 99)), 90),
                UnaryOp::Trigger(..)
                | UnaryOp::CoerceMode { .. }
                | UnaryOp::MustBeFinalized
                | UnaryOp::MustBeElaborated => {
                    return exp.x.to_string_prec(global, precedence);
                }
                UnaryOp::CastToInteger => {
                    (format!("{} as int", exp.x.to_user_string(global)), precedence)
                }
                UnaryOp::MutRefCurrent => {
                    (format!("mut_ref_current({})", exp.x.to_string_prec(global, 99)), 0)
                }
                UnaryOp::MutRefFuture(_) => {
                    (format!("mut_ref_future({})", exp.x.to_string_prec(global, 99)), 0)
                }
                UnaryOp::MutRefPtr => {
                    (format!("mut_ref_ptr({})", exp.x.to_string_prec(global, 99)), 0)
                }
                UnaryOp::MutRefFinal(_) => {
                    (format!("final({})", exp.x.to_string_prec(global, 99)), 0)
                }
                UnaryOp::Length(_kind) => {
                    (format!("length({})", exp.x.to_string_prec(global, 99)), 0)
                }
            },
            UnaryOpr(op, exp) => {
                use crate::ast::UnaryOpr::*;
                match op {
                    Box(_) | Unbox(_) | ToDyn(..) => {
                        return exp.x.to_string_prec(global, precedence);
                    }
                    HasType(t) => {
                        (format!("has_type({}, {:?})", exp.x.to_user_string(global), t), 99)
                    }
                    HasResolved(t) => {
                        (format!("has_resolved::<{:?}>({})", t, exp.x.to_user_string(global)), 99)
                    }
                    IntegerTypeBound(IntegerTypeBoundKind::ArchWordBits) => {
                        (format!("usize::BITS"), 99)
                    }
                    IntegerTypeBound(kind) => {
                        (format!("{:?}({})", kind, exp.x.to_user_string(global)), 99)
                    }
                    IsVariant { datatype: _, variant } => {
                        let (prec_exp, prec_left, _prec_right) = prec_of_in();
                        (
                            format!("{} is {}", exp.x.to_string_prec(global, prec_left), variant),
                            prec_exp,
                        )
                    }
                    Field(field) => {
                        (format!("{}.{}", exp.x.to_user_string(global), field.field), 99)
                    }
                    CustomErr(_msg) => {
                        (format!("with_diagnostic({})", exp.x.to_user_string(global)), 99)
                    }
                    AutoDecreases | AutoLoopEnsures => {
                        return exp.x.to_string_prec(global, precedence);
                    }
                    ProofNote(_label) => {
                        (format!("with_diagnostic({})", exp.x.to_user_string(global)), 99)
                    }
                    LoopIsolationBoundary(..) => (
                        format!("loop_isolation_boundary({})", exp.x.to_string_prec(global, 99)),
                        0,
                    ),
                }
            }
            Binary(op, e1, e2) => {
                let (prec_exp, prec_left, prec_right) = op.prec_of_binary_op();
                use ArithOp::*;
                use BinaryOp::*;
                use BitwiseOp::*;
                use InequalityOp::*;
                let left = e1.x.to_string_prec(global, prec_left);
                let right = e2.x.to_string_prec(global, prec_right);
                let op_str = match op {
                    And => "&&",
                    Or => "||",
                    Xor => "^",
                    Implies => "==>",
                    HeightCompare { .. } => "",
                    Eq => "==",
                    Ne => "!=",
                    Inequality(o) => match o {
                        Le => "<=",
                        Ge => ">=",
                        Lt => "<",
                        Gt => ">",
                    },
                    Arith(o) => match o {
                        Add => "+",
                        Sub => "-",
                        Mul => "*",
                        EuclideanDiv => "/",
                        EuclideanMod => "%",
                    },
                    RealArith(o) => match o {
                        crate::ast::RealArithOp::Add => "+",
                        crate::ast::RealArithOp::Sub => "-",
                        crate::ast::RealArithOp::Mul => "*",
                        crate::ast::RealArithOp::Div => "/",
                    },
                    Bitwise(o) => match o {
                        BitXor => "^",
                        BitAnd => "&",
                        BitOr => "|",
                        Shr => ">>",
                        Shl(..) => "<<",
                    },
                    IeeeFloat(_) => "ieee_float",
                    StrGetChar => "ignored", // This is a non-infix BinaryOp, so it needs special handling below
                    Index(..) => "ignored", // This is a non-infix BinaryOp, so it needs special handling below
                };
                if let BinaryOp::StrGetChar = op {
                    (format!("{}.get_char({})", left, e2.x.to_user_string(global)), prec_exp)
                } else if let HeightCompare { .. } = op {
                    (format!("height_compare({left}, {right})"), prec_exp)
                } else if let Index(..) = op {
                    (format!("index({left}, {right})"), prec_exp)
                } else {
                    (format!("{} {} {}", left, op_str, right), prec_exp)
                }
            }
            BinaryOpr(crate::ast::BinaryOpr::ExtEq(deep, _), e1, e2) => {
                let (prec_exp, prec_left, prec_right) = BinaryOp::Eq.prec_of_binary_op();
                let left = e1.x.to_string_prec(global, prec_left);
                let right = e2.x.to_string_prec(global, prec_right);
                let op_str = if *deep { "=~~=" } else { "=~=" };
                (format!("{} {} {}", left, op_str, right), prec_exp)
            }
            If(e1, e2, e3) => (
                format!(
                    "if {} {{ {} }} else {{ {} }}",
                    e1.x.to_user_string(global),
                    e2.x.to_user_string(global),
                    e3.x.to_user_string(global)
                ),
                99,
            ),
            Bind(bnd, exp) => {
                let s = match &bnd.x {
                    BndX::Let(bnds) => {
                        let assigns = bnds
                            .iter()
                            .map(|b| {
                                format!(
                                    "{} = {}",
                                    user_local_name(&b.name),
                                    b.a.x.to_user_string(global)
                                )
                            })
                            .collect::<Vec<_>>()
                            .join(", ");
                        format!("let {} in {}", assigns, exp.x.to_user_string(global))
                    }
                    BndX::Quant(Quant { quant: q, .. }, bnds, _trigs, _) => {
                        let q_str = match q {
                            air::ast::Quant::Forall => "forall",
                            air::ast::Quant::Exists => "exists",
                        };
                        let vars = bnds
                            .iter()
                            .map(|b| format!("{}", user_local_name(&b.name)))
                            .collect::<Vec<_>>()
                            .join(", ");

                        format!("({} |{}| {})", q_str, vars, exp.x.to_user_string(global))
                    }
                    BndX::Lambda(bnds, _trigs) => {
                        let assigns = bnds
                            .iter()
                            .map(|b| format!("{}", user_local_name(&b.name)))
                            .collect::<Vec<_>>()
                            .join(", ");
                        format!("(|{}| {})", assigns, exp.x.to_user_string(global))
                    }
                    BndX::Choose(bnds, _trigs, cond) => {
                        let vars = bnds
                            .iter()
                            .map(|b| format!("{}", user_local_name(&b.name)))
                            .collect::<Vec<_>>()
                            .join(", ");
                        format!(
                            "(choose |{}| {}, {})",
                            vars,
                            cond.x.to_user_string(global),
                            exp.x.to_user_string(global)
                        )
                    }
                };
                (s, 99)
            }
            Ctor(dt, variant_id, bnds) => {
                let style = match dt {
                    Dt::Path(path) => match global.datatypes.get(path) {
                        Some((_, variants)) => get_variant(variants, variant_id).ctor_style,
                        _ => CtorPrintStyle::Braces,
                    },
                    Dt::Tuple(_) => CtorPrintStyle::Tuple,
                };
                match style {
                    CtorPrintStyle::Parens | CtorPrintStyle::Tuple => {
                        match sst_unpack_tuple_style_ctor(self) {
                            Some(es) => {
                                let args = es
                                    .iter()
                                    .map(|e| e.x.to_user_string(global))
                                    .collect::<Vec<_>>()
                                    .join(", ");
                                let variant = if matches!(style, CtorPrintStyle::Parens) {
                                    &variant_id
                                } else {
                                    ""
                                };
                                (format!("{}({})", variant, args), 99)
                            }
                            None => {
                                // This probably shouldn't happen; if it does, fall back
                                // on the brace style
                                let args = bnds
                                    .iter()
                                    .map(|b| {
                                        format!("{}: {}", b.name, b.a.x.to_user_string(global))
                                    })
                                    .collect::<Vec<_>>()
                                    .join(", ");
                                (format!("{} {} {} {}", variant_id, "{", args, "}"), 99)
                            }
                        }
                    }
                    CtorPrintStyle::Const => (format!("{}", variant_id), 99),
                    CtorPrintStyle::Braces => {
                        let args = bnds
                            .iter()
                            .map(|b| format!("{}: {}", b.name, b.a.x.to_user_string(global)))
                            .collect::<Vec<_>>()
                            .join(", ");
                        (format!("{} {} {} {}", variant_id, "{", args, "}"), 99)
                    }
                }
            }
            CallLambda(e, args) => {
                let args =
                    args.iter().map(|e| e.x.to_user_string(global)).collect::<Vec<_>>().join(", ");
                (format!("{}({})", e.x.to_user_string(global), args), 99)
            }
            ArrayLiteral(es) => {
                let v =
                    es.iter().map(|e| e.x.to_user_string(global)).collect::<Vec<_>>().join(", ");
                (format!("[{}]", v), 99)
            }
            Interp(e) => {
                use InterpExp::*;
                match e {
                    FreeVar(id) => (format!("{}", user_local_name(id)), 99),
                    Seq(s) => {
                        let v = s
                            .iter()
                            .map(|e| e.x.to_user_string(global))
                            .collect::<Vec<_>>()
                            .join(", ");
                        (format!("[{}]", v), 99)
                    }
                    Closure(e, _ctx) => (format!("{}", e.x.to_user_string(global)), 99),
                    Array(s) => {
                        let v = s
                            .iter()
                            .map(|e| e.x.to_user_string(global))
                            .collect::<Vec<_>>()
                            .join(", ");
                        (format!("[{}]", v), 99)
                    }
                }
            }
            FuelConst(i) => (format!("fuel({i:})"), 99),
            Old(..) | WithTriggers(..) => ("".to_string(), 99), // We don't show the user these internal expressions
        };
        if precedence <= inner_precedence { s } else { format!("({})", s) }
    }
}

pub(crate) fn sst_exp_get_proof_note(exp: &Exp) -> Option<ProofNoteLabel> {
    match &exp.x {
        ExpX::UnaryOpr(UnaryOpr::Box(_), e) => sst_exp_get_proof_note(e),
        ExpX::UnaryOpr(UnaryOpr::Unbox(_), e) => sst_exp_get_proof_note(e),
        ExpX::UnaryOpr(UnaryOpr::ProofNote(label), _) => Some(label.clone()),
        _ => None,
    }
}

/// Collect proof notes from a function's `requires` clauses.
pub fn func_collect_requires_proof_notes(func: &FunctionSst) -> HashSet<String> {
    func.x
        .decl
        .reqs
        .iter()
        .filter_map(sst_exp_get_proof_note)
        .filter(|proof_note| !proof_note.is_custom_err)
        .map(|proof_note| proof_note.text.to_string())
        .collect()
}

/// Collect proof notes from a function's proof obligations.
///
/// Each proof obligation is one of the following cases:
/// - an `assert` statement
/// - a `requires` clause of a callee (another function called by this function)
/// - an `ensures` clause of this function
pub fn func_collect_obligation_proof_notes(
    func: &FunctionSst,
    func_to_requires_proof_notes: &HashMap<Fun, HashSet<String>>,
) -> HashSet<String> {
    let mut collector = ObligationProofNoteCollector::new(func_to_requires_proof_notes);
    if let Some(func_check) = func.x.exec_proof_check.as_ref() {
        collector.collect_func_check(func_check);
    }
    if let Some(spec_axioms) = func.x.axioms.spec_axioms.as_ref()
        && let Some(func_check) = spec_axioms.termination_check.as_ref()
    {
        collector.collect_func_check(func_check);
    }
    collector.proof_notes
}

struct ObligationProofNoteCollector<'a> {
    proof_notes: HashSet<String>,
    func_to_requires_proof_notes: &'a HashMap<Fun, HashSet<String>>,
}

impl<'a> ObligationProofNoteCollector<'a> {
    fn new(func_to_requires_proof_notes: &'a HashMap<Fun, HashSet<String>>) -> Self {
        Self { proof_notes: HashSet::new(), func_to_requires_proof_notes }
    }

    fn collect_func_check(&mut self, func_check: &FuncCheckSst) {
        // NOTE: Skip `func_check.reqs` to exclude `requires` clauses.
        // Collect proof notes from this function's own `ensures` clauses.
        for ens in func_check.post_condition.ens_exps.iter() {
            if let Some(label) = sst_exp_get_proof_note(ens)
                && !label.is_custom_err
            {
                self.proof_notes.insert(label.text.to_string());
            }
        }
        for stm in func_check.post_condition.ens_spec_precondition_stms.iter() {
            self.visit_stm(stm).expect("proof-note collector should not fail");
        }
        self.visit_unwind(&func_check.unwind).expect("proof-note collector should not fail");
        self.visit_stm(&func_check.body).expect("proof-note collector should not fail");
    }
}

impl<'a> Visitor<Walk, (), NoScoper> for ObligationProofNoteCollector<'a> {
    fn visit_stm(&mut self, stm: &Stm) -> Result<(), ()> {
        match &stm.x {
            // Collect proof note labels from callee `requires` clauses.
            StmX::Call { fun: crate::sst::CallTarget::Fun(fun), .. } => {
                if let Some(callee_req_notes) = self.func_to_requires_proof_notes.get(fun) {
                    self.proof_notes.extend(callee_req_notes.iter().cloned());
                }
            }
            // Collect proof note labels from `assert` statements.
            StmX::Assert(_, maybe_msg, exp) => {
                if let Some(label) = sst_exp_get_proof_note(exp)
                    && !label.is_custom_err
                {
                    self.proof_notes.insert(label.text.to_string());
                }
                if let Some(msg) = maybe_msg {
                    // This is likely unnecessary; here for future-proofing.
                    for label in msg.labels.iter() {
                        if label.is_proof_note && !label.is_custom_err {
                            self.proof_notes.insert(label.note.clone());
                        }
                    }
                }
            }
            _ => {}
        }
        self.visit_stm_rec(stm)
    }
}

pub fn sst_arch_word_bits(span: &Span) -> Exp {
    SpannedTyped::new(
        span,
        &Arc::new(TypX::Int(IntRange::Int)),
        ExpX::UnaryOpr(
            UnaryOpr::IntegerTypeBound(IntegerTypeBoundKind::ArchWordBits),
            sst_int_literal(span, 0),
        ),
    )
}

/// Returns an Exp (of type `int`) that represents the bit-width of the given
/// type. For example:
///   - If the input type is `u8`, then it returns a constant `8`
///   - If the input type is `usize`, then it returns the symbolic `arch_word_bits`
pub fn sst_bitwidth(span: &Span, w: &IntegerTypeBitwidth, arch: &crate::ast::ArchWordBits) -> Exp {
    match w.to_exact(arch) {
        Some(w) => sst_int_literal(span, w as i128),
        None => sst_arch_word_bits(span),
    }
}

fn chain_binary(span: &Span, op: BinaryOp, init: &Exp, exps: &[Exp]) -> Exp {
    if exps.len() == 0 {
        return init.clone();
    }
    let mut exp = exps[0].clone();
    for e in exps.iter().skip(1) {
        exp = SpannedTyped::new(span, &init.typ, ExpX::Binary(op, exp, e.clone()));
    }
    exp
}

pub fn sst_bool(span: &Span, b: bool) -> Exp {
    SpannedTyped::new(span, &Arc::new(TypX::Bool), ExpX::Const(Constant::Bool(b)))
}

pub fn sst_conjoin(span: &Span, exps: &Vec<Exp>) -> Exp {
    chain_binary(span, BinaryOp::And, &sst_bool(span, true), exps)
}

pub fn sst_disjoin(span: &Span, exps: &[Exp]) -> Exp {
    chain_binary(span, BinaryOp::Or, &sst_bool(span, false), exps)
}

pub fn sst_and(span: &Span, e1: &Exp, e2: &Exp) -> Exp {
    let op = BinaryOp::And;
    SpannedTyped::new(span, &Arc::new(TypX::Bool), ExpX::Binary(op, e1.clone(), e2.clone()))
}

pub fn sst_implies(span: &Span, e1: &Exp, e2: &Exp) -> Exp {
    let op = BinaryOp::Implies;
    SpannedTyped::new(span, &Arc::new(TypX::Bool), ExpX::Binary(op, e1.clone(), e2.clone()))
}

pub fn sst_lt(span: &Span, e1: &Exp, e2: &Exp) -> Exp {
    let op = BinaryOp::Inequality(InequalityOp::Lt);
    SpannedTyped::new(span, &Arc::new(TypX::Bool), ExpX::Binary(op, e1.clone(), e2.clone()))
}

pub fn sst_le(span: &Span, e1: &Exp, e2: &Exp) -> Exp {
    let op = BinaryOp::Inequality(InequalityOp::Le);
    SpannedTyped::new(span, &Arc::new(TypX::Bool), ExpX::Binary(op, e1.clone(), e2.clone()))
}

pub fn sst_equal(span: &Span, e1: &Exp, e2: &Exp) -> Exp {
    let op = BinaryOp::Eq;
    SpannedTyped::new(span, &Arc::new(TypX::Bool), ExpX::Binary(op, e1.clone(), e2.clone()))
}

pub fn sst_mut_ref_current(span: &Span, e1: &Exp) -> Exp {
    let t = match &*e1.typ {
        TypX::MutRef(t) => t,
        _ => panic!("sst_mut_ref_current expected MutRef type"),
    };
    let op = UnaryOp::MutRefCurrent;
    SpannedTyped::new(span, &t, ExpX::Unary(op, e1.clone()))
}

pub fn sst_mut_ref_future(span: &Span, e1: &Exp) -> Exp {
    let t = match &*e1.typ {
        TypX::MutRef(t) => t,
        _ => panic!("sst_mut_ref_future expected MutRef type"),
    };
    let op = UnaryOp::MutRefFuture(crate::ast::MutRefFutureSourceName::MutRefFuture);
    SpannedTyped::new(span, &t, ExpX::Unary(op, e1.clone()))
}

pub fn sst_mut_ref_ptr(span: &Span, e1: &Exp) -> Exp {
    let t = match &*undecorate_typ(&e1.typ) {
        TypX::MutRef(t) => t.clone(),
        _ => panic!("sst_mut_ref_ptr expected MutRef type"),
    };
    let ptr_t = Arc::new(TypX::Primitive(crate::ast::Primitive::Ptr, Arc::new(vec![t])));
    let op = UnaryOp::MutRefPtr;
    SpannedTyped::new(span, &ptr_t, ExpX::Unary(op, e1.clone()))
}

pub fn sst_ptr_addr(span: &Span, e1: &Exp) -> Exp {
    let t = match &*undecorate_typ(&e1.typ) {
        TypX::Primitive(crate::ast::Primitive::Ptr, ts) => ts[0].clone(),
        _ => panic!("sst_ptr_addr expects ptr type"),
    };
    let fun = crate::fun!(CrateId::Vstd => "raw_ptr", "spec_ptr_addr");
    let cf = CallFun::Fun(fun, None);
    let expx = ExpX::Call(cf, Arc::new(vec![t]), Arc::new(vec![e1.clone()]));
    let usize_t = Arc::new(TypX::Int(IntRange::USize));
    SpannedTyped::new(span, &usize_t, expx)
}

pub fn sst_equal_ext(span: &Span, e1: &Exp, e2: &Exp, ext: Option<bool>) -> Exp {
    match ext {
        None => sst_equal(span, e1, e2),
        Some(deep) => {
            let op = BinaryOpr::ExtEq(deep, crate::ast_util::undecorate_typ(&e1.typ));
            SpannedTyped::new(
                span,
                &Arc::new(TypX::Bool),
                ExpX::BinaryOpr(op, e1.clone(), e2.clone()),
            )
        }
    }
}

pub fn sst_not(span: &Span, e: &Exp) -> Exp {
    match &e.x {
        ExpX::Unary(UnaryOp::Not, e1) => e1.clone(),
        _ => {
            let op = UnaryOp::Not;
            SpannedTyped::new(span, &Arc::new(TypX::Bool), ExpX::Unary(op, e.clone()))
        }
    }
}

pub fn sst_int_literal(span: &Span, i: i128) -> Exp {
    SpannedTyped::new(
        span,
        &Arc::new(TypX::Int(IntRange::Int)),
        ExpX::Const(crate::ast_util::const_int_from_i128(i)),
    )
}

pub fn sst_int_literal_bigint(span: &Span, i: num_bigint::BigInt) -> Exp {
    SpannedTyped::new(span, &Arc::new(TypX::Int(IntRange::Int)), ExpX::Const(Constant::Int(i)))
}

impl LocalDeclKind {
    pub fn is_mutable(&self) -> bool {
        match self {
            LocalDeclKind::Param { mutable } => *mutable,
            LocalDeclKind::StmtLet { mutable } => *mutable,
            LocalDeclKind::ExecClosureParam { mutable } => *mutable,
            LocalDeclKind::Return
            | LocalDeclKind::TempViaAssign
            | LocalDeclKind::Decreases
            | LocalDeclKind::StmCallArg { native: _ }
            | LocalDeclKind::Assert
            | LocalDeclKind::AssertByVar { native: _ }
            | LocalDeclKind::LetBinder
            | LocalDeclKind::QuantBinder
            | LocalDeclKind::ChooseBinder
            | LocalDeclKind::ClosureBinder
            | LocalDeclKind::ExecClosureId
            | LocalDeclKind::ExecClosureRet
            | LocalDeclKind::Nondeterministic
            | LocalDeclKind::OpenInvariantInnerTemp
            | LocalDeclKind::LoopBreakValue
            | LocalDeclKind::BorrowMut => false,
        }
    }
}

/// Unit value
pub fn sst_unit_value(span: &Span) -> Exp {
    let name = Dt::Tuple(0);
    let variant = crate::def::prefix_tuple_variant(0);
    SpannedTyped::new(span, &unit_typ(), ExpX::Ctor(name, variant, Arc::new(vec![])))
}

pub fn sst_unpack_tuple_style_ctor(expx: &ExpX) -> Option<Vec<Exp>> {
    match &expx {
        ExpX::Ctor(_dt, _ident, binders) => {
            let n = binders.len();
            let mut results: Vec<Exp> = vec![];
            'outer: for i in 0..n {
                let field = crate::def::positional_field_ident(i);
                // Look for field named "i"
                for b in binders.iter() {
                    if b.name == field {
                        results.push(b.a.clone());
                        continue 'outer;
                    }
                }
                // If no field of name "i", then error
                return None;
            }
            return Some(results);
        }
        _ => None,
    }
}

pub fn sst_tuple(span: &Span, exps: &Exps) -> Exp {
    let typs = crate::util::vec_map(exps, |e| e.typ.clone());
    let tup_typ = crate::ast_util::mk_tuple_typ(&Arc::new(typs));
    SpannedTyped::new(span, &tup_typ, sst_tuple_x(exps))
}

pub fn sst_tuple_x(exps: &Exps) -> ExpX {
    let arity = exps.len();

    let mut binders: Vec<crate::ast::Binder<Exp>> = Vec::new();
    for (i, arg) in exps.iter().enumerate() {
        let field = crate::def::positional_field_ident(i);
        binders.push(crate::ast_util::ident_binder(&field, &arg));
    }
    let binders = Arc::new(binders);

    ExpX::Ctor(Dt::Tuple(arity), crate::def::prefix_tuple_variant(arity), binders)
}

pub(crate) fn sst_call_requires(
    ctx: &crate::context::Ctx,
    span: &Span,
    fun: &Fun,
    typ_args: &Typs,
    func: &crate::ast::Function,
    resolved_fun: &Option<Fun>,
    req_args: &Exps,
) -> Exp {
    let mut typ_substs: HashMap<Ident, Typ> = HashMap::new();
    assert!(func.x.typ_params.len() == typ_args.len());
    for (typ_param, arg) in func.x.typ_params.iter().zip(typ_args.iter()) {
        typ_substs.insert(typ_param.clone(), arg.clone());
    }

    let skip_dummy =
        func.x.params.len() > 0 && func.x.params[0].x.name == crate::def::dummy_param_name();
    let skip_dummy = if skip_dummy { 1 } else { 0 };

    let param_typs: Vec<Typ> =
        func.x.params.iter().skip(skip_dummy).map(|p| subst_typ(&typ_substs, &p.x.typ)).collect();

    let tuple_typ = crate::ast_util::mk_tuple_typ(&Arc::new(param_typs));
    let fndef_typ = Arc::new(TypX::FnDef(fun.clone(), typ_args.clone(), resolved_fun.clone()));

    let fndef_value = SpannedTyped::new(span, &fndef_typ, ExpX::ExecFnByName(fun.clone()));
    let fndef_value = crate::poly::coerce_exp_to_poly(ctx, &fndef_value);

    let req_args: Vec<Exp> =
        req_args.iter().skip(skip_dummy).map(|r| crate::poly::coerce_exp_to_poly(ctx, r)).collect();
    let args_tuple = sst_tuple(span, &Arc::new(req_args));
    let args_tuple = crate::poly::coerce_exp_to_poly(ctx, &args_tuple);

    let expx = ExpX::Call(
        CallFun::InternalFun(InternalFun::ClosureReq),
        Arc::new(vec![fndef_typ, tuple_typ]),
        Arc::new(vec![fndef_value, args_tuple]),
    );
    SpannedTyped::new(span, &Arc::new(TypX::Bool), expx)
}

pub(crate) fn sst_call_ensures(
    ctx: &crate::context::Ctx,
    span: &Span,
    fun: &Fun,
    typ_args: &Typs,
    func: &crate::ast::Function,
    resolved_fun: &Option<Fun>,
    req_args: &Exps,
    return_value: Option<Exp>,
) -> Exp {
    let mut typ_substs: HashMap<Ident, Typ> = HashMap::new();
    assert!(func.x.typ_params.len() == typ_args.len());
    for (typ_param, arg) in func.x.typ_params.iter().zip(typ_args.iter()) {
        typ_substs.insert(typ_param.clone(), arg.clone());
    }

    let skip_dummy =
        func.x.params.len() > 0 && func.x.params[0].x.name == crate::def::dummy_param_name();
    let skip_dummy = if skip_dummy { 1 } else { 0 };

    let param_typs: Vec<Typ> =
        func.x.params.iter().skip(skip_dummy).map(|p| subst_typ(&typ_substs, &p.x.typ)).collect();

    let tuple_typ = crate::ast_util::mk_tuple_typ(&Arc::new(param_typs));
    let fndef_typ = Arc::new(TypX::FnDef(fun.clone(), typ_args.clone(), resolved_fun.clone()));

    let fndef_value = SpannedTyped::new(span, &fndef_typ, ExpX::ExecFnByName(fun.clone()));
    let fndef_value = crate::poly::coerce_exp_to_poly(ctx, &fndef_value);

    let req_args: Vec<Exp> =
        req_args.iter().skip(skip_dummy).map(|r| crate::poly::coerce_exp_to_poly(ctx, r)).collect();
    let args_tuple = sst_tuple(span, &Arc::new(req_args));
    let args_tuple = crate::poly::coerce_exp_to_poly(ctx, &args_tuple);

    let return_value = match &return_value {
        Some(r) => crate::poly::coerce_exp_to_poly(ctx, r),
        None => {
            let unit = sst_tuple(span, &Arc::new(vec![]));
            crate::poly::coerce_exp_to_poly(ctx, &unit)
        }
    };

    let expx = ExpX::Call(
        CallFun::InternalFun(InternalFun::ClosureEns),
        Arc::new(vec![fndef_typ, tuple_typ]),
        Arc::new(vec![fndef_value, args_tuple, return_value]),
    );
    SpannedTyped::new(span, &Arc::new(TypX::Bool), expx)
}

pub(crate) fn exp_with_vars_at_pre_state(exp: &Exp, vars: &HashSet<UniqueIdent>) -> Exp {
    crate::sst_visitor::map_exp_visitor(exp, &mut |e| match &e.x {
        ExpX::Var(uid) if vars.contains(uid) => e.new_x(ExpX::VarAt(uid.clone(), VarAt::Pre)),
        _ => e.clone(),
    })
}

pub(crate) fn stm_with_vars_at_pre_state(stm: &Stm, vars: &HashSet<UniqueIdent>) -> Stm {
    crate::sst_visitor::map_exps_in_stm_visitor(stm, &mut |e| match &e.x {
        ExpX::Var(uid) if vars.contains(uid) => e.new_x(ExpX::VarAt(uid.clone(), VarAt::Pre)),
        _ => e.clone(),
    })
}
