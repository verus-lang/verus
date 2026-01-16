use crate::ast::{
    ArithOp, BinaryOp, BinaryOpr, BitwiseOp, Constant, CtorPrintStyle, Dt, Fun, Ident,
    InequalityOp, IntRange, IntegerTypeBitwidth, IntegerTypeBoundKind, Mode, Quant, SpannedTyped,
    Typ, TypX, Typs, UnaryOp, UnaryOpr, VarBinder, VarBinderX, VarBinders,
};
use crate::ast_util::{get_variant, unit_typ};
use crate::context::GlobalCtx;
use crate::def::{Spanned, unique_bound, user_local_name};
use crate::interpreter::InterpExp;
use crate::messages::Span;
use crate::sst::{
    BndX, CallFun, Exp, ExpX, Exps, InternalFun, LocalDeclKind, Stm, Trig, Trigs, UniqueIdent,
};
use air::scope_map::ScopeMap;
use std::collections::HashMap;
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

struct SubstCtxt<'a> {
    typ_substs: &'a HashMap<Ident, Typ>,
    // free variables in the Exps in SubstState.substs:
    allow_unfinalized: bool,
}

struct SubstState {
    substs: ScopeMap<UniqueIdent, Exp>,
    free_vars: ScopeMap<UniqueIdent, ()>,
    // variables already in scope, which we therefore cannot use when picking a fresh variable name:
    fresh_var_blacklist: ScopeMap<UniqueIdent, ()>,
}

fn subst_rename_binders<A: Clone, FA: Fn(&A) -> A, FT: Fn(&A) -> Typ>(
    span: &Span,
    _ctxt: &SubstCtxt,
    state: &mut SubstState,
    bs: &VarBinders<A>,
    fa: FA,
    f_typ: FT,
) -> VarBinders<A> {
    state.substs.push_scope(false);
    state.free_vars.push_scope(true);
    state.fresh_var_blacklist.push_scope(true);
    let mut binders: Vec<VarBinder<A>> = Vec::new();
    for b in bs.iter() {
        let unique = unique_bound(&b.name);
        let name = if state.free_vars.contains_key(&unique) {
            // capture-avoiding substitution:
            // rename bound variable to avoid capturing free variable
            let mut n: u64 = 0;
            loop {
                let name = crate::def::subst_rename_ident(&b.name, n);
                let rename = unique_bound(&name);
                if !state.fresh_var_blacklist.contains_key(&rename) {
                    state
                        .free_vars
                        .insert(rename.clone(), ())
                        .expect("subst_rename_binders free_vars");
                    state
                        .fresh_var_blacklist
                        .insert(rename.clone(), ())
                        .expect("subst_rename_binders fresh_var_blacklist");
                    let typ = f_typ(&b.a);
                    let var = SpannedTyped::new(span, &typ, ExpX::Var(rename.clone()));
                    state.substs.insert(unique, var).expect("subst_rename_binders substs");
                    break name;
                }
                n += 1;
            }
        } else {
            state
                .fresh_var_blacklist
                .insert(unique.clone(), ())
                .expect("subst_rename_binders fresh_var_blacklist");
            b.name.clone()
        };
        binders.push(Arc::new(VarBinderX { name, a: fa(&b.a) }));
    }
    Arc::new(binders)
}

fn subst_exp_rec(ctxt: &SubstCtxt, state: &mut SubstState, exp: &Exp) -> Exp {
    // If we're not finalized, substitutions are only allowed for type variables:
    assert!(!ctxt.allow_unfinalized || state.substs.map().len() == 0);

    let typ = subst_typ(&ctxt.typ_substs, &exp.typ);
    let mk_exp = |e: ExpX| SpannedTyped::new(&exp.span, &typ, e);
    let ft = |t: &Typ| subst_typ(&ctxt.typ_substs, t);
    match &exp.x {
        ExpX::Unary(UnaryOp::MustBeFinalized, _) if !ctxt.allow_unfinalized => {
            // Var won't match binders if we're not finalized
            // (special case allow_unfinalized = true for type-only substitution)
            panic!("MustBeFinalized")
        }
        ExpX::Const(..)
        | ExpX::Loc(..)
        | ExpX::StaticVar(..)
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
        | ExpX::ExecFnByName(..)
        | ExpX::FuelConst(..)
        | ExpX::WithTriggers(..) => crate::sst_visitor::map_shallow_exp(
            exp,
            state,
            &|_, t| Ok(subst_typ(ctxt.typ_substs, t)),
            &|state, e| Ok(subst_exp_rec(ctxt, state, e)),
        )
        .expect("map_shallow_exp for subst_exp_rec"),
        ExpX::Var(x) => {
            assert!(state.fresh_var_blacklist.contains_key(x));
            match state.substs.get(x) {
                None => mk_exp(ExpX::Var(x.clone())),
                Some(e) => e.clone(),
            }
        }
        ExpX::VarLoc(x) => match state.substs.get(x) {
            None => mk_exp(ExpX::VarLoc(x.clone())),
            Some(_) => panic!("cannot substitute for VarLoc"),
        },
        ExpX::VarAt(x, a) => match state.substs.get(x) {
            None => mk_exp(ExpX::VarAt(x.clone(), *a)),
            Some(_) => panic!("cannot substitute for VarAt"),
        },
        ExpX::Bind(bnd, e1) => {
            let ftrigs = |state: &mut SubstState, triggers: &Trigs| -> Trigs {
                let mut trigs: Vec<Trig> = Vec::new();
                for trigger in triggers.iter() {
                    let mut trig: Vec<Exp> = Vec::new();
                    for t in trigger.iter() {
                        trig.push(subst_exp_rec(ctxt, state, t));
                    }
                    trigs.push(Arc::new(trig));
                }
                Arc::new(trigs)
            };
            let bndx = match &bnd.x {
                BndX::Let(bs) => {
                    let mut binders: Vec<VarBinder<Exp>> = Vec::new();
                    for b in bs.iter() {
                        binders.push(b.new_a(subst_exp_rec(ctxt, state, &b.a)));
                    }
                    let binders = subst_rename_binders(
                        &bnd.span,
                        ctxt,
                        state,
                        &Arc::new(binders),
                        |e: &Exp| e.clone(),
                        |e: &Exp| e.typ.clone(),
                    );
                    BndX::Let(binders)
                }
                BndX::Quant(quant, binders, ts, ab) => {
                    let binders = subst_rename_binders(&bnd.span, ctxt, state, binders, ft, ft);
                    BndX::Quant(*quant, binders, ftrigs(state, ts), ab.clone())
                }
                BndX::Lambda(binders, ts) => {
                    let binders = subst_rename_binders(&bnd.span, ctxt, state, binders, ft, ft);
                    BndX::Lambda(binders, ftrigs(state, ts))
                }
                BndX::Choose(binders, ts, cond) => {
                    let binders = subst_rename_binders(&bnd.span, ctxt, state, binders, ft, ft);
                    let cond = subst_exp_rec(ctxt, state, cond);
                    BndX::Choose(binders, ftrigs(state, ts), cond)
                }
            };
            let bnd = Spanned::new(bnd.span.clone(), bndx);
            let e1 = subst_exp_rec(ctxt, state, e1);
            state.substs.pop_scope();
            state.free_vars.pop_scope();
            state.fresh_var_blacklist.pop_scope();
            SpannedTyped::new(&exp.span, &typ, ExpX::Bind(bnd, e1))
        }
        ExpX::ArrayLiteral(exprs) => {
            let mut new_exprs: Vec<Exp> = Vec::new();
            for e in exprs.iter() {
                new_exprs.push(subst_exp_rec(ctxt, state, e));
            }
            mk_exp(ExpX::ArrayLiteral(Arc::new(new_exprs)))
        }
        ExpX::Interp(_) => {
            panic!("Found an interpreter expression {:?} outside the interpreter", exp)
        }
    }
}

pub(crate) fn subst_exp(
    typ_substs: &HashMap<Ident, Typ>,
    substs: &HashMap<UniqueIdent, Exp>,
    exp: &Exp,
) -> Exp {
    if typ_substs.len() == 0 && substs.len() == 0 {
        return exp.clone();
    }
    let allow_unfinalized = substs.len() == 0;

    let mut scope_substs: ScopeMap<UniqueIdent, Exp> = ScopeMap::new();
    let mut free_vars: ScopeMap<UniqueIdent, ()> = ScopeMap::new();
    let mut fresh_var_blacklist: ScopeMap<UniqueIdent, ()> = ScopeMap::new();
    scope_substs.push_scope(false);
    free_vars.push_scope(true);
    fresh_var_blacklist.push_scope(true);
    let mut exp_free_vars_map: HashMap<UniqueIdent, Typ> = HashMap::new();
    free_vars_exp_scope(
        exp,
        &mut crate::sst_visitor::VisitorScopeMap::new(),
        &mut exp_free_vars_map,
        allow_unfinalized,
    );
    for (y, _) in exp_free_vars_map {
        let _ = fresh_var_blacklist.insert(y.clone(), ());
    }
    for (x, v) in substs {
        scope_substs.insert(x.clone(), v.clone()).expect("subst_exp scope_substs.insert");
        for (y, _) in free_vars_exp(v) {
            let _ = free_vars.insert(y.clone(), ());
            let _ = fresh_var_blacklist.insert(y.clone(), ());
        }
    }
    let ctxt = SubstCtxt { typ_substs, allow_unfinalized };
    let mut state = SubstState { substs: scope_substs, free_vars, fresh_var_blacklist };
    let e = subst_exp_rec(&ctxt, &mut state, exp);
    state.substs.pop_scope();
    state.free_vars.pop_scope();
    state.fresh_var_blacklist.pop_scope();
    assert_eq!(state.substs.num_scopes(), 0);
    assert_eq!(state.free_vars.num_scopes(), 0);
    assert_eq!(state.fresh_var_blacklist.num_scopes(), 0);
    e
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
            Eq(_) | Ne => (10, 11, 11),
            Inequality(_) => (10, 10, 10),
            Arith(o) => match o {
                Add(_) | Sub(_) => (30, 30, 31),
                Mul(_) | EuclideanDiv(_) | EuclideanMod(_) => (40, 40, 41),
            },
            RealArith(o) => match o {
                crate::ast::RealArithOp::Add | crate::ast::RealArithOp::Sub => (30, 30, 31),
                crate::ast::RealArithOp::Mul | crate::ast::RealArithOp::Div => (40, 40, 41),
            },
            Bitwise(o, _) => match o {
                BitXor => (22, 22, 23),
                BitAnd => (24, 24, 25),
                BitOr => (20, 20, 21),
                Shr(..) | Shl(..) => (26, 26, 27),
            },
            StrGetChar => (90, 90, 90),
            Index(_, _) => (90, 90, 90),
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
            NullaryOpr(crate::ast::NullaryOpr::NoInferSpecForLoopIter) => ("no_in".to_string(), 99),
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
                UnaryOp::FloatToBits => {
                    (format!("float_to_bits({})", exp.x.to_user_string(global)), 99)
                }
                UnaryOp::IntToReal => {
                    (format!("int_to_real({})", exp.x.to_user_string(global)), 99)
                }
                UnaryOp::RealToInt => {
                    (format!("real_to_int({})", exp.x.to_user_string(global)), 99)
                }
                UnaryOp::HeightTrigger => {
                    (format!("height_trigger({})", exp.x.to_user_string(global)), 99)
                }
                UnaryOp::StrLen => (format!("{}.len()", exp.x.to_string_prec(global, 99)), 90),
                UnaryOp::StrIsAscii => {
                    (format!("{}.is_ascii()", exp.x.to_string_prec(global, 99)), 90)
                }
                UnaryOp::Trigger(..)
                | UnaryOp::CoerceMode { .. }
                | UnaryOp::ToDyn
                | UnaryOp::MustBeFinalized
                | UnaryOp::MustBeElaborated => {
                    return exp.x.to_string_prec(global, precedence);
                }
                UnaryOp::InferSpecForLoopIter { .. } => {
                    (format!("InferSpecForLoopIter({})", exp.x.to_string_prec(global, 99)), 0)
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
                UnaryOp::MutRefFinal => (format!("fin({})", exp.x.to_string_prec(global, 99)), 0),
                UnaryOp::Length(_kind) => {
                    (format!("length({})", exp.x.to_string_prec(global, 99)), 0)
                }
            },
            UnaryOpr(op, exp) => {
                use crate::ast::UnaryOpr::*;
                match op {
                    Box(_) | Unbox(_) => {
                        return exp.x.to_string_prec(global, precedence);
                    }
                    HasType(t) => {
                        (format!("has_type({}, {:?})", exp.x.to_user_string(global), t), 99)
                    }
                    HasResolved(t) => {
                        (format!("has_resolved::<{:?}>({})", t, exp.x.to_user_string(global)), 99)
                    }
                    IntegerTypeBound(IntegerTypeBoundKind::ArchWordBits, _mode) => {
                        (format!("usize::BITS"), 99)
                    }
                    IntegerTypeBound(kind, mode) => {
                        (format!("{:?}.{:?}({})", kind, mode, exp.x.to_user_string(global)), 99)
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
                    Eq(_) => "==",
                    Ne => "!=",
                    Inequality(o) => match o {
                        Le => "<=",
                        Ge => ">=",
                        Lt => "<",
                        Gt => ">",
                    },
                    Arith(o) => match o {
                        Add(_) => "+",
                        Sub(_) => "-",
                        Mul(_) => "*",
                        EuclideanDiv(_) => "/",
                        EuclideanMod(_) => "%",
                    },
                    RealArith(o) => match o {
                        crate::ast::RealArithOp::Add => "+",
                        crate::ast::RealArithOp::Sub => "-",
                        crate::ast::RealArithOp::Mul => "*",
                        crate::ast::RealArithOp::Div => "/",
                    },
                    Bitwise(o, _) => match o {
                        BitXor => "^",
                        BitAnd => "&",
                        BitOr => "|",
                        Shr(..) => ">>",
                        Shl(..) => "<<",
                    },
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
                let (prec_exp, prec_left, prec_right) =
                    BinaryOp::Eq(Mode::Spec).prec_of_binary_op();
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

pub fn sst_arch_word_bits(span: &Span) -> Exp {
    SpannedTyped::new(
        span,
        &Arc::new(TypX::Int(IntRange::Int)),
        ExpX::UnaryOpr(
            UnaryOpr::IntegerTypeBound(
                IntegerTypeBoundKind::ArchWordBits,
                Mode::Spec, // mode doesn't matter
            ),
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
    let op = BinaryOp::Eq(Mode::Spec);
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
            | LocalDeclKind::ExecClosureParam
            | LocalDeclKind::ExecClosureRet
            | LocalDeclKind::Nondeterministic
            | LocalDeclKind::OpenInvariantInnerTemp
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
    let param_typs: Vec<Typ> =
        func.x.params.iter().map(|p| subst_typ(&typ_substs, &p.x.typ)).collect();

    let tuple_typ = crate::ast_util::mk_tuple_typ(&Arc::new(param_typs));
    let fndef_typ = Arc::new(TypX::FnDef(fun.clone(), typ_args.clone(), resolved_fun.clone()));

    let fndef_value = SpannedTyped::new(span, &fndef_typ, ExpX::ExecFnByName(fun.clone()));
    let fndef_value = crate::poly::coerce_exp_to_poly(ctx, &fndef_value);

    let req_args: Vec<Exp> =
        req_args.iter().map(|r| crate::poly::coerce_exp_to_poly(ctx, r)).collect();
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
    let param_typs: Vec<Typ> =
        func.x.params.iter().map(|p| subst_typ(&typ_substs, &p.x.typ)).collect();

    let tuple_typ = crate::ast_util::mk_tuple_typ(&Arc::new(param_typs));
    let fndef_typ = Arc::new(TypX::FnDef(fun.clone(), typ_args.clone(), resolved_fun.clone()));

    let fndef_value = SpannedTyped::new(span, &fndef_typ, ExpX::ExecFnByName(fun.clone()));
    let fndef_value = crate::poly::coerce_exp_to_poly(ctx, &fndef_value);

    let req_args: Vec<Exp> =
        req_args.iter().map(|r| crate::poly::coerce_exp_to_poly(ctx, r)).collect();
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
