use crate::air_ast::{Binder, BinderX, Binders, Ident};
use crate::ast::{
    ArithOp, BinaryOp, BitwiseOp, Constant, InequalityOp, IntRange, IntegerTypeBoundKind, Mode,
    Quant, SpannedTyped, Typ, TypX, UnaryOp, UnaryOpr,
};
use crate::def::{unique_bound, user_local_name, Spanned};
use crate::interpreter::InterpExp;
use crate::messages::Span;
use crate::prelude::ArchWordBits;
use crate::sst::{BndX, CallFun, Exp, ExpX, Stm, Trig, Trigs, UniqueIdent};
use air::scope_map::ScopeMap;
use std::collections::HashMap;
use std::fmt;
use std::sync::Arc;

pub(crate) fn free_vars_exp(exp: &Exp) -> HashMap<UniqueIdent, Typ> {
    free_vars_exp_scope(exp, &mut crate::sst_visitor::VisitorScopeMap::new())
}

fn free_vars_exp_scope(
    exp: &Exp,
    scope_map: &mut crate::sst_visitor::VisitorScopeMap,
) -> HashMap<UniqueIdent, Typ> {
    let mut vars: HashMap<UniqueIdent, Typ> = HashMap::new();
    crate::sst_visitor::exp_visitor_dfs::<(), _>(exp, scope_map, &mut |e, scope_map| {
        match &e.x {
            ExpX::Var(x) | ExpX::VarLoc(x) if !scope_map.contains_key(&x.name) => {
                vars.insert(x.clone(), e.typ.clone());
            }
            _ => (),
        }
        crate::sst_visitor::VisitorControlFlow::Recurse
    });
    vars
}

pub(crate) fn free_vars_stm(stm: &Stm) -> HashMap<UniqueIdent, Typ> {
    let mut vars: HashMap<UniqueIdent, Typ> = HashMap::new();
    crate::sst_visitor::stm_exp_visitor_dfs::<(), _>(stm, &mut |exp, scope_map| {
        vars.extend(free_vars_exp_scope(exp, scope_map).into_iter());
        crate::sst_visitor::VisitorControlFlow::Recurse
    });
    vars
}

fn subst_typ(typ_substs: &HashMap<Ident, Typ>, typ: &Typ) -> Typ {
    crate::ast_visitor::map_typ_visitor(typ, &|t: &Typ| match &**t {
        TypX::TypParam(x) => match typ_substs.get(x) {
            Some(t) => Ok(t.clone()),
            None => Ok(t.clone()),
        },
        _ => Ok(t.clone()),
    })
    .expect("subst_typ")
}

fn subst_rename_binders<A: Clone, FA: Fn(&A) -> A, FT: Fn(&A) -> Typ>(
    span: &Span,
    substs: &mut ScopeMap<UniqueIdent, Exp>,
    free_vars: &mut ScopeMap<UniqueIdent, ()>,
    bs: &Binders<A>,
    fa: FA,
    f_typ: FT,
) -> Binders<A> {
    substs.push_scope(false);
    free_vars.push_scope(false);
    let mut binders: Vec<Binder<A>> = Vec::new();
    for b in bs.iter() {
        let unique = unique_bound(&b.name);
        let name = if free_vars.contains_key(&unique) {
            // capture-avoiding substitution:
            // rename bound variable to avoid capturing free variable
            let mut n: u64 = 0;
            loop {
                let name = crate::def::subst_rename_ident(&b.name, n);
                let rename = unique_bound(&name);
                if !free_vars.contains_key(&rename) {
                    free_vars.insert(rename.clone(), ()).expect("subst_rename_binders free_vars");
                    let typ = f_typ(&b.a);
                    let var = SpannedTyped::new(span, &typ, ExpX::Var(rename.clone()));
                    substs.insert(unique, var).expect("subst_rename_binders substs");
                    break name;
                }
                n += 1;
            }
        } else {
            b.name.clone()
        };
        binders.push(Arc::new(BinderX { name, a: fa(&b.a) }));
    }
    Arc::new(binders)
}

fn subst_exp_rec(
    typ_substs: &HashMap<Ident, Typ>,
    substs: &mut ScopeMap<UniqueIdent, Exp>,
    free_vars: &mut ScopeMap<UniqueIdent, ()>,
    exp: &Exp,
) -> Exp {
    let typ = subst_typ(typ_substs, &exp.typ);
    let mk_exp = |e: ExpX| SpannedTyped::new(&exp.span, &typ, e);
    let ft = |t: &Typ| subst_typ(typ_substs, t);
    match &exp.x {
        ExpX::Const(..)
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
        | ExpX::WithTriggers(..) => crate::sst_visitor::map_shallow_exp(
            exp,
            &mut (substs, free_vars),
            &|_, t| Ok(subst_typ(typ_substs, t)),
            &|(substs, free_vars), e| Ok(subst_exp_rec(typ_substs, substs, free_vars, e)),
        )
        .expect("map_shallow_exp for subst_exp_rec"),
        ExpX::Var(x) => match substs.get(x) {
            None => mk_exp(ExpX::Var(x.clone())),
            Some(e) => e.clone(),
        },
        ExpX::VarLoc(x) => match substs.get(x) {
            None => mk_exp(ExpX::VarLoc(x.clone())),
            Some(_) => panic!("cannot substitute for VarLoc"),
        },
        ExpX::VarAt(x, a) => match substs.get(x) {
            None => mk_exp(ExpX::VarAt(x.clone(), *a)),
            Some(_) => panic!("cannot substitute for VarAt"),
        },
        ExpX::Bind(bnd, e1) => {
            let ftrigs = |substs: &mut ScopeMap<UniqueIdent, Exp>,
                          free_vars: &mut ScopeMap<UniqueIdent, ()>,
                          triggers: &Trigs|
             -> Trigs {
                let mut trigs: Vec<Trig> = Vec::new();
                for trigger in triggers.iter() {
                    let mut trig: Vec<Exp> = Vec::new();
                    for t in trigger.iter() {
                        trig.push(subst_exp_rec(typ_substs, substs, free_vars, t));
                    }
                    trigs.push(Arc::new(trig));
                }
                Arc::new(trigs)
            };
            let bndx = match &bnd.x {
                BndX::Let(bs) => {
                    let mut binders: Vec<Binder<Exp>> = Vec::new();
                    for b in bs.iter() {
                        binders.push(b.new_a(subst_exp_rec(typ_substs, substs, free_vars, &b.a)));
                    }
                    let binders = subst_rename_binders(
                        &bnd.span,
                        substs,
                        free_vars,
                        &Arc::new(binders),
                        |e: &Exp| e.clone(),
                        |e: &Exp| e.typ.clone(),
                    );
                    BndX::Let(binders)
                }
                BndX::Quant(quant, binders, ts) => {
                    let binders =
                        subst_rename_binders(&bnd.span, substs, free_vars, binders, ft, ft);
                    BndX::Quant(*quant, binders, ftrigs(substs, free_vars, ts))
                }
                BndX::Lambda(binders, ts) => {
                    let binders =
                        subst_rename_binders(&bnd.span, substs, free_vars, binders, ft, ft);
                    BndX::Lambda(binders, ftrigs(substs, free_vars, ts))
                }
                BndX::Choose(binders, ts, cond) => {
                    let binders =
                        subst_rename_binders(&bnd.span, substs, free_vars, binders, ft, ft);
                    let cond = subst_exp_rec(typ_substs, substs, free_vars, cond);
                    BndX::Choose(binders, ftrigs(substs, free_vars, ts), cond)
                }
            };
            let bnd = Spanned::new(bnd.span.clone(), bndx);
            let e1 = subst_exp_rec(typ_substs, substs, free_vars, e1);
            substs.pop_scope();
            free_vars.pop_scope();
            SpannedTyped::new(&exp.span, &typ, ExpX::Bind(bnd, e1))
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

    let mut scope_substs: ScopeMap<UniqueIdent, Exp> = ScopeMap::new();
    let mut free_vars: ScopeMap<UniqueIdent, ()> = ScopeMap::new();
    scope_substs.push_scope(false);
    free_vars.push_scope(false);
    for (x, v) in substs {
        scope_substs.insert(x.clone(), v.clone()).expect("subst_exp scope_substs.insert");
        for (y, _) in free_vars_exp(v) {
            let _ = free_vars.insert(y.clone(), ());
        }
    }
    let e = subst_exp_rec(&typ_substs, &mut scope_substs, &mut free_vars, exp);
    scope_substs.pop_scope();
    free_vars.pop_scope();
    assert_eq!(scope_substs.num_scopes(), 0);
    assert_eq!(free_vars.num_scopes(), 0);
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
            Arith(o, _) => match o {
                Add | Sub => (30, 30, 31),
                Mul | EuclideanDiv | EuclideanMod => (40, 40, 41),
            },
            Bitwise(o, _) => match o {
                BitXor => (22, 22, 23),
                BitAnd => (24, 24, 25),
                BitOr => (20, 20, 21),
                Shr | Shl => (26, 26, 27),
            },
            StrGetChar => (90, 90, 90),
        }
    }
}

impl ExpX {
    fn to_string_prec(&self, precedence: u32) -> String {
        use ExpX::*;
        let (s, inner_precedence) = match &self {
            Const(c) => match c {
                Constant::Bool(b) => (format!("{}", b), 99),
                Constant::Int(i) => (format!("{}", i), 99),
                Constant::StrSlice(s) => (format!("\"{}\"", s), 99),
                Constant::Char(c) => (format!("'{}'", c), 99),
            },
            Var(id) | VarLoc(id) => (format!("{}", user_local_name(&id.name)), 99),
            VarAt(id, _at) => (format!("old({})", user_local_name(&id.name)), 99),
            Loc(exp) => (format!("{}", exp), 99), // REVIEW: Additional decoration required?
            Call(CallFun::Fun(fun, _) | CallFun::CheckTermination(fun), _, exps) => {
                let args = exps.iter().map(|e| e.to_string()).collect::<Vec<_>>().join(", ");
                (format!("{}({})", fun.path.segments.last().unwrap(), args), 90)
            }
            Call(CallFun::InternalFun(func), _, exps) => {
                let args = exps.iter().map(|e| e.to_string()).collect::<Vec<_>>().join(", ");
                (format!("{:?}({})", func, args), 90)
            }
            NullaryOpr(crate::ast::NullaryOpr::ConstGeneric(_)) => {
                ("const_generic".to_string(), 99)
            }
            NullaryOpr(crate::ast::NullaryOpr::TraitBound(..)) => ("trait_bound".to_string(), 99),
            Unary(op, exp) => match op {
                UnaryOp::Not | UnaryOp::BitNot => (format!("!{}", exp.x.to_string_prec(99)), 90),
                UnaryOp::Clip { .. } => (format!("clip({})", exp), 99),
                UnaryOp::HeightTrigger => (format!("height_trigger({})", exp), 99),
                UnaryOp::StrLen => (format!("{}.len()", exp.x.to_string_prec(99)), 90),
                UnaryOp::StrIsAscii => (format!("{}.is_ascii()", exp.x.to_string_prec(99)), 90),
                UnaryOp::CharToInt => (format!("{} as char", exp.x.to_string_prec(99)), 90),
                UnaryOp::Trigger(..) | UnaryOp::CoerceMode { .. } | UnaryOp::MustBeFinalized => {
                    ("".to_string(), 0)
                }
            },
            UnaryOpr(op, exp) => {
                use crate::ast::UnaryOpr::*;
                match op {
                    Box(_) => (format!("box({})", exp), 99),
                    Unbox(_) => (format!("unbox({})", exp), 99),
                    HasType(t) => (format!("{}.has_type({:?})", exp, t), 99),
                    IntegerTypeBound(kind, mode) => (format!("{:?}.{:?}({})", kind, mode, exp), 99),
                    IsVariant { datatype: _, variant } => {
                        (format!("{}.is_type({})", exp, variant), 99)
                    }
                    TupleField { tuple_arity: _, field } => (format!("{}.{}", exp, field), 99),
                    Field(field) => (format!("{}.{}", exp, field.field), 99),
                    CustomErr(_msg) => (format!("with_diagnostic({})", exp), 99),
                }
            }
            Binary(op, e1, e2) => {
                let (prec_exp, prec_left, prec_right) = op.prec_of_binary_op();
                use ArithOp::*;
                use BinaryOp::*;
                use BitwiseOp::*;
                use InequalityOp::*;
                let left = e1.x.to_string_prec(prec_left);
                let right = e2.x.to_string_prec(prec_right);
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
                    Arith(o, _) => match o {
                        Add => "+",
                        Sub => "-",
                        Mul => "*",
                        EuclideanDiv => "/",
                        EuclideanMod => "%",
                    },
                    Bitwise(o, _) => match o {
                        BitXor => "^",
                        BitAnd => "&",
                        BitOr => "|",
                        Shr => ">>",
                        Shl => "<<",
                    },
                    StrGetChar => "ignored", // This is our only non-inline BinaryOp, so it needs special handling below
                };
                if let BinaryOp::StrGetChar = op {
                    (format!("{}.get_char({})", left, e2), prec_exp)
                } else if let HeightCompare { .. } = op {
                    (format!("height_compare({left}, {right})"), prec_exp)
                } else {
                    (format!("{} {} {}", left, op_str, right), prec_exp)
                }
            }
            BinaryOpr(crate::ast::BinaryOpr::ExtEq(..), e1, e2) => {
                (format!("ext_eq({}, {})", e1.x.to_string(), e2.x.to_string()), 99)
            }
            If(e1, e2, e3) => (format!("if {} {{ {} }} else {{ {} }}", e1, e2, e3), 99),
            Bind(bnd, exp) => {
                let s = match &bnd.x {
                    BndX::Let(bnds) => {
                        let assigns = bnds
                            .iter()
                            .map(|b| format!("{} = {}", user_local_name(&b.name), b.a))
                            .collect::<Vec<_>>()
                            .join(", ");
                        format!("let {} in {}", assigns, exp)
                    }
                    BndX::Quant(Quant { quant: q, .. }, bnds, _trigs) => {
                        let q_str = match q {
                            air::ast::Quant::Forall => "forall",
                            air::ast::Quant::Exists => "exists",
                        };
                        let vars = bnds
                            .iter()
                            .map(|b| format!("{}", user_local_name(&b.name)))
                            .collect::<Vec<_>>()
                            .join(", ");

                        format!("({} |{}| {})", q_str, vars, exp)
                    }
                    BndX::Lambda(bnds, _trigs) => {
                        let assigns = bnds
                            .iter()
                            .map(|b| format!("{}", user_local_name(&b.name)))
                            .collect::<Vec<_>>()
                            .join(", ");
                        format!("(|{}| {})", assigns, exp)
                    }
                    BndX::Choose(bnds, _trigs, cond) => {
                        let vars = bnds
                            .iter()
                            .map(|b| format!("{}", user_local_name(&b.name)))
                            .collect::<Vec<_>>()
                            .join(", ");
                        format!("(choose |{}| {}, {})", vars, cond, exp)
                    }
                };
                (s, 99)
            }
            Ctor(_path, id, bnds) => {
                let args = bnds.iter().map(|b| b.a.to_string()).collect::<Vec<_>>().join(", ");
                (format!("{}({})", id, args), 99)
            }
            CallLambda(_typ, e, args) => {
                let args = args.iter().map(|e| e.to_string()).collect::<Vec<_>>().join(", ");
                (format!("{}({})", e, args), 99)
            }
            Interp(e) => {
                use InterpExp::*;
                match e {
                    FreeVar(id) => (format!("{}", user_local_name(&id.name)), 99),
                    Seq(s) => {
                        let v = s.iter().map(|e| e.to_string()).collect::<Vec<_>>().join(", ");
                        (format!("[{}]", v), 99)
                    }
                    Closure(e, _ctx) => (format!("{}", e), 99),
                }
            }
            Old(..) | WithTriggers(..) => ("".to_string(), 99), // We don't show the user these internal expressions
        };
        if precedence <= inner_precedence { s } else { format!("({})", s) }
    }
}

impl fmt::Display for ExpX {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self.to_string_prec(5))
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

pub fn bitwidth_sst_from_typ(span: &Span, t: &Typ, arch: &ArchWordBits) -> Exp {
    let bitwidth = crate::ast_util::bitwidth_from_type(t)
        .expect("bitwidth_sst_from_typ expects bounded integer type");
    match bitwidth.to_exact(arch) {
        Some(w) => sst_int_literal(span, w as i128),
        None => sst_arch_word_bits(span),
    }
}

fn chain_binary(span: &Span, op: BinaryOp, init: &Exp, exps: &Vec<Exp>) -> Exp {
    let mut exp = init.clone();
    for e in exps.iter() {
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

pub fn sst_lt(span: &Span, e1: &Exp, e2: &Exp) -> Exp {
    let op = BinaryOp::Inequality(InequalityOp::Lt);
    SpannedTyped::new(span, &Arc::new(TypX::Bool), ExpX::Binary(op, e1.clone(), e2.clone()))
}

pub fn sst_le(span: &Span, e1: &Exp, e2: &Exp) -> Exp {
    let op = BinaryOp::Inequality(InequalityOp::Le);
    SpannedTyped::new(span, &Arc::new(TypX::Bool), ExpX::Binary(op, e1.clone(), e2.clone()))
}

pub fn sst_int_literal(span: &Span, i: i128) -> Exp {
    SpannedTyped::new(
        span,
        &Arc::new(TypX::Int(IntRange::Int)),
        ExpX::Const(crate::ast_util::const_int_from_i128(i)),
    )
}
