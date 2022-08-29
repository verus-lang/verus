//! VIR-SST (Statement-oriented Syntax Tree)
//!
//! Rust-AST --> Rust-HIR --> VIR-AST --> VIR-SST --> AIR --> Z3-SMT
//!
//! Whereas VIR-AST supports statements inside expressions,
//! SST expressions cannot contain statments.
//! SST is designed to make the translation to AIR as straightforward as possible.

use crate::ast::{
    ArithOp, AssertQueryMode, BinaryOp, BitwiseOp, Constant, Fun, InequalityOp, InvAtomicity, Mode,
    Path, Quant, SpannedTyped, Typ, Typs, UnaryOp, UnaryOpr, VarAt,
};
use crate::def::Spanned;
use crate::interpreter::InterpExp;
use air::ast::{Binders, Ident, Span};
use air::errors::Error;
use std::fmt;
use std::sync::Arc;

pub type Trig = Exps;
pub type Trigs = Arc<Vec<Trig>>;

pub struct BndInfo {
    pub span: Span,
    pub trigs: Trigs,
}

pub type Bnd = Arc<Spanned<BndX>>;
#[derive(Clone, Debug)]
pub enum BndX {
    Let(Binders<Exp>),
    Quant(Quant, Binders<Typ>, Trigs),
    Lambda(Binders<Typ>),
    Choose(Binders<Typ>, Trigs, Exp),
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct UniqueIdent {
    pub name: Ident,
    // None for bound vars, Some disambiguating integer for local vars
    pub local: Option<u64>,
}

pub type Exp = Arc<SpannedTyped<ExpX>>;
pub type Exps = Arc<Vec<Exp>>;
#[derive(Debug, Clone)]
pub enum ExpX {
    Const(Constant),
    Var(UniqueIdent),
    VarLoc(UniqueIdent),
    VarAt(UniqueIdent, VarAt),
    Loc(Exp),
    // used only during sst_to_air to generate AIR Old
    Old(Ident, UniqueIdent),
    // call to spec function
    Call(Fun, Typs, Exps),
    CallLambda(Typ, Exp, Exps),
    Ctor(Path, Ident, Binders<Exp>),
    Unary(UnaryOp, Exp),
    UnaryOpr(UnaryOpr, Exp),
    Binary(BinaryOp, Exp, Exp),
    If(Exp, Exp, Exp),
    WithTriggers(Trigs, Exp),
    Bind(Bnd, Exp),
    // only used internally by the interpreter; should never be seen outside it
    Interp(InterpExp),
}

#[derive(Debug, Clone, Copy)]
pub enum ParPurpose {
    MutPre,
    MutPost,
    Regular,
}

/// Function parameter
pub type Par = Arc<Spanned<ParX>>;
pub type Pars = Arc<Vec<Par>>;
#[derive(Debug, Clone)]
pub struct ParX {
    pub name: Ident,
    pub typ: Typ,
    pub mode: Mode,
    pub purpose: ParPurpose,
}

#[derive(Clone, Debug)]
pub struct Dest {
    pub dest: Exp,
    pub is_init: bool,
}

pub type Stm = Arc<Spanned<StmX>>;
pub type Stms = Arc<Vec<Stm>>;

#[derive(Debug)]
pub enum StmX {
    // call to exec/proof function (or spec function for checking_recommends)
    Call(Fun, Mode, Typs, Exps, Option<Dest>),
    // note: failed assertion reports Stm's span, plus an optional additional span
    Assert(Option<Error>, Exp),
    AssertBV(Exp),
    Assume(Exp),
    Assign {
        lhs: Dest,
        rhs: Exp,
    },
    Fuel(Fun, u32),
    DeadEnd(Stm),
    If(Exp, Stm, Option<Stm>),
    While {
        cond_stms: Stms,
        cond_exp: Exp,
        body: Stm,
        invs: Exps,
        typ_inv_vars: Arc<Vec<(UniqueIdent, Typ)>>,
        modified_vars: Arc<Vec<UniqueIdent>>,
    },
    OpenInvariant(Exp, UniqueIdent, Typ, Stm, InvAtomicity),
    Block(Stms),
    AssertQuery {
        mode: AssertQueryMode,
        typ_inv_vars: Arc<Vec<(UniqueIdent, Typ)>>,
        body: Stm,
    },
}

pub type LocalDecl = Arc<LocalDeclX>;
#[derive(Debug)]
pub struct LocalDeclX {
    pub ident: UniqueIdent,
    pub typ: Typ,
    pub mutable: bool,
}

// REVIEW: Move this to be an impl of BinaryOp in ast.rs?
// Based on the "Expression precedence" table here:
// https://doc.rust-lang.org/reference/expressions.html
fn prec_of_binary_op(op: BinaryOp) -> (u32, u32, u32) {
    use ArithOp::*;
    use BinaryOp::*;
    use BitwiseOp::*;
    match op {
        And => (8, 9, 9),
        Or => (6, 7, 7),
        Xor => (6, 7, 7), // REVIEW: Rust doesn't have a logical xor, so it's up to us to define this
        Implies => (3, 4, 4),
        Eq(_) | Ne | Inequality(_) => (10, 10, 10),
        Arith(o, _) => match o {
            Add | Sub => (30, 30, 31),
            Mul | EuclideanDiv | EuclideanMod => (40, 40, 41),
        },
        Bitwise(o) => match o {
            BitXor => (22, 22, 23),
            BitAnd => (24, 24, 25),
            BitOr => (20, 20, 21),
            Shr | Shl => (26, 26, 27),
        },
    }
}

impl ExpX {
    fn to_string_prec(&self, precedence: u32) -> String {
        use ExpX::*;
        let (s, inner_precedence) = match &self {
            Const(c) => match c {
                Constant::Bool(b) => (format!("{}", b), 99),
                Constant::Int(i) => (format!("{}", i), 99),
            },
            Var(id) | VarLoc(id) => (format!("{}", id.name), 99),
            VarAt(id, _at) => (format!("old({})", id.name), 99),
            Loc(exp) => (format!("{}", exp), 99), // REVIEW: Additional decoration required?
            Call(fun, _, exps) => {
                let args = exps.iter().map(|e| e.to_string()).collect::<Vec<_>>().join(", ");
                (format!("{}({})", fun.path.segments.last().unwrap(), args), 90)
            }
            Unary(op, exp) => match op {
                UnaryOp::Not | UnaryOp::BitNot => (format!("!{}", exp.x.to_string_prec(99)), 90),
                UnaryOp::Clip(_range) => (format!("clip({})", exp), 99),
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
                    IsVariant { datatype: _, variant } => {
                        (format!("{}.is_type({})", exp, variant), 99)
                    }
                    TupleField { tuple_arity: _, field } => (format!("{}.{}", exp, field), 99),
                    Field(field) => (format!("{}.{}", exp, field.field), 99),
                }
            }
            Binary(op, e1, e2) => {
                let (prec_exp, prec_left, prec_right) = prec_of_binary_op(*op);
                use ArithOp::*;
                use BinaryOp::*;
                use BitwiseOp::*;
                use InequalityOp::*;
                let left = e1.x.to_string_prec(prec_left);
                let right = e2.x.to_string_prec(prec_right);
                let op = match op {
                    And => "&&",
                    Or => "||",
                    Xor => "^",
                    Implies => "==>",
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
                    Bitwise(o) => match o {
                        BitXor => "^",
                        BitAnd => "&",
                        BitOr => "|",
                        Shr => ">>",
                        Shl => "<<",
                    },
                };
                (format!("{} {} {}", left, op, right), prec_exp)
            }
            If(e1, e2, e3) => (format!("if {} {{ {} }} else {{ {} }}", e1, e2, e3), 99),
            Bind(bnd, exp) => {
                let s = match &bnd.x {
                    BndX::Let(bnds) => {
                        let assigns = bnds
                            .iter()
                            .map(|b| format!("{} = {}", b.name, b.a))
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
                            .map(|b| format!("{}", b.name))
                            .collect::<Vec<_>>()
                            .join(", ");

                        format!("({} |{}| {})", q_str, vars, exp)
                    }
                    BndX::Lambda(bnds) => {
                        let assigns = bnds
                            .iter()
                            .map(|b| format!("{}", b.name))
                            .collect::<Vec<_>>()
                            .join(", ");
                        format!("(|{}| {})", assigns, exp)
                    }
                    BndX::Choose(bnds, _trigs, _cond) => {
                        // REVIEW: Where is cond used?  Couldn't find an example syntax
                        let vars = bnds
                            .iter()
                            .map(|b| format!("{}", b.name))
                            .collect::<Vec<_>>()
                            .join(", ");
                        format!("(choose |{}| {})", vars, exp)
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
                    FreeVar(id) => (format!("{}", id.name), 99),
                    Seq(s) => {
                        let v = s.iter().map(|e| e.to_string()).collect::<Vec<_>>().join(", ");
                        (format!("[{}]", v), 99)
                    }
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
