use crate::def::Spanned;
use air::ast::Quant;
use std::rc::Rc;

pub use air::ast::{Binder, Binders};

pub type VirErr = Rc<Spanned<VirErrX>>;
#[derive(Clone, Debug)]
pub enum VirErrX {
    Str(String),
}

pub type Ident = Rc<String>;
pub type Idents = Rc<Vec<Ident>>;
pub type Path = Rc<Vec<Ident>>;

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum Mode {
    Spec,
    Proof,
    Exec,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum IntRange {
    Int,
    Nat,
    U(u32), // number of bits
    I(u32), // number of bits
    USize,
    ISize,
}

pub type Typ = Rc<TypX>;
pub type Typs = Rc<Vec<Typ>>;
// Deliberately not marked Eq -- use explicit match instead, so we know where types are compared
#[derive(Debug)]
pub enum TypX {
    Bool,
    Int(IntRange),
    Path(Path),
    TypParam(Ident),
}

#[derive(Copy, Clone, Debug)]
pub enum UnaryOp {
    Not,
    Trigger(Option<u64>), // mark an expression as a member of a quantifier trigger group
    Clip(IntRange),       // force integer value into range given by IntRange (e.g. by using mod)
}

#[derive(Clone, Debug)]
pub enum UnaryOpr {
    Box(Typ),   // coerce Typ --> boxed
    Unbox(Typ), // coerce boxed --> Typ
}

#[derive(Copy, Clone, Debug)]
pub enum BinaryOp {
    And,
    Or,
    Implies,
    Eq,
    Ne,
    Le,
    Ge,
    Lt,
    Gt,
    Add,
    Sub,
    Mul,
    EuclideanDiv,
    EuclideanMod,
}

pub type HeaderExpr = Rc<HeaderExprX>;
#[derive(Debug)]
pub enum HeaderExprX {
    Requires(Exprs),
    Ensures(Option<(Ident, Typ)>, Exprs),
    Invariant(Exprs),
    Decreases(Expr, Typ),
    Hide(Ident),
}

#[derive(Clone, Debug)]
pub enum Constant {
    Bool(bool),
    Nat(Rc<String>),
}

pub type Expr = Rc<Spanned<ExprX>>;
pub type Exprs = Rc<Vec<Expr>>;
#[derive(Debug)]
pub enum ExprX {
    Const(Constant),
    Var(Ident),
    Call(Ident, Typs, Exprs),
    Ctor(Path, Ident, Binders<Expr>),
    Field { lhs: Expr, datatype_name: Ident, field_name: Ident },
    Unary(UnaryOp, Expr),
    UnaryOpr(UnaryOpr, Expr),
    Binary(BinaryOp, Expr, Expr),
    Quant(Quant, Binders<Typ>, Expr),
    Assign(Expr, Expr),
    Fuel(Ident, u32),
    Header(HeaderExpr),
    Admit,
    If(Expr, Expr, Option<Expr>),
    While { cond: Expr, body: Expr, invs: Exprs },
    Block(Stmts, Option<Expr>),
}

pub type Stmt = Rc<Spanned<StmtX>>;
pub type Stmts = Rc<Vec<Stmt>>;
#[derive(Debug)]
pub enum StmtX {
    Expr(Expr),
    Decl { param: Param, mutable: bool, init: Option<Expr> },
}

pub type Param = Rc<Spanned<ParamX>>;
pub type Params = Rc<Vec<Param>>;
#[derive(Debug)]
pub struct ParamX {
    pub name: Ident,
    pub typ: Typ,
    pub mode: Mode,
}

pub type Function = Rc<Spanned<FunctionX>>;
#[derive(Debug, Clone)]
pub struct FunctionX {
    pub name: Ident,
    pub mode: Mode,
    pub fuel: u32,
    pub typ_params: Idents,
    pub params: Params,
    pub ret: Option<(Ident, Typ, Mode)>,
    pub require: Exprs,
    pub ensure: Exprs,
    pub decrease: Option<(Expr, Typ)>,
    pub hidden: Idents,
    pub body: Option<Expr>,
}

pub type Field = Binder<(Typ, Mode)>;
pub type Fields = Binders<(Typ, Mode)>;
pub type Variant = Binder<Fields>;
pub type Variants = Binders<Fields>;

#[derive(Debug)]
pub struct DatatypeX {
    pub path: Path,
    pub variants: Variants,
}
pub type Datatype = Rc<Spanned<DatatypeX>>;
pub type Datatypes = Vec<Datatype>;

pub type Krate = Rc<KrateX>;
#[derive(Debug, Default)]
pub struct KrateX {
    pub functions: Vec<Function>,
    pub datatypes: Vec<Datatype>,
}
