use crate::def::Spanned;
use air::ast::Constant;
use std::rc::Rc;

pub type VirErr = Rc<Spanned<String>>;

pub type Ident = Rc<String>;
pub type Idents = Rc<Vec<Ident>>;

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum Mode {
    Spec,
    Proof,
    Exec,
}

#[derive(Clone, Debug)]
pub enum Typ {
    Bool,
    Int,
    Path(Vec<Ident>),
}

#[derive(Copy, Clone, Debug)]
pub enum UnaryOp {
    Not,
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
    Hide(Ident),
}

pub type Expr = Rc<Spanned<ExprX>>;
pub type Exprs = Rc<Vec<Expr>>;
#[derive(Debug)]
pub enum ExprX {
    Const(Constant),
    Var(Ident),
    Call(Ident, Exprs),
    Field(Expr, Ident),
    Assume(Expr),
    Assert(Expr),
    Unary(UnaryOp, Expr),
    Binary(BinaryOp, Expr, Expr),
    Assign(Expr, Expr),
    Fuel(Ident, u32),
    Header(HeaderExpr),
    Block(Stmts, Option<Expr>),
}

pub type Stmt = Rc<Spanned<StmtX>>;
pub type Stmts = Rc<Vec<Stmt>>;
#[derive(Debug)]
pub enum StmtX {
    Expr(Expr),
    Decl { param: ParamX, mutable: bool },
}

pub type Param = Rc<Spanned<ParamX>>;
pub type Params = Rc<Vec<Param>>;
#[derive(Debug)]
pub struct ParamX {
    pub name: Ident,
    pub typ: Typ,
}

pub type Function = Rc<Spanned<FunctionX>>;
#[derive(Debug, Clone)]
pub struct FunctionX {
    pub name: Ident,
    pub mode: Mode,
    pub fuel: u32,
    pub params: Params,
    pub ret: Option<(Ident, Typ)>,
    pub require: Exprs,
    pub ensure: Exprs,
    pub hidden: Idents,
    pub body: Option<Expr>,
}

pub use air::ast::Binder;
pub use air::ast::Binders;
pub type Field = Binder<Typ>;
pub type Fields = Binders<Typ>;
pub type Variant = Binder<Fields>;
pub type Variants = Binders<Fields>;
pub type Datatype = Rc<Spanned<Binder<Variants>>>;
pub type Datatypes = Vec<Rc<Spanned<Binder<Variants>>>>;

pub type Krate = Rc<KrateX>;
#[derive(Debug, Default)]
pub struct KrateX {
    pub functions: Vec<Function>,
    pub datatypes: Vec<Datatype>,
}
