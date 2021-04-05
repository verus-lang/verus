use crate::def::Spanned;
use air::ast::Const;
use std::rc::Rc;

pub type Ident = Rc<String>;

#[derive(Debug)]
pub enum Typ {
    Bool,
    Int,
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

pub type Expr = Rc<Spanned<ExprX>>;
#[derive(Debug)]
pub enum ExprX {
    Const(Const),
    Var(Ident),
    Assume(Expr),
    Assert(Expr),
    Unary(UnaryOp, Expr),
    Binary(BinaryOp, Expr, Expr),
    Block(Stmts),
}

pub type Stmt = Rc<Spanned<StmtX>>;
pub type Stmts = Rc<Box<[Stmt]>>;
#[derive(Debug)]
pub enum StmtX {
    Expr(Expr),
}

pub type Param = Rc<Spanned<ParamX>>;
pub type Params = Rc<Box<[Param]>>;
#[derive(Debug)]
pub struct ParamX {
    pub name: Ident,
    pub typ: Typ,
}

pub type Function = Rc<Spanned<FunctionX>>;
#[derive(Debug)]
pub struct FunctionX {
    pub params: Params,
    pub body: Expr,
}
