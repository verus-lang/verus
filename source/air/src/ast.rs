use crate::errors::{Error, ErrorLabels};
use std::collections::HashMap;
use std::sync::Arc;

pub type RawSpan = Arc<dyn std::any::Any + std::marker::Sync + std::marker::Send>;
#[derive(Clone)] // for Debug, see ast_util
pub struct Span {
    pub raw_span: RawSpan,
    pub as_string: String, // if we can't print (description, raw_span), print as_string instead
}

pub type TypeError = String;

pub type Ident = Arc<String>;

pub(crate) type Snapshot = HashMap<Ident, u32>;
pub(crate) type Snapshots = HashMap<Ident, Snapshot>;

pub type Typ = Arc<TypX>;
pub type Typs = Arc<Vec<Typ>>;
#[derive(Debug, PartialEq, Eq, Hash)]
pub enum TypX {
    Bool,
    Int,
    // Lambda deliberately omits argument, return types to make box/unbox for generics easier
    Lambda,
    Named(Ident),
    BitVec(u32),
}

#[derive(Clone, PartialEq, Eq, Hash)] // for Debug, see ast_util
pub enum Constant {
    Bool(bool),
    Nat(Arc<String>),
    BitVec(Arc<String>, u32),
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum UnaryOp {
    Not,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum BinaryOp {
    Implies,
    Eq,
    Le,
    Ge,
    Lt,
    Gt,
    EuclideanDiv,
    EuclideanMod,

    BitXor,
    BitAnd,
    BitOr,
    BitAdd,
    BitSub,
    BitMul,
    BitUDiv,
    BitULt,
    BitUGt,
    BitULe,
    BitUGe,
    BitUMod,
    LShr,
    Shl,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum MultiOp {
    And,
    Or,
    Add,
    Sub,
    Mul,
    Distinct,
}

pub type Binder<A> = Arc<BinderX<A>>;
pub type Binders<A> = Arc<Vec<Binder<A>>>;
#[derive(Clone)] // for Debug, see ast_util
pub struct BinderX<A: Clone> {
    pub name: Ident,
    pub a: A,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub enum Quant {
    Forall,
    Exists,
}

pub type Trigger = Exprs;
pub type Triggers = Arc<Vec<Trigger>>;

pub type Bind = Arc<BindX>;
#[derive(Clone, Debug)]
pub enum BindX {
    Let(Binders<Expr>),
    Quant(Quant, Binders<Typ>, Triggers),
    Lambda(Binders<Typ>),
    Choose(Binder<Typ>, Triggers),
}

pub type Expr = Arc<ExprX>;
pub type Exprs = Arc<Vec<Expr>>;
#[derive(Debug)]
pub enum ExprX {
    Const(Constant),
    Var(Ident),
    // Old(snap, x) reads x from snapshot snap
    Old(Ident, Ident),
    Apply(Ident, Exprs),
    // ApplyLambda applies function Expr to arguments Exprs, returning a value of type Typ
    ApplyLambda(Typ, Expr, Exprs),
    Unary(UnaryOp, Expr),
    Binary(BinaryOp, Expr, Expr),
    Multi(MultiOp, Exprs),
    IfElse(Expr, Expr, Expr),
    Bind(Bind, Expr),
    // Sometimes an axiom will have additional error messages. If an assert fails
    // and this axiom was relevant, then we append the error labels to the Error.
    LabeledAxiom(ErrorLabels, Expr),
    LabeledAssertion(Error, Expr),
}

pub type Stmt = Arc<StmtX>;
pub type Stmts = Arc<Vec<Stmt>>;
#[derive(Debug)]
pub enum StmtX {
    Assume(Expr),
    Assert(Error, Expr),
    Havoc(Ident),
    Assign(Ident, Expr),
    // create a named snapshot of the state of the variables
    Snapshot(Ident),
    // verify Stmt, but block assumptions in Stmt from persisting after Stmt
    DeadEnd(Stmt),
    Block(Stmts),
    Switch(Stmts),
}

pub type Field = Binder<Typ>;
pub type Fields = Binders<Typ>;
pub type Variant = Binder<Fields>;
pub type Variants = Binders<Fields>;
pub type Datatype = Binder<Variants>;
pub type Datatypes = Binders<Variants>;

pub type Decl = Arc<DeclX>;
pub type Decls = Arc<Vec<Decl>>;
#[derive(Debug)]
pub enum DeclX {
    Sort(Ident),
    Datatypes(Datatypes),
    Const(Ident, Typ),
    Fun(Ident, Typs, Typ),
    Var(Ident, Typ),
    Axiom(Expr),
}

pub type Query = Arc<QueryX>;
#[derive(Debug)]
pub struct QueryX {
    pub local: Decls,    // local declarations
    pub assertion: Stmt, // checked by SMT with global and local declarations
}

pub type Command = Arc<CommandX>;
pub type Commands = Arc<Vec<Command>>;
#[derive(Debug)]
pub enum CommandX {
    Push,                    // push space for temporary global declarations
    Pop,                     // pop temporary global declarations
    SetOption(Ident, Ident), // set-option option value (no colon on the option)
    Global(Decl),            // global declarations
    CheckValid(Query),       // SMT check-sat (reporting validity rather than satisfiability)
}
