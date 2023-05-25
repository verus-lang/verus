use crate::messages::{Message, MessageLabels};
use indexmap::IndexMap;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::sync::Arc;

pub type RawSpan = Arc<dyn std::any::Any + std::marker::Sync + std::marker::Send>;
pub type AstId = u64;
#[derive(Clone, Serialize, Deserialize)] // for Debug, see ast_util
pub struct Span {
    #[serde(skip)]
    #[serde(default = "crate::ast_util::empty_raw_span")]
    pub raw_span: RawSpan,
    pub id: AstId, // arbitrary integer identifier that may be set and used in any way (e.g. as unique id, or just left as 0)
    pub data: Vec<u64>, // arbitrary integers (e.g. for serialization/deserialization)
    pub as_string: String, // if we can't print (description, raw_span), print as_string instead
}

pub type TypeError = String;

pub type Ident = Arc<String>;

pub(crate) type Snapshot = IndexMap<Ident, u32>;
pub(crate) type Snapshots = HashMap<Ident, Snapshot>;

pub type Typ = Arc<TypX>;
pub type Typs = Arc<Vec<Typ>>;
#[derive(Debug, Serialize, Deserialize, PartialEq, Eq, Hash)]
pub enum TypX {
    Bool,
    Int,
    // Lambda deliberately omits argument, return types to make box/unbox for generics easier
    Lambda,
    Named(Ident),
    BitVec(u32),
}

#[derive(Clone, Serialize, Deserialize, PartialEq, Eq, Hash)] // for Debug, see ast_util
pub enum Constant {
    Bool(bool),
    Nat(Arc<String>),
    BitVec(Arc<String>, u32),
}

#[derive(Copy, Clone, Debug, Serialize, Deserialize, PartialEq, Eq, Hash)]
pub enum UnaryOp {
    Not,
    BitNot,
    BitExtract(u32, u32),
}

#[derive(Copy, Clone, Debug, Serialize, Deserialize, PartialEq, Eq, Hash)]
pub enum Relation {
    PartialOrder,
    LinearOrder,
    TreeOrder,
    PiecewiseLinearOrder,
}

#[derive(Copy, Clone, Debug, Serialize, Deserialize, PartialEq, Eq, Hash)]
pub enum BinaryOp {
    Implies,
    Eq,
    Le,
    Ge,
    Lt,
    Gt,
    EuclideanDiv,
    EuclideanMod,
    Relation(Relation, u64),
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
    BitConcat,
}

#[derive(Copy, Clone, Debug, Serialize, Deserialize, PartialEq, Eq, Hash)]
pub enum MultiOp {
    And,
    Or,
    Xor,
    Add,
    Sub,
    Mul,
    Distinct,
}

pub type Binder<A> = Arc<BinderX<A>>;
pub type Binders<A> = Arc<Vec<Binder<A>>>;
#[derive(Clone, Serialize, Deserialize)] // for Debug, see ast_util
pub struct BinderX<A: Clone> {
    pub name: Ident,
    pub a: A,
}

#[derive(Copy, Clone, Debug, Serialize, Deserialize, PartialEq, Eq, Hash)]
pub enum Quant {
    Forall,
    Exists,
}

pub type Trigger = Exprs;
pub type Triggers = Arc<Vec<Trigger>>;

pub type Qid = Option<Ident>;

pub type Bind = Arc<BindX>;
#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum BindX {
    Let(Binders<Expr>),
    Quant(Quant, Binders<Typ>, Triggers, Qid),
    Lambda(Binders<Typ>, Triggers, Qid),
    // choose Binders s.t. Expr is true
    Choose(Binders<Typ>, Triggers, Qid, Expr),
}

pub type Expr = Arc<ExprX>;
pub type Exprs = Arc<Vec<Expr>>;
#[derive(Debug, Serialize, Deserialize)]
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
    // and this axiom was relevant, then we append the error labels to the Message.
    LabeledAxiom(MessageLabels, Expr),
    LabeledAssertion(Message, Expr),
}

pub type Stmt = Arc<StmtX>;
pub type Stmts = Arc<Vec<Stmt>>;
#[derive(Debug, Serialize, Deserialize)]
pub enum StmtX {
    Assume(Expr),
    Assert(Message, Expr),
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
#[derive(Debug, Serialize, Deserialize)]
pub enum DeclX {
    Sort(Ident),
    Datatypes(Datatypes),
    Const(Ident, Typ),
    Fun(Ident, Typs, Typ),
    Var(Ident, Typ),
    Axiom(Expr),
}

pub type Query = Arc<QueryX>;
#[derive(Debug, Serialize, Deserialize)]
pub struct QueryX {
    pub local: Decls,    // local declarations
    pub assertion: Stmt, // checked by SMT with global and local declarations
}

pub type Command = Arc<CommandX>;
pub type Commands = Arc<Vec<Command>>;
#[derive(Debug, Serialize, Deserialize)]
pub enum CommandX {
    Push,                    // push space for temporary global declarations
    Pop,                     // pop temporary global declarations
    SetOption(Ident, Ident), // set-option option value (no colon on the option)
    Global(Decl),            // global declarations
    CheckValid(Query), // SMT check-sat (reporting validity rather than satisfiability), Possibly singular checks
}
