use crate::messages::Message;
use indexmap::IndexMap;
use serde::{Deserialize, Serialize};
use std::collections::HashMap;
use std::sync::Arc;

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

/// These are Z3 special relations x <= y that are documented at
/// https://microsoft.github.io/z3guide/docs/theories/Special%20Relations/
#[derive(Copy, Clone, Debug, Serialize, Deserialize, PartialEq, Eq, Hash)]
pub enum Relation {
    /// reflexive, transitive, antisymmetric
    PartialOrder,
    /// reflexive, transitive, antisymmetric, and for all x, y. (x <= y or y <= x)
    LinearOrder,
    /// reflexive, transitive, antisymmetric, and for all x, y, z. (y <= x and z <= x) ==> (y <= z or z <= y)
    TreeOrder,
    /// reflexive, transitive, antisymmetric, and:
    /// - for all x, y, z. (x <= y and x <= z) ==> (y <= z or z <= y)
    /// - for all x, y, z. (y <= x and z <= x) ==> (y <= z or z <= y)
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
    /// Z3 special relations (see Relation above)
    /// The u64 is the Z3 unique name ("index") for each relation that the user wants
    /// ("To create a different relation that is also a partial order use a different index,
    /// such as (_ partial-order 1)", according to
    /// https://microsoft.github.io/z3guide/docs/theories/Special%20Relations/ .)
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

pub type Trigger<M> = Exprs<M>;
pub type Triggers<M> = Arc<Vec<Trigger<M>>>;

pub type Qid = Option<Ident>;

pub type Bind<M> = Arc<BindX<M>>;
#[derive(Clone, Debug, Serialize, Deserialize)]
pub enum BindX<M: Message> {
    Let(Binders<Expr<M>>),
    Quant(Quant, Binders<Typ>, Triggers<M>, Qid),
    Lambda(Binders<Typ>, Triggers<M>, Qid),
    // choose Binders s.t. Expr is true
    Choose(Binders<Typ>, Triggers<M>, Qid, Expr<M>),
}

pub type Expr<M> = Arc<ExprX<M>>;
pub type Exprs<M> = Arc<Vec<Expr<M>>>;
#[derive(Debug, Serialize, Deserialize)]
pub enum ExprX<M: Message> {
    Const(Constant),
    Var(Ident),
    // Old(snap, x) reads x from snapshot snap
    Old(Ident, Ident),
    Apply(Ident, Exprs<M>),
    // ApplyLambda applies function Expr to arguments Exprs, returning a value of type Typ
    ApplyLambda(Typ, Expr<M>, Exprs<M>),
    Unary(UnaryOp, Expr<M>),
    Binary(BinaryOp, Expr<M>, Expr<M>),
    Multi(MultiOp, Exprs<M>),
    IfElse(Expr<M>, Expr<M>, Expr<M>),
    Bind(Bind<M>, Expr<M>),
    // Sometimes an axiom will have additional error messages. If an assert fails
    // and this axiom was relevant, then we append the error labels to the Message.
    LabeledAxiom(Vec<M::MessageLabel>, Expr<M>),
    LabeledAssertion(M, Expr<M>),
}

pub type Stmt<M> = Arc<StmtX<M>>;
pub type Stmts<M> = Arc<Vec<Stmt<M>>>;
#[derive(Debug, Serialize, Deserialize)]
pub enum StmtX<M: Message> {
    Assume(Expr<M>),
    Assert(M, Expr<M>),
    Havoc(Ident),
    Assign(Ident, Expr<M>),
    // create a named snapshot of the state of the variables
    Snapshot(Ident),
    // verify Stmt, but block assumptions in Stmt from persisting after Stmt
    DeadEnd(Stmt<M>),
    Block(Stmts<M>),
    Switch(Stmts<M>),
}

pub type Field = Binder<Typ>;
pub type Fields = Binders<Typ>;
pub type Variant = Binder<Fields>;
pub type Variants = Binders<Fields>;
pub type Datatype = Binder<Variants>;
pub type Datatypes = Binders<Variants>;

pub type Decl<M> = Arc<DeclX<M>>;
pub type Decls<M> = Arc<Vec<Decl<M>>>;
#[derive(Debug, Serialize, Deserialize)]
pub enum DeclX<M: Message> {
    Sort(Ident),
    Datatypes(Datatypes),
    Const(Ident, Typ),
    Fun(Ident, Typs, Typ),
    Var(Ident, Typ),
    Axiom(Expr<M>),
}

pub type Query<M> = Arc<QueryX<M>>;
#[derive(Debug, Serialize, Deserialize)]
pub struct QueryX<M: Message> {
    pub local: Decls<M>,    // local declarations
    pub assertion: Stmt<M>, // checked by SMT with global and local declarations
}

pub type Command<M> = Arc<CommandX<M>>;
pub type Commands<M> = Arc<Vec<Command<M>>>;
#[derive(Debug, Serialize, Deserialize)]
pub enum CommandX<M: Message> {
    Push,                    // push space for temporary global declarations
    Pop,                     // pop temporary global declarations
    SetOption(Ident, Ident), // set-option option value (no colon on the option)
    Global(Decl<M>),         // global declarations
    CheckValid(Query<M>), // SMT check-sat (reporting validity rather than satisfiability), Possibly singular checks
}
