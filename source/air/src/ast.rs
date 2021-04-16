use std::fmt::Debug;
use std::rc::Rc;

pub type RawSpan = Rc<dyn std::any::Any>;
#[derive(Clone)]
pub struct Span {
    pub raw_span: RawSpan,
    pub as_string: String,
}
pub type SpanOption = Rc<Option<Span>>;

impl Debug for Span {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        f.debug_tuple("Span").field(&self.as_string).finish()
    }
}

pub type TypeError = String;

#[derive(Debug)]
pub enum ValidityResult {
    Valid,
    Invalid(SpanOption),
    TypeError(TypeError),
}

pub type Ident = Rc<String>;

pub type Typ = Rc<TypX>;
pub type Typs = Rc<Box<[Typ]>>;
#[derive(Debug)]
pub enum TypX {
    Bool,
    Int,
    Named(Ident),
}

#[derive(Clone, Debug)]
pub enum Const {
    Bool(bool),
    Nat(Rc<String>),
}

#[derive(Copy, Clone, Debug)]
pub enum UnaryOp {
    Not,
}

#[derive(Copy, Clone, Debug)]
pub enum BinaryOp {
    Implies,
    Eq,
    Le,
    Ge,
    Lt,
    Gt,
    EuclideanDiv,
    EuclideanMod,
}

#[derive(Copy, Clone, Debug)]
pub enum MultiOp {
    And,
    Or,
    Add,
    Sub,
    Mul,
}

pub type Binder<A> = Rc<BinderX<A>>;
pub type Binders<A> = Rc<Box<[Binder<A>]>>;
#[derive(Clone, Debug)]
pub struct BinderX<A: Clone> {
    pub name: Ident,
    pub a: A,
}

#[derive(Copy, Clone, Debug)]
pub enum Quant {
    Forall,
    Exists,
}

pub type Trigger = Exprs;
pub type Triggers = Rc<Box<[Trigger]>>;

pub type Bind = Rc<BindX>;
#[derive(Clone, Debug)]
pub enum BindX {
    Let(Binders<Expr>),
    Quant(Quant, Binders<Typ>, Triggers),
}

pub type Expr = Rc<ExprX>;
pub type Exprs = Rc<Box<[Expr]>>;
#[derive(Debug)]
pub enum ExprX {
    Const(Const),
    Var(Ident),
    Apply(Ident, Exprs),
    Unary(UnaryOp, Expr),
    Binary(BinaryOp, Expr, Expr),
    Multi(MultiOp, Exprs),
    Bind(Bind, Expr),
    LabeledAssertion(SpanOption, Expr),
}

pub type Stmt = Rc<StmtX>;
pub type Stmts = Rc<Box<[Stmt]>>;
#[derive(Debug)]
pub enum StmtX {
    Assume(Expr),
    Assert(SpanOption, Expr),
    Assign(Ident, Expr),
    Block(Stmts),
}

pub type Decl = Rc<DeclX>;
pub type Decls = Rc<Box<[Decl]>>;
#[derive(Debug)]
pub enum DeclX {
    Sort(Ident),
    Const(Ident, Typ),
    Fun(Ident, Typs, Typ),
    Var(Ident, Typ),
    Axiom(Expr),
}

pub type Query = Rc<QueryX>;
#[derive(Debug)]
pub struct QueryX {
    pub local: Decls,    // local declarations
    pub assertion: Stmt, // checked by SMT with global and local declarations
}

pub type Command = Rc<CommandX>;
pub type Commands = Rc<Box<[Command]>>;
#[derive(Debug)]
pub enum CommandX {
    Push,                    // push space for temporary global declarations
    Pop,                     // pop temporary global declarations
    SetOption(Ident, Ident), // set-option option value (no colon on the option)
    Global(Decl),            // global declarations
    CheckValid(Query),       // SMT check-sat (reporting validity rather than satisfiability)
}
