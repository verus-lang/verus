#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SM<Span, Ident, Func, Expr, Ty> {
    pub name: Ident,
    // TODO generic args
    pub fields: Vec<Field<Ident, Ty>>,
    pub transitions: Vec<Transition<Span, Ident, Expr, Ty>>,
    pub invariants: Vec<Invariant<Func>>,
    pub lemmas: Vec<Lemma<Ident, Func>>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Extras<Ident, Func> {
    pub name: Ident,
    pub invariants: Vec<Invariant<Func>>,
    pub lemmas: Vec<Lemma<Ident, Func>>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Field<Ident, Ty> {
    pub ident: Ident,
    pub stype: ShardableType<Ty>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Arg<Ident, Ty> {
    pub ident: Ident,
    pub ty: Ty,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ShardableType<Ty> {
    Variable(Ty),
    // TODO more here
}

#[derive(Clone, Debug, PartialEq, Eq, Copy)]
pub enum TransitionKind {
    Init,
    Transition,
    Readonly,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Transition<Span, Ident, Expr, Ty> {
    pub name: Ident,
    pub kind: TransitionKind,
    pub args: Vec<Arg<Ident, Ty>>,
    pub body: TransitionStmt<Span, Ident, Expr>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TransitionStmt<Span, Ident, Expr> {
    Block(Span, Vec<TransitionStmt<Span, Ident, Expr>>),
    Let(Span, Ident, Expr),
    If(Span, Expr, Box<TransitionStmt<Span, Ident, Expr>>, Box<TransitionStmt<Span, Ident, Expr>>),
    Require(Span, Expr),
    Assert(Span, Expr),
    Update(Span, Ident, Expr),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Invariant<Func> {
    pub func: Func,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub enum LemmaPurposeKind {
    PreservesInvariant,
    SatisfiesAsserts,
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct LemmaPurpose<Ident> {
    pub transition: Ident,
    pub kind: LemmaPurposeKind,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Lemma<Ident, Func> {
    pub purpose: LemmaPurpose<Ident>,
    pub func: Func,
}
