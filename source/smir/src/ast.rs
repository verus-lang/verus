#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SM<Ident, Func, Expr, Ty> {
    pub name: Ident,
    // TODO generic args
    pub fields: Vec<Field<Ident, Ty>>,
    pub transitions: Vec<Transition<Ident, Expr, Ty>>,
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
    Init, Transition, Static,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Transition<Ident, Expr, Ty> {
    pub kind: TransitionKind,
    pub args: Vec<Arg<Ident, Ty>>,
    pub body: TransitionStmt<Ident, Expr>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TransitionStmt<Ident, Expr> {
    Block(Vec<TransitionStmt<Ident, Expr>>),
    Let(Ident, Expr, Box<TransitionStmt<Ident, Expr>>),
    If(Expr, Box<TransitionStmt<Ident, Expr>>, Box<TransitionStmt<Ident, Expr>>),
    Require(Expr),
    Assert(Expr),
    Update(Ident, Expr),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Invariant<Func> {
    pub func: Func,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LemmaPurpose<Ident> {
    pub transition: Ident,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Lemma<Ident, Func> {
    pub purpose: LemmaPurpose<Ident>,
    pub func: Func,
}
