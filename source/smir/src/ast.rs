#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SM<Func, Expr, Ty> {
    pub name: String,
    // TODO generic args
    pub fields: Vec<Field<Ty>>,
    pub transitions: Vec<Transition<Expr, Ty>>,
    pub invariants: Vec<Invariant<Func>>,
    pub lemmas: Vec<Lemma<Func>>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Extras<Func> {
    pub name: String,
    pub invariants: Vec<Invariant<Func>>,
    pub lemmas: Vec<Lemma<Func>>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Field<Ty> {
    pub ident: String,
    pub stype: ShardableType<Ty>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Arg<Ty> {
    pub ident: String,
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
pub struct Transition<Expr, Ty> {
    pub kind: TransitionKind,
    pub args: Vec<Arg<Ty>>,
    pub body: TransitionStmt<Expr>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TransitionStmt<Expr> {
    Block(Vec<TransitionStmt<Expr>>),
    Let(String, Expr),
    If(Expr, Box<TransitionStmt<Expr>>, Box<TransitionStmt<Expr>>),
    Require(Expr),
    Assert(Expr),
    Update(String, Expr),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Invariant<Func> {
    pub func: Func,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LemmaPurpose {
    pub transition: String,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Lemma<Func> {
    pub purpose: LemmaPurpose,
    pub func: Func,
}
