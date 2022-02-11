use syn::{Expr, ImplItemMethod, Ident, Type, FieldsNamed};
use proc_macro2::Span;

#[derive(Clone, Debug)]
pub struct SM {
    pub name: Ident,

    // TODO generic args
    pub fields: Vec<Field>,
    pub fields_named_ast: FieldsNamed,

    pub transitions: Vec<Transition>,
}

#[derive(Clone, Debug)]
pub struct Extras {
    pub invariants: Vec<Invariant>,
    pub lemmas: Vec<Lemma>,
}

#[derive(Clone, Debug)]
pub struct Field {
    pub ident: Ident,
    pub stype: ShardableType<Type>,
}

#[derive(Clone, Debug)]
pub struct TransitionParam {
    pub ident: Ident,
    pub ty: Type,
}

#[derive(Clone, Debug)]
pub enum ShardableType<Type> {
    Variable(Type),
    Constant(Type),
    // TODO more here
}

#[derive(Clone, Debug, PartialEq, Eq, Copy)]
pub enum TransitionKind {
    Init,
    Transition,
    Readonly,
}

#[derive(Clone, Debug)]
pub struct Transition {
    pub name: Ident,
    pub kind: TransitionKind,
    pub args: Vec<TransitionParam>,
    pub body: TransitionStmt,
}

#[derive(Clone, Debug)]
pub enum TransitionStmt {
    Block(Span, Vec<TransitionStmt>),
    Let(Span, Ident, Expr),
    If(Span, Expr, Box<TransitionStmt>, Box<TransitionStmt>),
    Require(Span, Expr),
    Assert(Span, Expr),
    Update(Span, Ident, Expr),
}

impl TransitionStmt {
    pub fn get_span<'a>(&'a self) -> &'a Span {
        match self {
            TransitionStmt::Block(span, _) => span,
            TransitionStmt::Let(span, _, _) => span,
            TransitionStmt::If(span, _, _, _) => span,
            TransitionStmt::Require(span, _) => span,
            TransitionStmt::Assert(span, _) => span,
            TransitionStmt::Update(span, _, _) => span,
        }
    }
}

#[derive(Clone, Debug)]
pub struct Invariant {
    pub func: ImplItemMethod,
}

#[derive(Clone, Debug, Hash)]
pub enum LemmaPurposeKind {
    PreservesInvariant,
    SatisfiesAsserts, // TODO remove?
}

#[derive(Clone, Debug, Hash)]
pub struct LemmaPurpose {
    pub transition: Ident,
    pub kind: LemmaPurposeKind,
}

#[derive(Clone, Debug)]
pub struct Lemma {
    pub purpose: LemmaPurpose,
    pub func: ImplItemMethod,
}
