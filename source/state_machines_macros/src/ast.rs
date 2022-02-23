use proc_macro2::Span;
use syn::{Expr, FieldsNamed, Generics, Ident, ImplItemMethod, Type};

#[derive(Clone, Debug)]
pub struct SM {
    pub name: Ident,

    pub generics: Option<Generics>,

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
    pub stype: ShardableType,
}

#[derive(Clone, Debug)]
pub struct TransitionParam {
    pub ident: Ident,
    pub ty: Type,
}

#[derive(Clone, Debug)]
pub enum ShardableType {
    Variable(Type),
    Constant(Type),
    NotTokenized(Type),
    Multiset(Type),
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
    pub params: Vec<TransitionParam>,
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

    // concurrent-state-machine-specific stuff
    AddElement(Span, Ident, Expr),
    RemoveElement(Span, Ident, Expr),
    HaveElement(Span, Ident, Expr),

    // used internally by concurrency_tokens.rs
    // Different than an Assert - this expression is allowed to depend on output values
    PostCondition(Span, Expr),
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
            TransitionStmt::AddElement(span, _, _) => span,
            TransitionStmt::RemoveElement(span, _, _) => span,
            TransitionStmt::HaveElement(span, _, _) => span,
            TransitionStmt::PostCondition(span, _) => span,
        }
    }

    pub fn statement_name(&self) -> &'static str {
        match self {
            TransitionStmt::Block(..) => "block",
            TransitionStmt::Let(..) => "let",
            TransitionStmt::If(..) => "if",
            TransitionStmt::Require(..) => "require",
            TransitionStmt::Assert(..) => "assert",
            TransitionStmt::Update(..) => "update",
            TransitionStmt::AddElement(..) => "add_element",
            TransitionStmt::RemoveElement(..) => "remove_element",
            TransitionStmt::HaveElement(..) => "have_element",
            TransitionStmt::PostCondition(..) => "post_condition",
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

impl TransitionStmt {
    pub fn visit_updatelike_stmts<F>(&self, ident: &Ident, f: &mut F)
    where F: FnMut(&TransitionStmt) -> ()
    {
        match self {
            TransitionStmt::Block(_, v) => {
                for t in v.iter() {
                    t.visit_updatelike_stmts(ident, f);
                }
            }
            TransitionStmt::Let(_, _, _) => { }
            TransitionStmt::If(_, _, thn, els) => {
                thn.visit_updatelike_stmts(ident, f);
                els.visit_updatelike_stmts(ident, f);
            }
            TransitionStmt::Require(_, _) => { }
            TransitionStmt::Assert(_, _) => { }
            TransitionStmt::Update(_, id, _) |
            TransitionStmt::AddElement(_, id, _) |
            TransitionStmt::RemoveElement(_, id, _) |
            TransitionStmt::HaveElement(_, id, _) => {
                if id.to_string() == ident.to_string() {
                    f(self);
                }
            }
            TransitionStmt::PostCondition(..) => { }
        }
    }
}

impl ShardableType {
    pub fn strategy_name(&self) -> &str {
        match self {
            ShardableType::Variable(_) => "variable",
            ShardableType::Constant(_) => "constant",
            ShardableType::NotTokenized(_) => "not_tokenized",
            ShardableType::Multiset(_) => "multiset",
        }
    }
}
