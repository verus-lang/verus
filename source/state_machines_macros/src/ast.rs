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
    Optional(Type),
    StorageOptional(Type),
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
pub enum SpecialOp {
    AddElement(Expr),
    RemoveElement(Expr),
    HaveElement(Expr),

    AddSome(Expr),
    RemoveSome(Expr),
    HaveSome(Expr),

    DepositSome(Expr),
    WithdrawSome(Expr),
    GuardSome(Expr),
}

#[derive(Clone, Debug)]
pub enum TransitionStmt {
    Block(Span, Vec<TransitionStmt>),
    Let(Span, Ident, Expr),
    If(Span, Expr, Box<TransitionStmt>, Box<TransitionStmt>),
    Require(Span, Expr),
    Assert(Span, Expr),
    Update(Span, Ident, Expr),

    /// concurrent-state-machine-specific stuff
    Special(Span, Ident, SpecialOp),

    /// used internally by concurrency_tokens.rs
    /// Different than an Assert - this expression is allowed to depend on output values
    PostCondition(Span, Expr),
}

impl SpecialOp {
    pub fn statement_name(&self) -> &'static str {
        match self {
            SpecialOp::RemoveElement(..) => "remove_element",
            SpecialOp::HaveElement(..) => "have_element",
            SpecialOp::AddElement(..) => "add_element",
            SpecialOp::RemoveSome(..) => "remove_some",
            SpecialOp::HaveSome(..) => "have_some",
            SpecialOp::AddSome(..) => "add_some",
            SpecialOp::DepositSome(..) => "deposit_some",
            SpecialOp::WithdrawSome(..) => "withdraw_some",
            SpecialOp::GuardSome(..) => "guard_some",
        }
    }

    pub fn is_modifier(&self) -> bool {
        match self {
            SpecialOp::RemoveElement(..) => true,
            SpecialOp::HaveElement(..) => false,
            SpecialOp::AddElement(..) => true,
            SpecialOp::RemoveSome(..) => true,
            SpecialOp::HaveSome(..) => false,
            SpecialOp::AddSome(..) => true,
            SpecialOp::DepositSome(..) => true,
            SpecialOp::WithdrawSome(..) => true,
            SpecialOp::GuardSome(..) => false,
        }
    }

    pub fn is_only_allowed_in_readonly(&self) -> bool {
        match self {
            SpecialOp::RemoveElement(..) => false,
            SpecialOp::HaveElement(..) => false,
            SpecialOp::AddElement(..) => false,
            SpecialOp::RemoveSome(..) => false,
            SpecialOp::HaveSome(..) => false,
            SpecialOp::AddSome(..) => false,
            SpecialOp::DepositSome(..) => false,
            SpecialOp::WithdrawSome(..) => false,
            SpecialOp::GuardSome(..) => true,
        }
    }
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
            TransitionStmt::Special(span, _, _) => span,
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
            TransitionStmt::Special(_, _, op) => op.statement_name(),
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

impl ShardableType {
    pub fn strategy_name(&self) -> &str {
        match self {
            ShardableType::Variable(_) => "variable",
            ShardableType::Constant(_) => "constant",
            ShardableType::NotTokenized(_) => "not_tokenized",
            ShardableType::Multiset(_) => "multiset",
            ShardableType::Optional(_) => "option",
            ShardableType::StorageOptional(_) => "storage_option",
        }
    }

    pub fn is_storage(&self) -> bool {
        match self {
            ShardableType::Variable(_) => false,
            ShardableType::Constant(_) => false,
            ShardableType::NotTokenized(_) => false,
            ShardableType::Multiset(_) => false,
            ShardableType::Optional(_) => false,
            ShardableType::StorageOptional(_) => true,
        }
    }
}
