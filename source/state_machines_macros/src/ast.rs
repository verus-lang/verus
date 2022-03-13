use proc_macro2::Span;
use syn::{Expr, FieldsNamed, Generics, Ident, ImplItemMethod, Type};

#[derive(Clone, Debug)]
pub struct SM {
    pub name: Ident,

    pub generics: Option<Generics>,

    pub fields: Vec<Field>,
    pub fields_named_ast: FieldsNamed,

    pub transitions: Vec<Transition>,

    pub concurrent: bool,
}

#[derive(Clone, Debug)]
pub struct Extras {
    pub invariants: Vec<Invariant>,
    pub lemmas: Vec<Lemma>,
}

#[derive(Clone, Debug)]
pub struct Field {
    pub name: Ident,
    pub stype: ShardableType,
    pub type_span: Span,
}

#[derive(Clone, Debug)]
pub struct TransitionParam {
    pub name: Ident,
    pub ty: Type,
}

/// These represent the types of the state machine fields,
/// along with their sharding strategies.
/// (For non-concurrent state machines, we just say everything
/// is 'Variable'.)
///
/// Be aware of the relationship between the enum representation here
/// and the user's field declarations. As an example, a user's declaration
/// might look like `#[sharding(option)] foo: Option<Foo>`.
/// Recall the user is expected to declare a type of a certain form which
/// depends on the sharding strategy; e.g., in `#[sharding(option)]`, the
/// user is required to declare a type of the form `Option<something>`.
///
/// In the representation here, we actually "destruct" user-provided type,
/// and just represent it as `Optional(Foo)` (not `Optional(Option<Foo>)`).
/// This way, we can easily talk about `Foo` directly when necessary,
/// while we can easily reconstruct the user-provided type (see `shardable_type_to_type`).

#[derive(Clone, Debug)]
pub enum ShardableType {
    Variable(Type),
    Constant(Type),
    NotTokenized(Type),
    Multiset(Type),
    Optional(Type),
    StorageOptional(Type),
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

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum LetKind {
    Normal,
    BirdsEye,
}

#[derive(Clone, Debug)]
pub enum TransitionStmt {
    Block(Span, Vec<TransitionStmt>),
    Let(Span, Ident, LetKind, Expr, Box<TransitionStmt>),
    If(Span, Expr, Box<TransitionStmt>, Box<TransitionStmt>),
    Require(Span, Expr),
    Assert(Span, Expr),
    Update(Span, Ident, Expr),
    Initialize(Span, Ident, Expr),

    /// concurrent-state-machine-specific stuff
    Special(Span, Ident, SpecialOp),

    /// Different than an Assert - this statement is allowed to depend on output values.
    /// Used internally by various transformations, both by `concurrency_tokens.rs`
    /// and by `to_relation.rs`.
    /// This cannot be directly constructed by the user.
    PostCondition(Span, Expr),
}

impl SpecialOp {
    /// get the name of an op (for error reporting)
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

    /// returns 'true' if the operational definition of the operation
    /// updates the field value
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
            SpecialOp::RemoveElement(..)
            | SpecialOp::HaveElement(..)
            | SpecialOp::AddElement(..)
            | SpecialOp::RemoveSome(..)
            | SpecialOp::HaveSome(..)
            | SpecialOp::AddSome(..)
            | SpecialOp::DepositSome(..)
            | SpecialOp::WithdrawSome(..) => false,

            SpecialOp::GuardSome(..) => true,
        }
    }

    pub fn is_have(&self) -> bool {
        match self {
            SpecialOp::HaveElement(..) | SpecialOp::HaveSome(..) => true,

            SpecialOp::RemoveElement(..)
            | SpecialOp::AddElement(..)
            | SpecialOp::RemoveSome(..)
            | SpecialOp::AddSome(..)
            | SpecialOp::DepositSome(..)
            | SpecialOp::WithdrawSome(..)
            | SpecialOp::GuardSome(..) => false,
        }
    }

    pub fn is_remove(&self) -> bool {
        match self {
            SpecialOp::RemoveElement(..) | SpecialOp::RemoveSome(..) => true,

            SpecialOp::HaveElement(..)
            | SpecialOp::AddElement(..)
            | SpecialOp::HaveSome(..)
            | SpecialOp::AddSome(..)
            | SpecialOp::DepositSome(..)
            | SpecialOp::WithdrawSome(..)
            | SpecialOp::GuardSome(..) => false,
        }
    }

    pub fn is_add(&self) -> bool {
        match self {
            SpecialOp::AddElement(..) | SpecialOp::AddSome(..) => true,

            SpecialOp::RemoveElement(..)
            | SpecialOp::HaveElement(..)
            | SpecialOp::RemoveSome(..)
            | SpecialOp::HaveSome(..)
            | SpecialOp::DepositSome(..)
            | SpecialOp::WithdrawSome(..)
            | SpecialOp::GuardSome(..) => false,
        }
    }

    pub fn is_guard(&self) -> bool {
        match self {
            SpecialOp::GuardSome(..) => true,

            SpecialOp::AddElement(..)
            | SpecialOp::AddSome(..)
            | SpecialOp::RemoveElement(..)
            | SpecialOp::HaveElement(..)
            | SpecialOp::RemoveSome(..)
            | SpecialOp::HaveSome(..)
            | SpecialOp::DepositSome(..)
            | SpecialOp::WithdrawSome(..) => false,
        }
    }
}

impl TransitionStmt {
    pub fn get_span<'a>(&'a self) -> &'a Span {
        match self {
            TransitionStmt::Block(span, _) => span,
            TransitionStmt::Let(span, _, _, _, _) => span,
            TransitionStmt::If(span, _, _, _) => span,
            TransitionStmt::Require(span, _) => span,
            TransitionStmt::Assert(span, _) => span,
            TransitionStmt::Update(span, _, _) => span,
            TransitionStmt::Initialize(span, _, _) => span,
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
            TransitionStmt::Initialize(..) => "init",
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
    /// get the name the user uses in the field declarations to declare the given strategy
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
