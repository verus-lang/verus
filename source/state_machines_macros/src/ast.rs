use proc_macro2::Span;
use std::rc::Rc;
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
/// (For non-tokenized state machines, we just say everything
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
/// and just represent it as `Option(Foo)` (not `Option(Option<Foo>)`).
/// This way, we can easily talk about `Foo` directly when necessary,
/// while we can easily reconstruct the user-provided type (see `shardable_type_to_type`).

#[derive(Clone, Debug)]
pub enum ShardableType {
    Variable(Type),
    Constant(Type),
    NotTokenized(Type),
    Option(Type),
    Map(Type, Type),
    Multiset(Type),
    StorageOption(Type),
    StorageMap(Type, Type),
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

#[derive(Clone, Copy, Debug)]
pub enum MonoidStmtType {
    Have,
    Add,
    Remove,
    Guard,
    Deposit,
    Withdraw,
}

impl MonoidStmtType {
    pub fn name(self) -> &'static str {
        match self {
            MonoidStmtType::Have => "have",
            MonoidStmtType::Add => "add",
            MonoidStmtType::Remove => "remove",
            MonoidStmtType::Guard => "guard",
            MonoidStmtType::Deposit => "deposit",
            MonoidStmtType::Withdraw => "withdraw",
        }
    }

    pub fn is_for_storage(self) -> bool {
        match self {
            MonoidStmtType::Have => false,
            MonoidStmtType::Add => false,
            MonoidStmtType::Remove => false,
            MonoidStmtType::Guard => true,
            MonoidStmtType::Deposit => true,
            MonoidStmtType::Withdraw => true,
        }
    }
}

#[derive(Clone, Debug)]
pub enum MonoidElt {
    OptionSome(Expr),
    SingletonKV(Expr, Expr),
    SingletonMultiset(Expr),
}

impl MonoidElt {
    pub fn syntax(&self) -> &'static str {
        match self {
            MonoidElt::OptionSome(_) => "Some(...)",
            MonoidElt::SingletonKV(_, _) => "[... => ...]",
            MonoidElt::SingletonMultiset(_) => "{ ... }",
        }
    }

    pub fn type_name(&self) -> &'static str {
        match self {
            MonoidElt::OptionSome(_) => "Option",
            MonoidElt::SingletonKV(_, _) => "Map",
            MonoidElt::SingletonMultiset(_) => "Multiset",
        }
    }
}

#[derive(Clone, Debug)]
pub struct SpecialOp {
    pub stmt: MonoidStmtType,
    pub elt: MonoidElt,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum LetKind {
    Normal,
    BirdsEye,
}

/// Extra info for generating the verification condition of a safety condition
#[derive(Clone, Debug)]
pub struct AssertProof {
    pub proof: Option<Rc<syn::Block>>,
    pub error_msg: &'static str,
}

#[derive(Clone, Debug)]
pub enum TransitionStmt {
    Block(Span, Vec<TransitionStmt>),
    Let(Span, Ident, LetKind, Expr, Box<TransitionStmt>),
    If(Span, Expr, Box<TransitionStmt>, Box<TransitionStmt>),
    Require(Span, Expr),
    Assert(Span, Expr, AssertProof),
    Update(Span, Ident, Expr),
    Initialize(Span, Ident, Expr),

    /// concurrent-state-machine-specific stuff
    Special(Span, Ident, SpecialOp, AssertProof),

    /// Different than an Assert - this statement is allowed to depend on output values.
    /// Used internally by various transformations, both by `concurrency_tokens.rs`
    /// and by `to_relation.rs`.
    /// This cannot be directly constructed by the user.
    PostCondition(Span, Expr),
}

impl SpecialOp {
    /// returns 'true' if the operational definition of the operation
    /// updates the field value
    pub fn is_modifier(&self) -> bool {
        self.stmt.is_modifier()
    }

    pub fn is_only_allowed_in_readonly(&self) -> bool {
        self.stmt.is_guard()
    }

    pub fn is_have(&self) -> bool {
        self.stmt.is_have()
    }

    pub fn is_deposit(&self) -> bool {
        self.stmt.is_deposit()
    }

    pub fn is_remove(&self) -> bool {
        self.stmt.is_remove()
    }

    pub fn is_add(&self) -> bool {
        self.stmt.is_add()
    }

    pub fn is_guard(&self) -> bool {
        self.stmt.is_guard()
    }
}

impl MonoidStmtType {
    pub fn is_modifier(self) -> bool {
        match self {
            MonoidStmtType::Have => false,
            MonoidStmtType::Guard => false,
            MonoidStmtType::Add => true,
            MonoidStmtType::Remove => true,
            MonoidStmtType::Deposit => true,
            MonoidStmtType::Withdraw => true,
        }
    }

    pub fn is_have(self) -> bool {
        match self {
            MonoidStmtType::Have => true,
            _ => false,
        }
    }

    pub fn is_deposit(self) -> bool {
        match self {
            MonoidStmtType::Deposit => true,
            _ => false,
        }
    }

    pub fn is_remove(self) -> bool {
        match self {
            MonoidStmtType::Remove => true,
            _ => false,
        }
    }

    pub fn is_add(self) -> bool {
        match self {
            MonoidStmtType::Add => true,
            _ => false,
        }
    }

    pub fn is_guard(self) -> bool {
        match self {
            MonoidStmtType::Guard => true,
            _ => false,
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
            TransitionStmt::Assert(span, _, _) => span,
            TransitionStmt::Update(span, _, _) => span,
            TransitionStmt::Initialize(span, _, _) => span,
            TransitionStmt::Special(span, _, _, _) => span,
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
            TransitionStmt::Special(_, _, op, _) => op.stmt.name(),
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
            ShardableType::Option(_) => "option",
            ShardableType::Map(_, _) => "map",
            ShardableType::StorageOption(_) => "storage_option",
            ShardableType::StorageMap(_, _) => "storage_map",
        }
    }

    pub fn is_storage(&self) -> bool {
        match self {
            ShardableType::Variable(_) => false,
            ShardableType::Constant(_) => false,
            ShardableType::NotTokenized(_) => false,
            ShardableType::Multiset(_) => false,
            ShardableType::Option(_) => false,
            ShardableType::Map(_, _) => false,
            ShardableType::StorageOption(_) => true,
            ShardableType::StorageMap(_, _) => true,
        }
    }
}
