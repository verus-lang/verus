use proc_macro2::Span;
use std::rc::Rc;
use syn_verus::token;
use syn_verus::{Block, Expr, FieldsNamed, Generics, Ident, ImplItemMethod, Item, Pat, Type};

#[derive(Clone, Debug)]
pub struct SM {
    pub name: Ident,
    pub generics: Option<Generics>,
    pub fields: Vec<Field>,
    pub fields_named_ast: FieldsNamed,
    pub transitions: Vec<Transition>,
    pub concurrent: bool,
    pub transition_label: Option<Item>,
    pub init_label: Option<Item>,
}

#[derive(Clone, Debug)]
pub struct Extras {
    pub invariants: Vec<Invariant>,
    pub lemmas: Vec<Lemma>,
}

pub const TRANSITION_LABEL_TYPE_NAME: &str = "Label";
pub const INIT_LABEL_TYPE_NAME: &str = "InitLabel";

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
    Set(Type),
    Count,
    Bool,

    PersistentMap(Type, Type),
    PersistentOption(Type),
    PersistentSet(Type),
    PersistentCount,
    PersistentBool,

    StorageOption(Type),
    StorageMap(Type, Type),
}

#[derive(Clone, Debug, PartialEq, Eq, Copy)]
pub enum TransitionKind {
    Init,
    Transition,

    /// Like a transition, but it can't update anything.
    /// Can still be useful if there's a transition label
    /// (e.g., for "query" transitions).
    ReadonlyTransition,

    /// This is sort of like a readonly transition, but it
    /// does not actually create a transition relation and
    /// it never has an associated label.
    /// You can use this to define extra safety conditions,
    /// like guard properties.
    Property,
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
    /// Represents the element `true`
    True,
    /// Represents the element Some(e)
    OptionSome(Option<Expr>),
    /// Represents the singleton map [k => v]
    SingletonKV(Expr, Option<Expr>),
    /// Represents the singleton multiset {e}
    SingletonMultiset(Expr),
    /// Represents the set multiset {e}
    SingletonSet(Expr),
    /// Represents e
    /// (can be used with any sharding strategy)
    General(Expr),
}

impl MonoidElt {
    pub fn syntax(&self) -> &'static str {
        match self {
            MonoidElt::OptionSome(_) => "Some(...)",
            MonoidElt::SingletonKV(_, _) => "[... => ...]",
            MonoidElt::SingletonMultiset(_) => "{ ... }",
            MonoidElt::SingletonSet(_) => "set { ... }",
            MonoidElt::General(_) => "( ... )",
            MonoidElt::True => "true",
        }
    }

    pub fn type_name(&self) -> &'static str {
        match self {
            MonoidElt::OptionSome(_) => "Option",
            MonoidElt::SingletonKV(_, _) => "Map",
            MonoidElt::SingletonMultiset(_) => "Multiset",
            MonoidElt::SingletonSet(_) => "Set",
            MonoidElt::True => "bool",
            MonoidElt::General(_) => {
                // This function is just for error messages, and the relevant error
                // shouldn't show up for this case.
                panic!("no single applicable type");
            }
        }
    }

    pub fn is_general(&self) -> bool {
        match self {
            MonoidElt::General(_) => true,
            _ => false,
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
    pub proof: Option<Rc<Block>>,
    pub error_msg: String,
}

/// like syn::Arm, without the body
#[derive(Clone, Debug)]
pub struct Arm {
    pub pat: Pat,
    pub guard: Option<(token::If, Box<Expr>)>,
    pub fat_arrow_token: token::FatArrow,
    pub comma: Option<token::Comma>,
}

#[derive(Clone, Debug)]
pub enum SplitKind {
    If(Expr),
    Match(Expr, Vec<Arm>),
    Let(Pat, Option<Type>, LetKind, Expr),
    /// concurrent-state-machine-specific stuff
    Special(Ident, SpecialOp, AssertProof, Option<Pat>),
}

#[derive(Clone, Debug)]
pub enum SubIdx {
    Field(Ident),
    Idx(Expr),
}

#[derive(Clone, Debug)]
pub enum TransitionStmt {
    Block(Span, Vec<TransitionStmt>),
    Split(Span, SplitKind, Vec<TransitionStmt>),
    Require(Span, Expr),
    Assert(Span, Expr, AssertProof),
    Update(Span, Ident, Expr),
    SubUpdate(Span, Ident, Vec<SubIdx>, Expr),
    Initialize(Span, Ident, Expr),

    /// Different than an Assert - this statement is allowed to depend on output values.
    /// Used internally by various transformations in `concurrency_tokens.rs`.
    PostCondition(Span, Expr),
}

#[derive(Clone, Debug)]
pub enum SimplStmt {
    Let(Span, Pat, Option<Type>, Expr, Vec<SimplStmt>),
    Split(Span, SplitKind, Vec<Vec<SimplStmt>>), // only for If, Match

    Require(Span, Expr),
    PostCondition(Span, Expr),
    Assert(Span, Expr, AssertProof),
    Assign(Span, Ident, Type, Expr),
}

impl SpecialOp {
    /// returns 'true' if the operational definition of the operation
    /// updates the field value
    pub fn is_modifier(&self) -> bool {
        self.stmt.is_modifier()
    }

    pub fn is_only_allowed_in_property_or_readonly(&self) -> bool {
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

    pub fn is_withdraw(self) -> bool {
        match self {
            MonoidStmtType::Withdraw => true,
            _ => false,
        }
    }
}

impl TransitionStmt {
    pub fn get_span<'a>(&'a self) -> &'a Span {
        match self {
            TransitionStmt::Block(span, _) => span,
            TransitionStmt::Split(span, _, _) => span,
            TransitionStmt::Require(span, _) => span,
            TransitionStmt::Assert(span, _, _) => span,
            TransitionStmt::Update(span, _, _) => span,
            TransitionStmt::SubUpdate(span, _, _, _) => span,
            TransitionStmt::Initialize(span, _, _) => span,
            TransitionStmt::PostCondition(span, _) => span,
        }
    }

    pub fn statement_name(&self) -> &'static str {
        match self {
            TransitionStmt::Block(..) => "block",
            TransitionStmt::Split(_, SplitKind::Let(..), _) => "let",
            TransitionStmt::Split(_, SplitKind::If(..), _) => "if",
            TransitionStmt::Split(_, SplitKind::Match(..), _) => "match",
            TransitionStmt::Split(_, SplitKind::Special(_, op, _, _), _) => op.stmt.name(),
            TransitionStmt::Require(..) => "require",
            TransitionStmt::Assert(..) => "assert",
            TransitionStmt::Update(..) => "update",
            TransitionStmt::SubUpdate(..) => "update",
            TransitionStmt::Initialize(..) => "init",
            TransitionStmt::PostCondition(..) => "post_condition",
        }
    }

    pub fn is_trivial(&self) -> bool {
        match self {
            TransitionStmt::Block(_, vs) => vs.len() == 0,
            _ => false,
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

            ShardableType::Option(_) => "option",
            ShardableType::Map(_, _) => "map",
            ShardableType::Multiset(_) => "multiset",
            ShardableType::Set(_) => "set",
            ShardableType::Count => "count",
            ShardableType::Bool => "bool",

            ShardableType::PersistentMap(_, _) => "persistent_map",
            ShardableType::PersistentOption(_) => "persistent_option",
            ShardableType::PersistentSet(_) => "persistent_set",
            ShardableType::PersistentCount => "persistent_count",
            ShardableType::PersistentBool => "persistent_bool",

            ShardableType::StorageOption(_) => "storage_option",
            ShardableType::StorageMap(_, _) => "storage_map",
        }
    }

    pub fn is_count(&self) -> bool {
        match self {
            ShardableType::Count => true,
            ShardableType::PersistentCount => true,
            _ => false,
        }
    }

    pub fn is_storage(&self) -> bool {
        match self {
            ShardableType::StorageOption(_) | ShardableType::StorageMap(_, _) => true,

            ShardableType::Variable(_)
            | ShardableType::Constant(_)
            | ShardableType::NotTokenized(_)
            | ShardableType::Multiset(_)
            | ShardableType::Option(_)
            | ShardableType::Map(_, _)
            | ShardableType::PersistentMap(_, _)
            | ShardableType::PersistentOption(_)
            | ShardableType::PersistentSet(_)
            | ShardableType::PersistentCount
            | ShardableType::PersistentBool
            | ShardableType::Count
            | ShardableType::Bool
            | ShardableType::Set(_) => false,
        }
    }

    pub fn is_persistent(&self) -> bool {
        match self {
            ShardableType::PersistentMap(_, _)
            | ShardableType::PersistentOption(_)
            | ShardableType::PersistentSet(_)
            | ShardableType::PersistentCount
            | ShardableType::PersistentBool => true,

            ShardableType::Variable(_)
            | ShardableType::Constant(_)
            | ShardableType::NotTokenized(_)
            | ShardableType::Multiset(_)
            | ShardableType::Option(_)
            | ShardableType::Set(_)
            | ShardableType::Map(_, _)
            | ShardableType::StorageOption(_)
            | ShardableType::StorageMap(_, _)
            | ShardableType::Bool
            | ShardableType::Count => false,
        }
    }

    #[allow(unused)]
    pub fn get_option_param_type(&self) -> Type {
        match self {
            ShardableType::Option(ty) => ty.clone(),
            ShardableType::StorageOption(ty) => ty.clone(),
            _ => panic!("get_option_param_type expected option"),
        }
    }

    #[allow(unused)]
    pub fn get_multiset_param_type(&self) -> Type {
        match self {
            ShardableType::Multiset(ty) => ty.clone(),
            _ => panic!("get_multiset_param_type expected multiset"),
        }
    }

    #[allow(unused)]
    pub fn get_map_key_type(&self) -> Type {
        match self {
            ShardableType::Map(key, _val) => key.clone(),
            ShardableType::StorageMap(key, _val) => key.clone(),
            _ => panic!("get_map_key_type expected map"),
        }
    }

    #[allow(unused)]
    pub fn get_map_value_type(&self) -> Type {
        match self {
            ShardableType::Map(_key, val) => val.clone(),
            ShardableType::StorageMap(_key, val) => val.clone(),
            _ => panic!("get_map_value_type expected map"),
        }
    }
}

impl Field {
    pub fn get_type(&self) -> Type {
        crate::to_token_stream::shardable_type_to_type(self.type_span, &self.stype)
    }
}

impl TransitionKind {
    pub fn requires_invariant_lemma(&self) -> bool {
        match self {
            TransitionKind::Init => true,
            TransitionKind::Transition => true,
            TransitionKind::ReadonlyTransition => false,
            TransitionKind::Property => false,
        }
    }
}
