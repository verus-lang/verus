use rustc_ast::{CaptureBy, Movability, Mutability};
use rustc_span::Span;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum IdKind {
    Trait,
    Datatype,
    Variant,
    TypParam,
    Lifetime,
    Fun,
    Local,
    Builtin,
    Field,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct Id {
    kind: IdKind,
    rename_count: usize,
    raw_id: String,
}

impl Id {
    pub(crate) fn new(kind: IdKind, rename_count: usize, raw_id: String) -> Id {
        Id { kind, rename_count, raw_id }
    }
    pub(crate) fn to_string(&self) -> String {
        crate::lifetime_emit::encode_id(self.kind, self.rename_count, &self.raw_id)
    }
}

pub(crate) type Typ = Box<TypX>;
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum TypX {
    Primitive(String),
    TypParam(Id),
    Never,
    Ref(Typ, Option<Id>, Mutability),
    Phantom(Typ),
    Slice(Typ),
    Array(Typ, Typ),
    Tuple(Vec<Typ>),
    Datatype(Id, Vec<Id>, Vec<Typ>),
    Projection {
        self_typ: Typ,
        // use Datatype(Id, Vec<Typ>) to represent (trait_path, trait_typ_args)
        trait_as_datatype: Typ,
        name: Id,
    },
    Closure,
    FnDef,
}

pub(crate) type Pattern = Box<(Span, PatternX)>;
#[derive(Debug, Clone)]
pub(crate) enum PatternX {
    Wildcard,
    Binding(Id, Mutability),
    Box(Pattern),
    Or(Vec<Pattern>),
    Tuple(Vec<Pattern>, Option<usize>),
    DatatypeTuple(Id, Option<Id>, Vec<Pattern>, Option<usize>),
    DatatypeStruct(Id, Option<Id>, Vec<(Id, Pattern)>, bool),
}

// We're only interested in expressions that produce non-spec values,
// and primitive types are uninteresting.
// So we don't need most Unary, Binary operators.
pub(crate) type Exp = Box<(Span, ExpX)>;
#[derive(Debug, Clone)]
pub(crate) enum ExpX {
    Panic,
    Var(Id),
    Op(Vec<Exp>, Typ),
    Call(Exp, Vec<Typ>, Vec<Exp>),
    BuiltinMethod(Exp, String),
    Tuple(Vec<Exp>),
    Array(Vec<Exp>),
    DatatypeTuple(Id, Option<Id>, Vec<Typ>, Vec<Exp>),
    DatatypeStruct(Id, Option<Id>, Vec<Typ>, Vec<(Id, Exp)>, Option<Exp>),
    AddrOf(Mutability, Exp),
    Deref(Exp),
    Assign(Exp, Exp),
    Field(Exp, Id),
    If(Exp, Exp, Exp),
    Match(Exp, Vec<(Pattern, Option<Exp>, Exp)>),
    While(Exp, Exp, Option<Id>),
    Loop(Exp, Option<Id>),
    Break(Option<Id>),
    Continue(Option<Id>),
    Ret(Option<Exp>),
    Closure(CaptureBy, Option<Movability>, Vec<(Span, Id, Typ)>, Exp),
    OpenInvariant(vir::ast::InvAtomicity, Pattern, Exp, Typ, Vec<Stm>),
    ExtraParens(Exp),
    Block(Vec<Stm>, Option<Exp>),
    Index(Typ, Exp, Exp),
}

pub(crate) type Stm = Box<(Span, StmX)>;
#[derive(Debug, Clone)]
pub(crate) enum StmX {
    Expr(Exp),
    Let(Pattern, Typ, Option<Exp>),
}

#[derive(Debug)]
pub(crate) struct Field {
    pub(crate) name: Id,
    pub(crate) typ: Typ,
}

#[derive(Debug)]
pub(crate) enum Fields {
    Pos(Vec<Typ>),
    Named(Vec<Field>),
}

#[derive(Debug)]
pub(crate) enum Datatype {
    Struct(Fields),
    Enum(Vec<(Id, Fields)>),
    Union(Fields),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum ClosureKind {
    Fn,
    FnMut,
    FnOnce,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum Bound {
    Copy,
    Clone,
    Id(Id),
    // use TypX::Datatype to represent Trait bound
    Trait(Typ),
    Fn(ClosureKind, Typ, Typ),
}

// where typ: bound
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct GenericBound {
    pub(crate) typ: Typ,
    pub(crate) bound_vars: Vec<Id>,
    pub(crate) bound: Bound,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct GenericParam {
    pub(crate) name: Id,
    pub(crate) const_typ: Option<Typ>,
}

#[derive(Debug)]
pub(crate) struct TraitDecl {
    pub(crate) name: Id,
    pub(crate) generic_params: Vec<GenericParam>,
    pub(crate) generic_bounds: Vec<GenericBound>,
    pub(crate) assoc_typs: Vec<(Id, Vec<GenericBound>)>,
}

#[derive(Debug, PartialEq, Eq, Hash)]
pub(crate) struct AssocTypeImpl {
    pub(crate) self_typ: Typ,
    pub(crate) generic_params: Vec<GenericParam>,
    pub(crate) generic_bounds: Vec<GenericBound>,
    // use Datatype(Id, Vec<Typ>) to represent (trait_path, trait_typ_args)
    pub(crate) trait_as_datatype: Typ,
}

#[derive(Debug)]
pub(crate) struct AssocTypeImplType {
    pub(crate) name: Id,
    pub(crate) typ: Typ,
}

#[derive(Debug)]
pub(crate) struct DatatypeDecl {
    pub(crate) name: Id,
    pub(crate) span: Span,
    // Does the type implement the Copy trait? (e.g. impl<A: Copy> Copy for S<A> {})
    // If so, for each GenericParam A say whether clone and copy require A: Clone and A: Copy
    pub(crate) implements_copy: Option<Vec<bool>>,
    pub(crate) generic_params: Vec<GenericParam>,
    pub(crate) generic_bounds: Vec<GenericBound>,
    pub(crate) datatype: Box<Datatype>,
}

#[derive(Debug)]
pub(crate) struct Param {
    pub(crate) name: Id,
    pub(crate) typ: Typ,
    pub(crate) span: Option<Span>,
    // is_mut_var: parameter is declared as a mut var like `mut x: X`
    pub(crate) is_mut_var: bool,
}

#[derive(Debug)]
pub(crate) struct FunDecl {
    pub(crate) sig_span: Span,
    pub(crate) name_span: Span,
    pub(crate) name: Id,
    pub(crate) generic_params: Vec<GenericParam>,
    pub(crate) generic_bounds: Vec<GenericBound>,
    pub(crate) params: Vec<Param>,
    pub(crate) ret: Option<(Option<Span>, Typ)>,
    pub(crate) body: Exp,
}
