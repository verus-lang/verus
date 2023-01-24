use rustc_ast::{CaptureBy, Movability, Mutability};
use rustc_span::Span;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum IdKind {
    Datatype,
    Variant,
    TypParam,
    Lifetime,
    Fun,
    Local,
    Builtin,
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
#[derive(Debug)]
pub(crate) enum TypX {
    Primitive(String),
    TypParam(Id),
    Never,
    Ref(Typ, Option<Id>, Mutability),
    Phantom(Typ),
    Slice(Typ),
    Tuple(Vec<Typ>),
    Datatype(Id, Vec<Typ>),
    Closure,
}

pub(crate) type Pattern = Box<(Span, PatternX)>;
#[derive(Debug)]
pub(crate) enum PatternX {
    Wildcard,
    Binding(Id, Mutability),
    Tuple(Vec<Pattern>),
    DatatypeTuple(Id, Option<Id>, Vec<Pattern>),
    DatatypeStruct(Id, Option<Id>, Vec<(Id, Pattern)>),
}

// We're only interested in expressions that produce non-spec values,
// and primitive types are uninteresting.
// So we don't need most Unary, Binary operators.
pub(crate) type Exp = Box<(Span, ExpX)>;
#[derive(Debug)]
pub(crate) enum ExpX {
    Panic,
    Var(Id),
    Op(Vec<Exp>, Typ),
    Call(Exp, Vec<Typ>, Vec<Exp>),
    Tuple(Vec<Exp>),
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
    Block(Vec<Stm>, Option<Exp>),
}

pub(crate) type Stm = Box<(Span, StmX)>;
#[derive(Debug)]
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
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum ClosureKind {
    Fn,
    FnMut,
    FnOnce,
}

#[derive(Debug)]
pub(crate) enum Bound {
    Id(Id),
    Fn(ClosureKind, Typ, Typ),
}

pub(crate) type GenericParam = (Id, Vec<Bound>);

#[derive(Debug)]
pub(crate) struct DatatypeDecl {
    pub(crate) name: Id,
    pub(crate) span: Span,
    // Does the type implement the Copy trait? (e.g. impl<A: Copy> Copy for S<A> {})
    pub(crate) implements_copy: bool,
    pub(crate) generics: Vec<GenericParam>,
    pub(crate) datatype: Box<Datatype>,
}

#[derive(Debug)]
pub(crate) struct ConstDecl {
    pub(crate) span: Span,
    pub(crate) name: Id,
    pub(crate) typ: Typ,
    pub(crate) body: Exp,
}

#[derive(Debug)]
pub(crate) struct FunDecl {
    pub(crate) sig_span: Span,
    pub(crate) name_span: Span,
    pub(crate) name: Id,
    pub(crate) generics: Vec<GenericParam>,
    pub(crate) params: Vec<(Span, Id, Typ)>,
    pub(crate) ret: Option<(Span, Typ)>,
    pub(crate) body: Exp,
}
