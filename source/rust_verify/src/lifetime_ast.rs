use rustc_span::Span;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct Id {
    rename_count: usize,
    raw_id: String,
}

impl Id {
    pub(crate) fn new(rename_count: usize, raw_id: String) -> Id {
        Id { rename_count, raw_id }
    }
    pub(crate) fn to_string(&self) -> String {
        crate::lifetime_emit::encode_raw_id(self.rename_count, &self.raw_id)
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct TypName {
    rename_count: usize,
    id: String,
}

impl TypName {
    pub(crate) fn new(rename_count: usize, id: String) -> TypName {
        TypName { rename_count, id }
    }
    pub(crate) fn to_string(&self) -> String {
        crate::lifetime_emit::encode_typ_name(self.rename_count, &self.id)
    }
}

pub(crate) type Typ = Box<TypX>;
#[derive(Debug)]
pub(crate) enum TypX {
    Primitive(String),
    Datatype(TypName),
}

pub(crate) type Pattern = Box<(Span, PatternX)>;
#[derive(Debug)]
pub(crate) enum PatternX {
    //Wild,
    // TODO: mutability
    Binding(Id),
    // Path(TypName),
}

// We're only interested in expressions that produce non-spec values,
// and primitive types are uninteresting.
// So we don't need most Unary, Binary operators.
pub(crate) type Exp = Box<(Span, ExpX)>;
#[derive(Debug)]
pub(crate) enum ExpX {
    Var(Id),
    // The call target is irrelevant; we only care about the arguments
    Call(Vec<Exp>, Typ),
    Block(Vec<Stm>, Option<Exp>),
}

pub(crate) type Stm = Box<(Span, StmX)>;
#[derive(Debug)]
pub(crate) enum StmX {
    Expr(Exp),
    Let(Pattern, Option<Exp>),
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
}

#[derive(Debug)]
pub(crate) struct DatatypeDecl {
    pub(crate) name: TypName,
    pub(crate) span: Span,
    // Does the type implement the Copy trait?
    // REVIEW: for generic types like Option, this will be more than just a bool
    pub(crate) implements_copy: bool,
    pub(crate) datatype: Box<Datatype>,
}

#[derive(Debug)]
pub(crate) struct FunDecl {
    pub(crate) name: Id,
    pub(crate) params: Vec<(Span, Id, Typ)>,
    pub(crate) ret: Option<Typ>,
    pub(crate) body: Exp,
}
