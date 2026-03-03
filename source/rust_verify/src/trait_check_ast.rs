use rustc_span::Span;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum IdKind {
    Trait,
    Datatype,
    TypParam,
    Builtin,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct Id {
    pub(crate) kind: IdKind,
    pub(crate) rename_count: usize,
    pub(crate) raw_id: String,
}

impl Id {
    pub(crate) fn new(kind: IdKind, rename_count: usize, raw_id: String) -> Id {
        Id { kind, rename_count, raw_id }
    }
    pub(crate) fn to_string(&self) -> String {
        crate::trait_check_emit::encode_id(self.kind, self.rename_count, &self.raw_id)
    }
    pub(crate) fn is_typ_param(&self) -> bool {
        self.kind == IdKind::TypParam
    }
}

pub(crate) type Typ = Box<TypX>;
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum TypX {
    Primitive(String),
    TypParam(Id),
    // inside trait declarations, Self is special:
    TraitSelf,
    Tuple(Vec<Typ>),
    Datatype(Id, Vec<Id>, Vec<Typ>),
    Dyn(Id, Vec<Typ>),
    Slice(Typ),
    StrSlice,
    Projection {
        self_typ: Typ,
        // use Datatype(Id, Vec<Typ>) to represent (trait_path, trait_typ_args)
        trait_as_datatype: Typ,
        name: Id,
        assoc_typ_args: Vec<Id>,
    },
    PointeeMetadata(Typ),
}

#[derive(Debug)]
pub(crate) enum Fields {
    Pos(Vec<Typ>),
}

#[derive(Debug)]
pub(crate) enum Datatype {
    Struct(Fields),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum Bound {
    Sized,
    Trait { trait_path: Id, args: Vec<Typ>, equality: Option<(Id, Vec<Id>, Typ)> },
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
    pub(crate) assoc_typs: Vec<(Id, Vec<GenericParam>, Vec<GenericBound>)>,
}

#[derive(Debug)]
pub(crate) struct TraitImpl {
    pub(crate) span: Option<Span>,
    pub(crate) self_typ: Typ,
    pub(crate) generic_params: Vec<GenericParam>,
    pub(crate) generic_bounds: Vec<GenericBound>,
    // use Datatype(Id, Vec<Typ>) to represent (trait_path, trait_typ_args)
    pub(crate) trait_as_datatype: Typ,
    pub(crate) trait_polarity: rustc_middle::ty::ImplPolarity,
    pub(crate) assoc_typs: Vec<(Id, Vec<GenericParam>, Typ)>,
    pub(crate) is_clone: bool,
}

#[derive(Debug)]
pub(crate) struct DatatypeDecl {
    pub(crate) name: Id,
    pub(crate) span: Option<Span>,
    pub(crate) generic_params: Vec<GenericParam>,
    pub(crate) generic_bounds: Vec<GenericBound>,
    pub(crate) datatype: Box<Datatype>,
}
