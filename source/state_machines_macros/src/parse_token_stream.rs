#![allow(unused_imports)]

use crate::ident_visitor::IdentVisitor;
use crate::parse_transition::parse_impl_item_method;
use crate::transitions::check_transitions;
use crate::to_token_stream::shardable_type_to_type;
use proc_macro2::Span;
use crate::ast::{
    Extras, Invariant, Lemma, LemmaPurpose, LemmaPurposeKind, ShardableType, Transition,
    TransitionKind, TransitionStmt, SM,
};
use syn::Token;
use syn::buffer::Cursor;
use syn::parse::{Parse, ParseStream};
use syn::spanned::Spanned;
use syn::visit::Visit;
use syn::{
    braced, AttrStyle, Attribute, Error, Expr, FieldsNamed, FnArg, Ident, ImplItemMethod, Meta,
    MetaList, NestedMeta, Receiver, Type, Visibility, Generics, GenericParam, WhereClause,
};

pub struct SMBundle {
    pub name: Ident,
    pub sm: SM,
    pub extras: Extras,
    pub normal_fns: Vec<ImplItemMethod>,
}

///////// TokenStream -> ParseResult

pub struct ParseResult {
    pub name: Ident,
    pub fns: Vec<ImplItemMethod>,
    pub fields: Option<FieldsNamed>,
    pub generics: Option<Generics>,
}

impl Parse for ParseResult {
    fn parse(input: ParseStream) -> syn::parse::Result<Self> {
        // parse
        //
        // IDENT <...> {
        //    ... a bunch of items
        // }
        let name: Ident = input.parse()?;

        let generics = if input.peek(Token![<]) {
            let mut gen: Generics = input.parse()?;

            for gp in gen.params.iter() {
                match gp {
                    GenericParam::Type(_) => { }
                    _ => {
                        return Err(Error::new(
                            gp.span(),
                            "Only generic type parameters are supported for state machine"
                        ));
                    }
                }
            }

            // parsing a `Generics` doesn't parse the 'where' clause by default
            // so we add this in
            assert!(gen.where_clause.is_none());
            if peek_keyword(input.cursor(), "where") {
                let where_clause: WhereClause = input.parse()?;
                gen.where_clause = Some(where_clause);
            }

            Some(gen)
        } else {
            None
        };

        let items_stream;
        let _ = braced!(items_stream in input);

        let mut fns = Vec::new();
        let mut fields_opt: Option<FieldsNamed> = None;

        while !items_stream.is_empty() {
            // Attempt to parse something of the form
            //
            // fields {
            //    ... a bunch of fields
            // }
            if peek_keyword(items_stream.cursor(), "fields") {
                let kw_span = keyword(&items_stream, "fields")?;
                if fields_opt.is_some() {
                    return Err(Error::new(
                        kw_span,
                        "Expected only one declaration of `fields` block",
                    ));
                }

                let fields_named: FieldsNamed = items_stream.parse()?;
                fields_opt = Some(fields_named);
            }

            // Otherwise parse a function
            let item: ImplItemMethod = items_stream.parse()?;
            fns.push(item);
        }

        return Ok(ParseResult { name, fns, generics, fields: fields_opt });
    }
}

fn keyword(input: ParseStream, token: &str) -> syn::parse::Result<Span> {
    input.step(|cursor| {
        if let Some((ident, rest)) = cursor.ident() {
            if ident == token {
                return Ok((ident.span(), rest));
            }
        }
        Err(cursor.error(format!("expected `{}`", token)))
    })
}

fn peek_keyword(cursor: Cursor, token: &str) -> bool {
    if let Some((ident, _rest)) = cursor.ident() { ident == token } else { false }
}

///////// ParseResult -> SMIR

enum FnAttrInfo {
    NoneFound,
    Transition,
    Readonly,
    Init,
    Invariant,
    Lemma(LemmaPurpose),
}

fn err_on_dupe(info: &FnAttrInfo, span: Span) -> syn::parse::Result<()> {
    match info {
        FnAttrInfo::NoneFound => Ok(()),
        _ => Err(Error::new(span, "conflicting attributes")),
    }
}

fn parse_fn_attr_info(attrs: &Vec<Attribute>) -> syn::parse::Result<FnAttrInfo> {
    let mut fn_attr_info = FnAttrInfo::NoneFound;

    for attr in attrs {
        match attr.style {
            AttrStyle::Inner(_) => {
                continue;
            }
            AttrStyle::Outer => {}
        }

        match attr.parse_meta()? {
            Meta::Path(path) => {
                if path.is_ident("invariant") {
                    err_on_dupe(&fn_attr_info, attr.span())?;
                    fn_attr_info = FnAttrInfo::Invariant;
                } else if path.is_ident("transition") {
                    err_on_dupe(&fn_attr_info, attr.span())?;
                    fn_attr_info = FnAttrInfo::Transition;
                } else if path.is_ident("readonly") {
                    err_on_dupe(&fn_attr_info, attr.span())?;
                    fn_attr_info = FnAttrInfo::Readonly;
                } else if path.is_ident("init") {
                    err_on_dupe(&fn_attr_info, attr.span())?;
                    fn_attr_info = FnAttrInfo::Init;
                }
            }
            Meta::List(MetaList { path, nested, .. }) => {
                if path.is_ident("inductive") || path.is_ident("safety") {
                    let is_safety = path.is_ident("safety");
                    let attrname = if is_safety { "safety" } else { "inductive" };
                    let lp_kind = if is_safety {
                        LemmaPurposeKind::SatisfiesAsserts
                    } else {
                        LemmaPurposeKind::PreservesInvariant
                    };
                    if nested.len() != 1 {
                        return Err(Error::new(
                            attr.span(),
                            "expected transition name: #[".to_string() + attrname + "(name)]",
                        ));
                    }
                    err_on_dupe(&fn_attr_info, attr.span())?;

                    let transition_name = match nested.iter().next() {
                        Some(NestedMeta::Meta(Meta::Path(path))) => match path.get_ident() {
                            Some(ident) => ident.clone(),
                            None => {
                                return Err(Error::new(
                                    attr.span(),
                                    "expected transition name: #[".to_string()
                                        + attrname
                                        + "(name)]",
                                ));
                            }
                        },
                        _ => {
                            return Err(Error::new(
                                attr.span(),
                                "expected transition name: #[".to_string() + attrname + "(name)]",
                            ));
                        }
                    };

                    fn_attr_info = FnAttrInfo::Lemma(LemmaPurpose {
                        transition: transition_name,
                        kind: lp_kind,
                    });
                }
            }
            _ => {}
        };
    }

    return Ok(fn_attr_info);
}

/*
fn attr_is_mode(attr: &Attribute, mode: &str) -> bool {
    match attr.parse_meta() {
        Ok(Meta::Path(path)) if path.is_ident(mode) => true,
        _ => false,
    }
}
*/

fn attr_is_any_mode(attr: &Attribute) -> bool {
    match attr.parse_meta() {
        Ok(Meta::Path(path))
            if path.is_ident("spec") || path.is_ident("proof") || path.is_ident("exec") =>
        {
            true
        }
        _ => false,
    }
}

/*
fn ensure_mode(impl_item_method: &ImplItemMethod, msg: &str, mode: &str) -> syn::parse::Result<()> {
    for attr in &impl_item_method.attrs {
        if attr_is_mode(attr, mode) {
            return Ok(());
        }
    }

    return Err(Error::new(impl_item_method.span(), msg));
}
*/

fn ensure_no_mode(impl_item_method: &ImplItemMethod, msg: &str) -> syn::parse::Result<()> {
    for attr in &impl_item_method.attrs {
        if attr_is_any_mode(attr) {
            return Err(Error::new(attr.span(), msg));
        }
    }

    return Ok(());
}

fn to_transition(
    impl_item_method: &mut ImplItemMethod,
    kind: TransitionKind,
) -> syn::parse::Result<Transition> {
    ensure_no_mode(
        &impl_item_method,
        "a transition fn is implied to be 'spec'; it should not be explicitly labelled",
    )?;
    let ctxt = crate::parse_transition::Ctxt { kind };
    return parse_impl_item_method(impl_item_method, &ctxt);
}

fn to_invariant(impl_item_method: ImplItemMethod) -> syn::parse::Result<Invariant> {
    ensure_no_mode(
        &impl_item_method,
        "an invariant fn is implied to be 'spec'; it should not be explicitly labelled",
    )?;
    if impl_item_method.sig.inputs.len() != 1 {
        return Err(Error::new(
            impl_item_method.sig.inputs.span(),
            "an invariant function must take exactly 1 argument (self)",
        ));
    }

    let one_arg = impl_item_method.sig.inputs.iter().next().expect("one_arg");
    match one_arg {
        FnArg::Receiver(Receiver { mutability: None, .. }) => {}
        _ => {
            return Err(Error::new(
                one_arg.span(),
                "an invariant function must take 1 argument (self)",
            ));
        }
    }

    if impl_item_method.sig.generics.params.len() > 0 {
        return Err(Error::new(
            impl_item_method.sig.generics.span(),
            "an invariant function must take 0 type arguments",
        ));
    }

    return Ok(Invariant { func: impl_item_method });
}

fn to_lemma(
    impl_item_method: ImplItemMethod,
    purpose: LemmaPurpose,
) -> syn::parse::Result<Lemma> {
    ensure_no_mode(
        &impl_item_method,
        "an inductivity lemma is implied to be 'proof'; it should not be explicitly labelled",
    )?;
    Ok(Lemma { purpose, func: impl_item_method })
}

enum ShardingType {
    Variable,
    Constant,
}

fn get_sharding_type(field_span: Span, attrs: &[Attribute], concurrent: bool) ->
      syn::parse::Result<ShardingType>
{
    let mut res = None;

    for attr in attrs {
        match attr.parse_meta() {
            Ok(Meta::Path(path)) if path.is_ident("sharding") => {
                return Err(Error::new(attr.span(), "expected 1 argument as the sharding strategy, e.g., #[sharding(variable)]"));
            }
            Ok(Meta::List(MetaList { path, paren_token: _, nested })) if path.is_ident("sharding") => {
                if nested.len() != 1 {
                    return Err(Error::new(attr.span(), "expected 1 argument as the sharding strategy, e.g., #[sharding(variable)]"));
                }
                let arg = &nested[0];
                match arg {
                    NestedMeta::Meta(Meta::Path(p)) => {
                        match p.get_ident() {
                            Some(ident) => {
                                let t = match ident.to_string().as_str() {
                                    "variable" => ShardingType::Variable,
                                    "constant" => ShardingType::Constant,
                                    name => {
                                        return Err(Error::new(attr.span(), format!("unrecognized sharding strategy: '{}'", name)));
                                    }
                                };
                                if !concurrent {
                                    return Err(Error::new(attr.span(), "sharding strategy only makes sense for concurrent state machines; did you mean to use the concurrent_state_machine! macro?"));
                                }
                                match res {
                                    Some(_) => {
                                        return Err(Error::new(attr.span(), "duplicate sharding attribute"));
                                    }
                                    None => { }
                                }
                                res = Some(t);
                            }
                            None => {
                                return Err(Error::new(attr.span(), "expected a single identifier as the sharding strategy, e.g., #[sharding(variable)]"));
                            }
                        }
                    }
                    _ => {
                        return Err(Error::new(attr.span(), "expected a single identifier as the sharding strategy, e.g., #[sharding(variable)]"));
                    }
                }
            }
            _ => { }
        }
    }

    if concurrent {
        match res {
            None => Err(Error::new(field_span, "concurrent state machine requires a sharding strategy, e.g., #[sharding(variable)]")),
            Some(r) => Ok(r)
        }
    } else {
        Ok(ShardingType::Variable)
    }
}

fn to_fields(fields_named: &mut FieldsNamed, concurrent: bool) -> syn::parse::Result<Vec<crate::ast::Field>> {
    let mut v: Vec<crate::ast::Field> = Vec::new();
    for field in fields_named.named.iter_mut() {
        let ident = match &field.ident {
            None => {
                return Err(Error::new(field.span(), "state machine field must have a name"));
            }
            Some(ident) => ident.clone(),
        };
        match &field.vis {
            Visibility::Public(..) => { }
            _ => {
                return Err(Error::new(field.span(), "state machine field must be marked public"));
            }
        }

        let sharding_type = get_sharding_type(field.span(), &field.attrs, concurrent)?;
        let stype = match sharding_type {
            ShardingType::Variable => ShardableType::Variable(field.ty.clone()),
            ShardingType::Constant => ShardableType::Constant(field.ty.clone()),
        };

        field.ty = shardable_type_to_type(&stype);

        v.push(crate::ast::Field { ident, stype });
    }
    return Ok(v);
}

pub fn check_idents(iim: &ImplItemMethod) -> syn::parse::Result<()> {
    let mut idv = IdentVisitor::new();
    idv.visit_impl_item_method(iim);
    idv.error
}

pub fn parse_result_to_smir(pr: ParseResult, concurrent: bool) -> syn::parse::Result<SMBundle> {
    let ParseResult { name, generics, fns, fields } = pr;

    let mut normal_fns = Vec::new();
    let mut transitions: Vec<Transition> = Vec::new();
    let mut invariants: Vec<Invariant> = Vec::new();
    let mut lemmas: Vec<Lemma> = Vec::new();

    let err_if_not_primary = |impl_item_method: &ImplItemMethod| match fields {
        None => Err(Error::new(
            impl_item_method.span(),
            "a transition definition must be in the primary body for a state machine, i.e.,the body with the 'fields' definition",
        )),
        Some(_) => Ok(()),
    };

    for impl_item_method in fns {
        let attr_info = parse_fn_attr_info(&impl_item_method.attrs)?;
        match attr_info {
            FnAttrInfo::NoneFound => {
                normal_fns.push(impl_item_method);
            }
            FnAttrInfo::Transition | FnAttrInfo::Readonly | FnAttrInfo::Init => {
                check_idents(&impl_item_method)?;

                let kind = match attr_info {
                    FnAttrInfo::Transition => TransitionKind::Transition,
                    FnAttrInfo::Readonly => TransitionKind::Readonly,
                    FnAttrInfo::Init => TransitionKind::Init,
                    _ => {
                        panic!("can't get here");
                    }
                };

                err_if_not_primary(&impl_item_method)?;
                let mut iim = impl_item_method;
                transitions.push(to_transition(&mut iim, kind)?);
            }
            FnAttrInfo::Invariant => {
                invariants.push(to_invariant(impl_item_method)?);
            }
            FnAttrInfo::Lemma(purpose) => lemmas.push(to_lemma(impl_item_method, purpose)?),
        }
    }

    let sm = match fields {
        None => {
            panic!("not implemented");
            //assert!(transitions.len() == 0);
            //None
        }
        Some(fields_named) => {
            let mut fields_named_ast = fields_named;
            let fields = to_fields(&mut fields_named_ast, concurrent)?;
            let name = name.clone();
            let sm = SM { name, generics, fields, fields_named_ast, transitions };
            check_transitions(&sm)?;
            sm
        }
    };

    Ok(SMBundle { name, normal_fns, sm, extras: Extras { invariants, lemmas } })
}
