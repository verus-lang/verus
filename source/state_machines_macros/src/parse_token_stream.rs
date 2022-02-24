//! Module for the initial processing of the macro tokens, to return an SM AST

use crate::ast::{
    Extras, Invariant, Lemma, LemmaPurpose, LemmaPurposeKind, ShardableType, Transition,
    TransitionKind, SM,
};
use crate::ident_visitor::{validate_ident, validate_idents_impl_item_method};
use crate::parse_transition::parse_impl_item_method;
use crate::to_token_stream::shardable_type_to_type;
use crate::transitions::check_transitions;
use proc_macro2::Span;
use syn::buffer::Cursor;
use syn::parse::{Parse, ParseStream};
use syn::spanned::Spanned;
use syn::Token;
use syn::{
    braced, AttrStyle, Attribute, Error, FieldsNamed, FnArg, GenericParam, Generics, Ident,
    ImplItemMethod, Meta, MetaList, NestedMeta, Receiver, ReturnType, Type, TypePath, Visibility,
    WhereClause, PathArguments, GenericArgument,
};

pub struct SMBundle {
    pub name: Ident,
    pub sm: SM,
    pub extras: Extras,
    // Any extra functions the user declares, which are copied verbatim to the
    // 'impl' of the resulting datatype, with no extra processing.
    pub normal_fns: Vec<ImplItemMethod>,
}

///////// TokenStream -> ParseResult

// Here, we do VERY minimal processing, primarily obtaining a list of ImplItemMethods
// to be processed later. The only trick is that we have to look out for the special item
// 'fields' which of course is not valid Rust syntax.

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

        validate_ident(&name)?;

        let generics = if input.peek(Token![<]) {
            let mut gen: Generics = input.parse()?;

            for gp in gen.params.iter() {
                match gp {
                    GenericParam::Type(_) => {}
                    _ => {
                        return Err(Error::new(
                            gp.span(),
                            "Only generic type parameters are supported for state machine",
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

///////// ParseResult -> SM AST

// For a given ImplItemMethod, we check its attributes to see if it needs special processing.
// Transitions (init, transition, and readonly) require the most processing. We have to
// translate the body AST, interpreting it as our mini-language.
// The other special functions (inv, lemma) are kept as-is for now, although they receive
// minimal processing later.

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
                if path.is_ident("inductive") {
                    let lp_kind = LemmaPurposeKind::PreservesInvariant;
                    if nested.len() != 1 {
                        return Err(Error::new(
                            attr.span(),
                            "expected transition name: #[".to_string() + "inductive(name)]",
                        ));
                    }
                    err_on_dupe(&fn_attr_info, attr.span())?;

                    let transition_name = match nested.iter().next() {
                        Some(NestedMeta::Meta(Meta::Path(path))) => match path.get_ident() {
                            Some(ident) => ident.clone(),
                            None => {
                                return Err(Error::new(
                                    attr.span(),
                                    "expected transition name: #[".to_string() + "inductive(name)]",
                                ));
                            }
                        },
                        _ => {
                            return Err(Error::new(
                                attr.span(),
                                "expected transition name: #[".to_string() + "inductive(name)]",
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

// Check that the user did not apply an explicit mode. We will be apply the modes ourselves
// during macro expansion.

fn ensure_no_mode(impl_item_method: &ImplItemMethod, msg: &str) -> syn::parse::Result<()> {
    for attr in &impl_item_method.attrs {
        if attr_is_any_mode(attr) {
            return Err(Error::new(attr.span(), msg));
        }
    }

    return Ok(());
}

fn to_transition(
    impl_item_method: &ImplItemMethod,
    kind: TransitionKind,
) -> syn::parse::Result<Transition> {
    ensure_no_mode(
        impl_item_method,
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

    // make sure the return type is 'bool'
    match &impl_item_method.sig.output {
        ReturnType::Default => {
            return Err(Error::new(
                impl_item_method.sig.span(),
                "an invariant function must return a bool",
            ));
        }
        ReturnType::Type(_, ty) => {
            match &**ty {
                Type::Path(TypePath { qself: None, path }) if path.is_ident("bool") => {
                    // ok
                }
                _ => {
                    return Err(Error::new(ty.span(), "an invariant function must return a bool"));
                }
            }
        }
    }

    return Ok(Invariant { func: impl_item_method });
}

fn to_lemma(impl_item_method: ImplItemMethod, purpose: LemmaPurpose) -> syn::parse::Result<Lemma> {
    ensure_no_mode(
        &impl_item_method,
        "an inductivity lemma is implied to be 'proof'; it should not be explicitly labelled",
    )?;
    Ok(Lemma { purpose, func: impl_item_method })
}

// Process the fields of the state machine.

enum ShardingType {
    Variable,
    Constant,
    NotTokenized,
    Multiset,
    Optional,
}

/// Get the sharding type from the attributes of the field.
/// In a concurrent state machine, we require this for each field.
/// In a 'normal' state machine, we error if we find such an attribute
/// (but internally we represent the field as having the 'variable' strategy).

fn get_sharding_type(
    field_span: Span,
    attrs: &[Attribute],
    concurrent: bool,
) -> syn::parse::Result<ShardingType> {
    let mut res = None;

    for attr in attrs {
        match attr.parse_meta() {
            Ok(Meta::Path(path)) if path.is_ident("sharding") => {
                return Err(Error::new(
                    attr.span(),
                    "expected 1 argument as the sharding strategy, e.g., #[sharding(variable)]",
                ));
            }
            Ok(Meta::List(MetaList { path, paren_token: _, nested }))
                if path.is_ident("sharding") =>
            {
                if nested.len() != 1 {
                    return Err(Error::new(
                        attr.span(),
                        "expected 1 argument as the sharding strategy, e.g., #[sharding(variable)]",
                    ));
                }
                let arg = &nested[0];
                match arg {
                    NestedMeta::Meta(Meta::Path(p)) => match p.get_ident() {
                        Some(ident) => {
                            let t = match ident.to_string().as_str() {
                                "variable" => ShardingType::Variable,
                                "constant" => ShardingType::Constant,
                                "multiset" => ShardingType::Multiset,
                                "option" => ShardingType::Optional,
                                "not_tokenized" => ShardingType::NotTokenized,
                                name => {
                                    return Err(Error::new(
                                        attr.span(),
                                        format!("unrecognized sharding strategy: '{}'", name),
                                    ));
                                }
                            };
                            if !concurrent {
                                return Err(Error::new(
                                    attr.span(),
                                    "sharding strategy only makes sense for concurrent state machines; did you mean to use the concurrent_state_machine! macro?",
                                ));
                            }
                            match res {
                                Some(_) => {
                                    return Err(Error::new(
                                        attr.span(),
                                        "duplicate sharding attribute",
                                    ));
                                }
                                None => {}
                            }
                            res = Some(t);
                        }
                        None => {
                            return Err(Error::new(
                                attr.span(),
                                "expected a single identifier as the sharding strategy, e.g., #[sharding(variable)]",
                            ));
                        }
                    },
                    _ => {
                        return Err(Error::new(
                            attr.span(),
                            "expected a single identifier as the sharding strategy, e.g., #[sharding(variable)]",
                        ));
                    }
                }
            }
            _ => {}
        }
    }

    if concurrent {
        match res {
            None => Err(Error::new(
                field_span,
                "concurrent state machine requires a sharding strategy, e.g., #[sharding(variable)]",
            )),
            Some(r) => Ok(r),
        }
    } else {
        Ok(ShardingType::Variable)
    }
}

/// Checks the given type to be of the form `type_name<...>` and if so, extracts
/// the type parameter and returns it.
/// Returns an Error (using the given strategy name in the error message) if the given
/// type is not of the right form.
fn extract_template_param(ty: &Type, strategy: &str, type_name: &str) -> syn::parse::Result<Type> {
    match ty {
        Type::Path(TypePath { qself: None, path }) if path.segments.len() == 1 => {
            let path_segment = &path.segments[0];
            if path_segment.ident.to_string() == type_name {
                match &path_segment.arguments {
                    PathArguments::AngleBracketed(args) => {
                        if args.args.len() == 1 {
                            let gen_arg = &args.args[0];
                            match gen_arg {
                                GenericArgument::Type(ty) => {
                                    return Ok(ty.clone());
                                }
                                _ => { }
                            }
                        }
                    }
                    _ => { }
                }
            }
        }
        _ => {
        }
    }

    let expected_form = type_name.to_string() + "<...>";
    return Err(Error::new(ty.span(),
        format!("type of a field with sharding strategy '{strategy:}' must be of the form {expected_form:}")));
}

fn to_fields(
    fields_named: &mut FieldsNamed,
    concurrent: bool,
) -> syn::parse::Result<Vec<crate::ast::Field>> {
    let mut v: Vec<crate::ast::Field> = Vec::new();
    for field in fields_named.named.iter_mut() {
        let ident = match &field.ident {
            None => {
                return Err(Error::new(field.span(), "state machine field must have a name"));
            }
            Some(ident) => ident.clone(),
        };
        match &field.vis {
            Visibility::Public(..) => {}
            _ => {
                return Err(Error::new(field.span(), "state machine field must be marked public"));
            }
        }

        validate_ident(&ident)?;

        let sharding_type = get_sharding_type(field.span(), &field.attrs, concurrent)?;
        let stype = match sharding_type {
            ShardingType::Variable => ShardableType::Variable(field.ty.clone()),
            ShardingType::Constant => ShardableType::Constant(field.ty.clone()),
            ShardingType::NotTokenized => ShardableType::NotTokenized(field.ty.clone()),
            ShardingType::Multiset => ShardableType::Multiset(
                  extract_template_param(&field.ty, "multiset", "Multiset")?),
            ShardingType::Optional => ShardableType::Optional(
                  extract_template_param(&field.ty, "option", "Option")?),
        };

        field.ty = shardable_type_to_type(&stype);

        v.push(crate::ast::Field { ident, stype });
    }
    return Ok(v);
}

pub fn parse_result_to_smir(pr: ParseResult, concurrent: bool) -> syn::parse::Result<SMBundle> {
    let ParseResult { name, generics, fns, fields } = pr;

    let mut normal_fns = Vec::new();
    let mut transitions: Vec<Transition> = Vec::new();
    let mut invariants: Vec<Invariant> = Vec::new();
    let mut lemmas: Vec<Lemma> = Vec::new();

    let fields_named = match fields {
        None => {
            return Err(Error::new(
                name.span(),
                "the 'fields' declaration was not found in the state machine definition",
            ));
        }
        Some(f) => f,
    };

    for impl_item_method in fns {
        let attr_info = parse_fn_attr_info(&impl_item_method.attrs)?;
        match attr_info {
            FnAttrInfo::NoneFound => {
                normal_fns.push(impl_item_method);
            }
            FnAttrInfo::Transition | FnAttrInfo::Readonly | FnAttrInfo::Init => {
                validate_idents_impl_item_method(&impl_item_method)?;

                let kind = match attr_info {
                    FnAttrInfo::Transition => TransitionKind::Transition,
                    FnAttrInfo::Readonly => TransitionKind::Readonly,
                    FnAttrInfo::Init => TransitionKind::Init,
                    _ => panic!("can't get here"),
                };

                transitions.push(to_transition(&impl_item_method, kind)?);
            }
            FnAttrInfo::Invariant => {
                invariants.push(to_invariant(impl_item_method)?);
            }
            FnAttrInfo::Lemma(purpose) => lemmas.push(to_lemma(impl_item_method, purpose)?),
        }
    }

    let mut fields_named_ast = fields_named;
    let fields = to_fields(&mut fields_named_ast, concurrent)?;
    let sm = SM { name: name.clone(), generics, fields, fields_named_ast, transitions };

    check_transitions(&sm)?;

    Ok(SMBundle { name, normal_fns, sm, extras: Extras { invariants, lemmas } })
}
