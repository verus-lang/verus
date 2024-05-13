//! Module for the initial processing of the macro tokens, to return an SM AST

use crate::ast::INIT_LABEL_TYPE_NAME;
use crate::ast::TRANSITION_LABEL_TYPE_NAME;
use crate::ast::{
    Extras, Invariant, Lemma, LemmaPurpose, LemmaPurposeKind, ShardableType, Transition, SM,
};
use crate::ident_visitor::validate_ident;
use crate::parse_transition::parse_transition;
use crate::self_type_visitor::replace_self_sm;
use crate::to_token_stream::shardable_type_to_type;
use crate::transitions::check_transitions;
use proc_macro2::Span;
use syn_verus::buffer::Cursor;
use syn_verus::parse;
use syn_verus::parse::{Parse, ParseStream};
use syn_verus::spanned::Spanned;
use syn_verus::Token;
use syn_verus::{
    braced, AttrStyle, Attribute, Error, FieldsNamed, FnArg, FnArgKind, FnMode, GenericArgument,
    GenericParam, Generics, Ident, ImplItemMethod, Item, ItemFn, Meta, MetaList, NestedMeta,
    PathArguments, Receiver, ReturnType, Type, TypeParam, TypePath, Visibility, WhereClause,
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
    pub attrs: Vec<Attribute>,
    pub name: Ident,
    pub items: Vec<Item>,
    pub fields: Option<FieldsNamed>,
    pub generics: Option<Generics>,
}

impl Parse for ParseResult {
    fn parse(input: ParseStream) -> parse::Result<Self> {
        // parse
        //
        // IDENT <...> {
        //    ... a bunch of items
        // }
        let attrs = input.call(Attribute::parse_outer)?;
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

        let mut items = Vec::new();
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
            } else {
                // Otherwise parse a function
                let item: Item = items_stream.parse()?;
                items.push(item);
            }
        }

        return Ok(ParseResult { attrs, name, items, generics, fields: fields_opt });
    }
}

pub fn keyword(input: ParseStream, token: &str) -> parse::Result<Span> {
    input.step(|cursor| {
        if let Some((ident, rest)) = cursor.ident() {
            if ident == token {
                return Ok((ident.span(), rest));
            }
        }
        Err(cursor.error(format!("expected `{}`", token)))
    })
}

pub fn peek_keyword(cursor: Cursor, token: &str) -> bool {
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
    Invariant,
    Lemma(LemmaPurpose),
}

fn err_on_dupe(info: &FnAttrInfo, span: Span) -> parse::Result<()> {
    match info {
        FnAttrInfo::NoneFound => Ok(()),
        _ => Err(Error::new(span, "conflicting attributes")),
    }
}

fn parse_fn_attr_info(attrs: &Vec<Attribute>) -> parse::Result<FnAttrInfo> {
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
                }
            }
            Meta::List(MetaList { path, nested, .. }) => {
                if path.is_ident("inductive") {
                    let lp_kind = LemmaPurposeKind::PreservesInvariant;
                    if nested.len() != 1 {
                        return Err(Error::new(
                            attr.span(),
                            "expected transition name: #[inductive(name)]",
                        ));
                    }
                    err_on_dupe(&fn_attr_info, attr.span())?;

                    let transition_name = match nested.iter().next() {
                        Some(NestedMeta::Meta(Meta::Path(path))) => match path.get_ident() {
                            Some(ident) => ident.clone(),
                            None => {
                                return Err(Error::new(
                                    attr.span(),
                                    "expected transition name: #[inductive(name)]",
                                ));
                            }
                        },
                        _ => {
                            return Err(Error::new(
                                attr.span(),
                                "expected transition name: #[inductive(name)]",
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
        Ok(Meta::Path(path)) => {
            let segments = path.segments.iter().collect::<Vec<_>>();
            match &segments[..] {
                [prefix_segment, segment] if prefix_segment.ident.to_string() == "verifier" => {
                    let name = segment.ident.to_string();
                    name == "spec" || name == "proof" || name == "exec"
                }
                _ => false,
            }
        }
        _ => false,
    }
}

fn check_polarity_attribute(name: &str) -> bool {
    name == "accept_recursive_types"
        || name == "reject_recursive_types"
        || name == "reject_recursive_types_in_ground_variants"
}

fn attr_is_polarity(attr: &Attribute) -> bool {
    match attr.parse_meta() {
        Ok(Meta::List(list)) => {
            let segments =
                list.path.segments.iter().map(|e| e.ident.to_string()).collect::<Vec<_>>();
            match &segments[..] {
                [prefix_segment, name] if prefix_segment == "verifier" => {
                    check_polarity_attribute(name.as_str())
                }
                [segment] if segment == "cfg_attr" => list.nested.iter().all(|elm| match elm {
                    NestedMeta::Meta(Meta::Path(path)) => {
                        let segments =
                            path.segments.iter().map(|e| e.ident.to_string()).collect::<Vec<_>>();
                        segments[..] == ["verus_keep_ghost"]
                    }
                    NestedMeta::Meta(Meta::List(list)) => {
                        let segments = list
                            .path
                            .segments
                            .iter()
                            .map(|e| e.ident.to_string())
                            .collect::<Vec<_>>();
                        match &segments[..] {
                            [prefix_segment, name] if prefix_segment == "verifier" => {
                                check_polarity_attribute(name)
                            }
                            _ => false,
                        }
                    }
                    _ => false,
                }),
                _ => false,
            }
        }
        _ => false,
    }
}

// Check that the user did not apply an explicit mode. We will apply the modes ourselves
// during macro expansion.

fn ensure_no_mode(impl_item_method: &ImplItemMethod, msg: &str) -> parse::Result<()> {
    for attr in &impl_item_method.attrs {
        if attr_is_any_mode(attr) {
            return Err(Error::new(attr.span(), msg));
        }
    }

    return Ok(());
}

fn to_invariant(impl_item_method: ImplItemMethod) -> parse::Result<Invariant> {
    ensure_no_mode(
        &impl_item_method,
        "an invariant fn is implied to be 'spec'; it should not be explicitly labelled",
    )?;

    if impl_item_method.sig.inputs.len() != 1 {
        return Err(Error::new(
            impl_item_method.sig.span(),
            "an invariant function must take exactly 1 argument (self)",
        ));
    }

    match &impl_item_method.sig.mode {
        FnMode::Default | FnMode::Spec(_) | FnMode::SpecChecked(_) => {}
        FnMode::Proof(mode_proof) => {
            return Err(Error::new(mode_proof.span(), "an invariant function should be `spec`"));
        }
        FnMode::Exec(mode_exec) => {
            return Err(Error::new(mode_exec.span(), "an invariant function should be `spec`"));
        }
    }

    let one_arg = impl_item_method.sig.inputs.iter().next().expect("one_arg");
    match one_arg {
        FnArg { tracked: _, kind: FnArgKind::Receiver(Receiver { mutability: None, .. }) } => {
            // don't need to check for 'tracked' or anything
            // (would be caught by mode checking later)
        }
        _ => {
            return Err(Error::new(
                one_arg.kind.span(),
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
        ReturnType::Type(_, _tracked, _return_name, ty) => {
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

fn to_lemma(impl_item_method: ImplItemMethod, purpose: LemmaPurpose) -> parse::Result<Lemma> {
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

    Option,
    Map,
    Set,
    Multiset,
    Count,
    Bool,

    PersistentOption,
    PersistentMap,
    PersistentSet,
    PersistentCount,
    PersistentBool,

    StorageOption,
    StorageMap,
}

/// Get the sharding type from the attributes of the field.
/// In a tokenized state machine, we require this for each field.
/// In a 'normal' state machine, we error if we find such an attribute
/// (but internally we represent the field as having the 'variable' strategy).

fn get_sharding_type(
    field_span: Span,
    attrs: &[Attribute],
    concurrent: bool,
) -> parse::Result<ShardingType> {
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
                                "set" => ShardingType::Set,
                                "bool" => ShardingType::Bool,
                                "count" => ShardingType::Count,
                                "option" => ShardingType::Option,
                                "map" => ShardingType::Map,
                                "storage_option" => ShardingType::StorageOption,
                                "storage_map" => ShardingType::StorageMap,
                                "persistent_option" => ShardingType::PersistentOption,
                                "persistent_map" => ShardingType::PersistentMap,
                                "persistent_set" => ShardingType::PersistentSet,
                                "persistent_count" => ShardingType::PersistentCount,
                                "persistent_bool" => ShardingType::PersistentBool,
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
                                    "sharding strategy only makes sense for tokenized state machines; did you mean to use the tokenized_state_machine! macro?",
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
                "tokenized state machine requires a sharding strategy on each field, e.g., #[sharding(variable)]",
            )),
            Some(r) => Ok(r),
        }
    } else {
        Ok(ShardingType::Variable)
    }
}

/// Checks the given type to be of the form `type_name`.
/// Returns an Error (using the given strategy name in the error message) if the given
/// type is not of the right form.
fn check_untemplated_type(ty: &Type, strategy: &str, type_name: &str) -> parse::Result<()> {
    match ty {
        Type::Path(TypePath { qself: None, path }) if path.segments.len() == 1 => {
            let path_segment = &path.segments[0];
            if path_segment.ident.to_string() == type_name {
                match &path_segment.arguments {
                    PathArguments::None => {
                        return Ok(());
                    }
                    _ => {}
                }
            }
        }
        _ => {}
    }

    let expected_form = type_name.to_string();
    return Err(Error::new(
        ty.span(),
        format!("type of a field with sharding strategy '{strategy:}' must be {expected_form:}"),
    ));
}

/// Checks the given type to be of the form `type_name<...>` and if so, extracts
/// the type parameter and returns it.
/// Returns an Error (using the given strategy name in the error message) if the given
/// type is not of the right form.
fn extract_template_params(
    ty: &Type,
    strategy: &str,
    type_name: &str,
    num_expected_args: usize,
) -> parse::Result<Vec<Type>> {
    match ty {
        Type::Path(TypePath { qself: None, path }) if path.segments.len() == 1 => {
            let path_segment = &path.segments[0];
            if path_segment.ident.to_string() == type_name {
                match &path_segment.arguments {
                    PathArguments::AngleBracketed(args) => {
                        if args.args.len() == num_expected_args {
                            let types: Vec<Type> = args
                                .args
                                .iter()
                                .filter_map(|gen_arg| match gen_arg {
                                    GenericArgument::Type(ty) => Some(ty.clone()),
                                    _ => None,
                                })
                                .collect();
                            // Check that the filter_map succeeded for each element:
                            if types.len() == num_expected_args {
                                return Ok(types);
                            }
                        }
                    }
                    _ => {}
                }
            }
        }
        _ => {}
    }

    let expected_form =
        type_name.to_string() + "<" + &vec!["_"; num_expected_args].join(", ") + ">";
    return Err(Error::new(
        ty.span(),
        format!(
            "type of a field with sharding strategy '{strategy:}' must be of the form {expected_form:}"
        ),
    ));
}

fn to_fields(
    fields_named: &mut FieldsNamed,
    concurrent: bool,
) -> parse::Result<Vec<crate::ast::Field>> {
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

        for attr in &field.attrs {
            if attr_is_any_mode(attr) {
                return Err(Error::new(
                    attr.span(),
                    "a state field is implied to be 'spec'; it should not be explicitly labelled",
                ));
            }
        }

        validate_ident(&ident)?;

        let sharding_type = get_sharding_type(field.span(), &field.attrs, concurrent)?;
        let stype = match sharding_type {
            ShardingType::Variable => ShardableType::Variable(field.ty.clone()),
            ShardingType::Constant => ShardableType::Constant(field.ty.clone()),
            ShardingType::NotTokenized => ShardableType::NotTokenized(field.ty.clone()),
            ShardingType::Count => {
                check_untemplated_type(&field.ty, "count", "nat")?;
                ShardableType::Count
            }
            ShardingType::PersistentCount => {
                check_untemplated_type(&field.ty, "persistent_count", "nat")?;
                ShardableType::PersistentCount
            }
            ShardingType::Bool => {
                check_untemplated_type(&field.ty, "bool", "bool")?;
                ShardableType::Bool
            }
            ShardingType::PersistentBool => {
                check_untemplated_type(&field.ty, "persistent_bool", "bool")?;
                ShardableType::PersistentBool
            }
            ShardingType::Multiset => {
                let v = extract_template_params(&field.ty, "multiset", "Multiset", 1)?;
                ShardableType::Multiset(v[0].clone())
            }
            ShardingType::Option => {
                let v = extract_template_params(&field.ty, "option", "Option", 1)?;
                ShardableType::Option(v[0].clone())
            }
            ShardingType::Map => {
                let v = extract_template_params(&field.ty, "map", "Map", 2)?;
                ShardableType::Map(v[0].clone(), v[1].clone())
            }
            ShardingType::Set => {
                let v = extract_template_params(&field.ty, "set", "Set", 1)?;
                ShardableType::Set(v[0].clone())
            }
            ShardingType::StorageOption => {
                let v = extract_template_params(&field.ty, "storage_option", "Option", 1)?;
                ShardableType::StorageOption(v[0].clone())
            }
            ShardingType::StorageMap => {
                let v = extract_template_params(&field.ty, "storage_map", "Map", 2)?;
                ShardableType::StorageMap(v[0].clone(), v[1].clone())
            }
            ShardingType::PersistentOption => {
                let v = extract_template_params(&field.ty, "persistent_option", "Option", 1)?;
                ShardableType::PersistentOption(v[0].clone())
            }
            ShardingType::PersistentMap => {
                let v = extract_template_params(&field.ty, "persistent_map", "Map", 2)?;
                ShardableType::PersistentMap(v[0].clone(), v[1].clone())
            }
            ShardingType::PersistentSet => {
                let v = extract_template_params(&field.ty, "persistent_set", "Set", 1)?;
                ShardableType::PersistentSet(v[0].clone())
            }
        };

        field.ty = shardable_type_to_type(field.ty.span(), &stype);
        let type_span = field.ty.span();

        v.push(crate::ast::Field { name: ident, stype, type_span });
    }
    return Ok(v);
}

fn impl_item_method_from_item_fn(item_fn: ItemFn) -> ImplItemMethod {
    let ItemFn { attrs, vis, sig, block, semi_token } = item_fn;
    let block = *block;
    ImplItemMethod { attrs, vis, sig, block, semi_token, defaultness: None }
}

fn item_type_check_name(ident: &Ident) -> parse::Result<bool> {
    if ident.to_string() == TRANSITION_LABEL_TYPE_NAME {
        Ok(false)
    } else if ident.to_string() == INIT_LABEL_TYPE_NAME {
        Ok(true)
    } else {
        Err(Error::new(
            ident.span(),
            format!(
                "state_machine macro only supports the declaration of a `{TRANSITION_LABEL_TYPE_NAME:}` and `{INIT_LABEL_TYPE_NAME:}` types"
            ),
        ))
    }
}

fn is_okay_label_generic_ident(ident: &Ident, main_generics: &Option<Generics>) -> bool {
    let s = ident.to_string();
    match main_generics {
        None => false,
        Some(main_generics) => {
            for p in &main_generics.params {
                match p {
                    GenericParam::Type(TypeParam { ident: i, .. }) => {
                        if i.to_string() == s {
                            return true;
                        }
                    }
                    _ => unreachable!(),
                }
            }
            return false;
        }
    }
}

fn item_type_check_no_bounds(
    span: Span,
    generics: &Generics,
    main_generics: &Option<Generics>,
) -> parse::Result<()> {
    if generics.where_clause.is_some() {
        return Err(Error::new(span, "where clause not supported here"));
    }
    for p in &generics.params {
        match p {
            GenericParam::Type(TypeParam {
                attrs,
                ident,
                colon_token,
                bounds,
                eq_token,
                default,
            }) => {
                if attrs.len() > 0
                    || colon_token.is_some()
                    || bounds.len() > 0
                    || eq_token.is_some()
                    || default.is_some()
                {
                    return Err(Error::new(p.span(), "unsupported type param"));
                }
                if !is_okay_label_generic_ident(ident, main_generics) {
                    return Err(Error::new(p.span(), "invalid generic param"));
                }
            }
            _ => {
                return Err(Error::new(p.span(), "this type param not supported here"));
            }
        }
    }
    Ok(())
}

fn item_type_check_vis(span: Span, vis: &Visibility) -> parse::Result<()> {
    match vis {
        Visibility::Public(_) => Ok(()),
        _ => Err(Error::new(span, "type definition should be `pub`")),
    }
}

pub fn parse_result_to_smir(pr: ParseResult, concurrent: bool) -> parse::Result<SMBundle> {
    let ParseResult { attrs, name, generics, items, fields } = pr;

    for attr in attrs.iter() {
        if !attr_is_polarity(attr) {
            return Err(Error::new(
                attr.span(),
                "the only attributes allowed here are verus_keep_ghost, verifier::accept_recursive_types, verifier::reject_recursive_types, and verifier::reject_recursive_types_in_ground_variants",
            ));
        }
    }

    let mut normal_fns = Vec::new();
    let mut transitions: Vec<Transition> = Vec::new();
    let mut invariants: Vec<Invariant> = Vec::new();
    let mut lemmas: Vec<Lemma> = Vec::new();
    let mut init_label: Option<Item> = None;
    let mut transition_label: Option<Item> = None;

    let fields_named = match fields {
        None => {
            return Err(Error::new(
                name.span(),
                "the 'fields' declaration was not found in the state machine definition",
            ));
        }
        Some(f) => f,
    };

    for item in items.into_iter() {
        match item {
            Item::Fn(item_fn) => {
                let impl_item_method = impl_item_method_from_item_fn(item_fn);
                let attr_info = parse_fn_attr_info(&impl_item_method.attrs)?;
                match attr_info {
                    FnAttrInfo::NoneFound => {
                        normal_fns.push(impl_item_method);
                    }
                    FnAttrInfo::Invariant => {
                        invariants.push(to_invariant(impl_item_method)?);
                    }
                    FnAttrInfo::Lemma(purpose) => lemmas.push(to_lemma(impl_item_method, purpose)?),
                }
            }
            Item::Macro(item_macro) => {
                let t = parse_transition(item_macro.mac)?;
                transitions.push(t);
            }
            item @ Item::Type(_) | item @ Item::Enum(_) | item @ Item::Struct(_) => {
                let is_init = match &item {
                    Item::Type(item_type) => {
                        let is_init = item_type_check_name(&item_type.ident)?;
                        item_type_check_no_bounds(item.span(), &item_type.generics, &generics)?;
                        item_type_check_vis(item.span(), &item_type.vis)?;
                        is_init
                    }
                    Item::Struct(item_struct) => {
                        let is_init = item_type_check_name(&item_struct.ident)?;
                        item_type_check_no_bounds(item.span(), &item_struct.generics, &generics)?;
                        item_type_check_vis(item.span(), &item_struct.vis)?;
                        is_init
                    }
                    Item::Enum(item_enum) => {
                        let is_init = item_type_check_name(&item_enum.ident)?;
                        item_type_check_no_bounds(item.span(), &item_enum.generics, &generics)?;
                        item_type_check_vis(item.span(), &item_enum.vis)?;
                        is_init
                    }
                    _ => {
                        panic!("can't get here");
                    }
                };

                if is_init {
                    if init_label.is_some() {
                        return Err(Error::new(
                            item.span(),
                            format!("{INIT_LABEL_TYPE_NAME:} already declared"),
                        ));
                    }
                    init_label = Some(item);
                } else {
                    if transition_label.is_some() {
                        return Err(Error::new(
                            item.span(),
                            format!("{TRANSITION_LABEL_TYPE_NAME:} already declared"),
                        ));
                    }
                    transition_label = Some(item);
                }
            }
            item => {
                return Err(Error::new(item.span(), "this item is not supported"));
            }
        }
    }

    let mut fields_named_ast = fields_named;
    let fields = to_fields(&mut fields_named_ast, concurrent)?;
    let mut sm = SM {
        attrs,
        name: name.clone(),
        generics,
        fields,
        fields_named_ast,
        transitions,
        concurrent,
        init_label,
        transition_label,
    };

    replace_self_sm(&mut sm);
    check_transitions(&mut sm)?;

    for inv in invariants.iter() {
        match inv.func.vis {
            Visibility::Public(_) => {}
            _ => {
                return Err(Error::new(
                    inv.func.span(),
                    format!(
                        "#[invariant] fn must be be marked `pub` so it can called from the auto-generated `invariant` fn"
                    ),
                ));
            }
        }
    }

    Ok(SMBundle { name, normal_fns, sm, extras: Extras { invariants, lemmas } })
}
