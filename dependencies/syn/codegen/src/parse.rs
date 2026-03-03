use crate::{version, workspace_path};
use anyhow::{bail, Result};
use indexmap::IndexMap;
use quote::quote;
use std::collections::BTreeMap;
use std::fmt::{self, Display};
use std::fs;
use std::path::{Path, PathBuf};
use syn::parse::{Error, Parser};
use syn::{
    parse_quote, Attribute, Data, DataEnum, DataStruct, DeriveInput, Fields, GenericArgument,
    Ident, Item, PathArguments, TypeMacro, TypePath, TypeTuple, UseTree, Visibility,
};
use syn_codegen as types;

const SYN_CRATE_ROOT: &str = "src/lib.rs";
const TOKEN_SRC: &str = "src/token.rs";
const IGNORED_MODS: &[&str] = &["fold", "visit", "visit_mut"];
const EXTRA_TYPES: &[&str] = &["Lifetime"];

struct Lookup {
    items: BTreeMap<Ident, AstItem>,
    // "+" => "Add"
    tokens: BTreeMap<String, String>,
    // "PatLit" => "ExprLit"
    aliases: BTreeMap<Ident, Ident>,
}

/// Parse the contents of `src` and return a list of AST types.
pub fn parse() -> Result<types::Definitions> {
    let tokens = load_token_file(TOKEN_SRC)?;

    let mut lookup = Lookup {
        items: BTreeMap::new(),
        tokens,
        aliases: BTreeMap::new(),
    };

    load_file(SYN_CRATE_ROOT, &[], &mut lookup)?;

    let version = version::get()?;

    let types = lookup
        .items
        .values()
        .map(|item| introspect_item(item, &lookup))
        .collect();

    let tokens = lookup
        .tokens
        .into_iter()
        .map(|(name, ty)| (ty, name))
        .collect();

    Ok(types::Definitions {
        version,
        types,
        tokens,
    })
}

/// Data extracted from syn source
pub struct AstItem {
    ast: DeriveInput,
    features: Vec<Attribute>,
}

fn introspect_item(item: &AstItem, lookup: &Lookup) -> types::Node {
    let features = introspect_features(&item.features);

    match &item.ast.data {
        Data::Enum(data) => types::Node {
            ident: item.ast.ident.to_string(),
            features,
            data: types::Data::Enum(introspect_enum(data, lookup)),
            exhaustive: !(is_non_exhaustive(&item.ast.attrs)
                || data.variants.iter().any(|v| is_doc_hidden(&v.attrs))),
        },
        Data::Struct(data) => types::Node {
            ident: item.ast.ident.to_string(),
            features,
            data: {
                if data.fields.iter().all(|f| is_pub(&f.vis)) {
                    types::Data::Struct(introspect_struct(data, lookup))
                } else {
                    types::Data::Private
                }
            },
            exhaustive: !is_non_exhaustive(&item.ast.attrs),
        },
        Data::Union(..) => panic!("union not supported"),
    }
}

fn introspect_enum(item: &DataEnum, lookup: &Lookup) -> types::Variants {
    item.variants
        .iter()
        .filter_map(|variant| {
            if is_doc_hidden(&variant.attrs) {
                return None;
            }
            let fields = match &variant.fields {
                Fields::Unnamed(fields) => fields
                    .unnamed
                    .iter()
                    .map(|field| introspect_type(&field.ty, lookup))
                    .collect(),
                Fields::Unit => vec![],
                Fields::Named(_) => panic!("enum representation not supported"),
            };
            Some((variant.ident.to_string(), fields))
        })
        .collect()
}

fn introspect_struct(item: &DataStruct, lookup: &Lookup) -> types::Fields {
    match &item.fields {
        Fields::Named(fields) => fields
            .named
            .iter()
            .map(|field| {
                (
                    field.ident.as_ref().unwrap().to_string(),
                    introspect_type(&field.ty, lookup),
                )
            })
            .collect(),
        Fields::Unit => IndexMap::new(),
        Fields::Unnamed(_) => panic!("struct representation not supported"),
    }
}

fn introspect_type(item: &syn::Type, lookup: &Lookup) -> types::Type {
    match item {
        syn::Type::Path(TypePath { qself: None, path }) => {
            let last = path.segments.last().unwrap();
            let string = last.ident.to_string();

            match string.as_str() {
                "Option" => {
                    let nested = introspect_type(first_arg(&last.arguments), lookup);
                    types::Type::Option(Box::new(nested))
                }
                "Punctuated" => {
                    let nested = introspect_type(first_arg(&last.arguments), lookup);
                    let types::Type::Token(punct) =
                        introspect_type(last_arg(&last.arguments), lookup)
                    else {
                        panic!()
                    };
                    types::Type::Punctuated(types::Punctuated {
                        element: Box::new(nested),
                        punct,
                    })
                }
                "Vec" => {
                    let nested = introspect_type(first_arg(&last.arguments), lookup);
                    types::Type::Vec(Box::new(nested))
                }
                "Box" => {
                    let nested = introspect_type(first_arg(&last.arguments), lookup);
                    types::Type::Box(Box::new(nested))
                }
                "Brace" | "Bracket" | "Paren" | "Group" => types::Type::Group(string),
                "TokenStream" | "Literal" | "Ident" | "Span" => types::Type::Ext(string),
                "String" | "u32" | "usize" | "bool" => types::Type::Std(string),
                _ => {
                    let mut resolved = &last.ident;
                    while let Some(alias) = lookup.aliases.get(resolved) {
                        resolved = alias;
                    }
                    if lookup.items.contains_key(resolved) {
                        types::Type::Syn(resolved.to_string())
                    } else {
                        unimplemented!("{}", resolved);
                    }
                }
            }
        }
        syn::Type::Tuple(TypeTuple { elems, .. }) => {
            let tys = elems.iter().map(|ty| introspect_type(ty, lookup)).collect();
            types::Type::Tuple(tys)
        }
        syn::Type::Macro(TypeMacro { mac })
            if mac.path.segments.last().unwrap().ident == "Token" =>
        {
            let content = mac.tokens.to_string();
            let ty = lookup.tokens.get(&content).unwrap().clone();

            types::Type::Token(ty)
        }
        _ => panic!("{}", quote!(#item).to_string()),
    }
}

fn introspect_features(attrs: &[Attribute]) -> types::Features {
    let mut ret = types::Features::default();

    for attr in attrs {
        if !attr.path().is_ident("cfg") {
            continue;
        }

        let features = attr.parse_args_with(parsing::parse_features).unwrap();

        if ret.any.is_empty() {
            ret = features;
        } else if ret.any.len() < features.any.len() {
            assert!(ret.any.iter().all(|f| features.any.contains(f)));
        } else {
            assert!(features.any.iter().all(|f| ret.any.contains(f)));
            ret = features;
        }
    }

    ret
}

fn is_pub(vis: &Visibility) -> bool {
    match vis {
        Visibility::Public(_) => true,
        _ => false,
    }
}

fn is_non_exhaustive(attrs: &[Attribute]) -> bool {
    for attr in attrs {
        if attr.path().is_ident("non_exhaustive") {
            return true;
        }
    }
    false
}

fn is_doc_hidden(attrs: &[Attribute]) -> bool {
    for attr in attrs {
        if attr.path().is_ident("doc") && attr.parse_args::<parsing::kw::hidden>().is_ok() {
            return true;
        }
    }
    false
}

fn first_arg(params: &PathArguments) -> &syn::Type {
    let data = match params {
        PathArguments::AngleBracketed(data) => data,
        _ => panic!("expected at least 1 type argument here"),
    };

    match data
        .args
        .first()
        .expect("expected at least 1 type argument here")
    {
        GenericArgument::Type(ty) => ty,
        _ => panic!("expected at least 1 type argument here"),
    }
}

fn last_arg(params: &PathArguments) -> &syn::Type {
    let data = match params {
        PathArguments::AngleBracketed(data) => data,
        _ => panic!("expected at least 1 type argument here"),
    };

    match data
        .args
        .last()
        .expect("expected at least 1 type argument here")
    {
        GenericArgument::Type(ty) => ty,
        _ => panic!("expected at least 1 type argument here"),
    }
}

mod parsing {
    use super::AstItem;
    use proc_macro2::TokenStream;
    use quote::quote;
    use std::collections::{BTreeMap, BTreeSet};
    use syn::parse::{ParseStream, Result};
    use syn::{
        braced, bracketed, parenthesized, parse_quote, token, Attribute, Expr, Ident, Lit, LitStr,
        Path, Token,
    };
    use syn_codegen as types;

    fn peek_tag(input: ParseStream, tag: &str) -> bool {
        let ahead = input.fork();
        ahead.parse::<Token![#]>().is_ok()
            && ahead
                .parse::<Ident>()
                .map(|ident| ident == tag)
                .unwrap_or(false)
    }

    // Parses #full - returns #[cfg(feature = "full")] if it is present, and
    // nothing otherwise.
    fn full(input: ParseStream) -> Vec<Attribute> {
        if peek_tag(input, "full") {
            input.parse::<Token![#]>().unwrap();
            input.parse::<Ident>().unwrap();
            vec![parse_quote!(#[cfg(feature = "full")])]
        } else {
            vec![]
        }
    }

    pub fn ast_struct(input: ParseStream) -> Result<AstItem> {
        let attrs = input.call(Attribute::parse_outer)?;
        input.parse::<Token![pub]>()?;
        input.parse::<Token![struct]>()?;
        let ident: Ident = input.parse()?;
        let features = full(input);
        let rest: TokenStream = input.parse()?;
        Ok(AstItem {
            ast: syn::parse2(quote! {
                #(#attrs)*
                pub struct #ident #rest
            })?,
            features,
        })
    }

    pub fn ast_enum(input: ParseStream) -> Result<AstItem> {
        let attrs = input.call(Attribute::parse_outer)?;
        input.parse::<Token![pub]>()?;
        input.parse::<Token![enum]>()?;
        let ident: Ident = input.parse()?;
        let rest: TokenStream = input.parse()?;
        Ok(AstItem {
            ast: syn::parse2(quote! {
                #(#attrs)*
                pub enum #ident #rest
            })?,
            features: vec![],
        })
    }

    // A single variant of an ast_enum_of_structs!
    struct EosVariant {
        attrs: Vec<Attribute>,
        name: Ident,
        member: Option<Path>,
    }
    fn eos_variant(input: ParseStream) -> Result<EosVariant> {
        let attrs = input.call(Attribute::parse_outer)?;
        let variant: Ident = input.parse()?;
        let member = if input.peek(token::Paren) {
            let content;
            parenthesized!(content in input);
            let path: Path = content.parse()?;
            Some(path)
        } else {
            None
        };
        input.parse::<Token![,]>()?;
        Ok(EosVariant {
            attrs,
            name: variant,
            member,
        })
    }

    pub fn ast_enum_of_structs(input: ParseStream) -> Result<AstItem> {
        let attrs = input.call(Attribute::parse_outer)?;
        input.parse::<Token![pub]>()?;
        input.parse::<Token![enum]>()?;
        let ident: Ident = input.parse()?;

        let content;
        braced!(content in input);
        let mut variants = Vec::new();
        while !content.is_empty() {
            variants.push(content.call(eos_variant)?);
        }

        let enum_item = {
            let variants = variants.iter().map(|v| {
                let attrs = &v.attrs;
                let name = &v.name;
                if let Some(member) = &v.member {
                    quote!(#(#attrs)* #name(#member))
                } else {
                    quote!(#(#attrs)* #name)
                }
            });
            parse_quote! {
                #(#attrs)*
                pub enum #ident {
                    #(#variants),*
                }
            }
        };
        Ok(AstItem {
            ast: enum_item,
            features: vec![],
        })
    }

    pub mod kw {
        syn::custom_keyword!(hidden);
        syn::custom_keyword!(macro_rules);
        syn::custom_keyword!(Token);
    }

    pub fn parse_token_macro(input: ParseStream) -> Result<BTreeMap<String, String>> {
        let mut tokens = BTreeMap::new();
        while !input.is_empty() {
            let pattern;
            bracketed!(pattern in input);
            let token = pattern.parse::<TokenStream>()?.to_string();
            input.parse::<Token![=>]>()?;
            let expansion;
            braced!(expansion in input);
            input.parse::<Token![;]>()?;
            expansion.parse::<Token![$]>()?;
            let path: Path = expansion.parse()?;
            let ty = path.segments.last().unwrap().ident.to_string();
            tokens.insert(token, ty.clone());
        }
        Ok(tokens)
    }

    fn parse_feature(input: ParseStream) -> Result<String> {
        let i: Ident = input.parse()?;
        assert_eq!(i, "feature");

        input.parse::<Token![=]>()?;
        let s = input.parse::<LitStr>()?;

        Ok(s.value())
    }

    pub fn parse_features(input: ParseStream) -> Result<types::Features> {
        let mut features = BTreeSet::new();

        let i: Ident = input.fork().parse()?;

        if i == "any" {
            input.parse::<Ident>()?;

            let nested;
            parenthesized!(nested in input);

            while !nested.is_empty() {
                features.insert(parse_feature(&nested)?);

                if !nested.is_empty() {
                    nested.parse::<Token![,]>()?;
                }
            }
        } else if i == "feature" {
            features.insert(parse_feature(input)?);
            assert!(input.is_empty());
        } else {
            panic!("{:?}", i);
        }

        Ok(types::Features { any: features })
    }

    pub fn path_attr(attrs: &[Attribute]) -> Result<Option<&LitStr>> {
        for attr in attrs {
            if attr.path().is_ident("path") {
                if let Expr::Lit(expr) = &attr.meta.require_name_value()?.value {
                    if let Lit::Str(lit) = &expr.lit {
                        return Ok(Some(lit));
                    }
                }
            }
        }
        Ok(None)
    }
}

fn clone_features(features: &[Attribute]) -> Vec<Attribute> {
    features.iter().map(|attr| parse_quote!(#attr)).collect()
}

fn get_features(attrs: &[Attribute], base: &[Attribute]) -> Vec<Attribute> {
    let mut ret = clone_features(base);

    for attr in attrs {
        if attr.path().is_ident("cfg") {
            ret.push(parse_quote!(#attr));
        }
    }

    ret
}

#[derive(Debug)]
struct LoadFileError {
    path: PathBuf,
    line: usize,
    column: usize,
    error: Error,
}

impl std::error::Error for LoadFileError {}

impl Display for LoadFileError {
    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        write!(
            formatter,
            "{path}:{line}:{column}: {error}",
            path = self.path.display(),
            line = self.line,
            column = self.column,
            error = self.error,
        )
    }
}

fn load_file(
    relative_to_workspace_root: impl AsRef<Path>,
    features: &[Attribute],
    lookup: &mut Lookup,
) -> Result<()> {
    let error = match do_load_file(&relative_to_workspace_root, features, lookup).err() {
        None => return Ok(()),
        Some(error) => error,
    };

    let error = error.downcast::<Error>()?;
    let span = error.span().start();

    bail!(LoadFileError {
        path: relative_to_workspace_root.as_ref().to_owned(),
        line: span.line,
        column: span.column + 1,
        error,
    })
}

fn do_load_file(
    relative_to_workspace_root: impl AsRef<Path>,
    features: &[Attribute],
    lookup: &mut Lookup,
) -> Result<()> {
    let relative_to_workspace_root = relative_to_workspace_root.as_ref();
    let parent = relative_to_workspace_root.parent().expect("no parent path");

    // Parse the file
    let src = fs::read_to_string(workspace_path::get(relative_to_workspace_root))?;
    let file = syn::parse_file(&src)?;

    // Collect all of the interesting AstItems declared in this file or submodules.
    'items: for item in file.items {
        match item {
            Item::Mod(item) => {
                // Don't inspect inline modules.
                if item.content.is_some() {
                    continue;
                }

                // We don't want to try to load the generated rust files and
                // parse them, so we ignore them here.
                for name in IGNORED_MODS {
                    if item.ident == name {
                        continue 'items;
                    }
                }

                // Lookup any #[cfg()] attributes on the module and add them to
                // the feature set.
                //
                // The derive module is weird because it is built with either
                // `full` or `derive` but exported only under `derive`.
                let features = if item.ident == "derive" {
                    vec![parse_quote!(#[cfg(feature = "derive")])]
                } else {
                    get_features(&item.attrs, features)
                };

                // Look up the submodule file, and recursively parse it.
                // Only handles same-directory .rs file submodules for now.
                let filename = if let Some(filename) = parsing::path_attr(&item.attrs)? {
                    filename.value()
                } else {
                    format!("{}.rs", item.ident)
                };
                let path = parent.join(filename);
                load_file(path, &features, lookup)?;
            }
            Item::Macro(item) => {
                // Lookip any #[cfg()] attributes directly on the macro
                // invocation, and add them to the feature set.
                let features = get_features(&item.attrs, features);

                // Try to parse the AstItem declaration out of the item.
                let tokens = item.mac.tokens.clone();
                let mut found = if item.mac.path.is_ident("ast_struct") {
                    parsing::ast_struct.parse2(tokens)
                } else if item.mac.path.is_ident("ast_enum") {
                    parsing::ast_enum.parse2(tokens)
                } else if item.mac.path.is_ident("ast_enum_of_structs") {
                    parsing::ast_enum_of_structs.parse2(tokens)
                } else {
                    continue;
                }?;

                // Record our features on the parsed AstItems.
                found.features.extend(clone_features(&features));
                lookup.items.insert(found.ast.ident.clone(), found);
            }
            Item::Struct(item) => {
                let ident = item.ident;
                if EXTRA_TYPES.contains(&&ident.to_string()[..]) {
                    lookup.items.insert(
                        ident.clone(),
                        AstItem {
                            ast: DeriveInput {
                                ident,
                                vis: item.vis,
                                attrs: item.attrs,
                                generics: item.generics,
                                data: Data::Struct(DataStruct {
                                    fields: item.fields,
                                    struct_token: item.struct_token,
                                    semi_token: item.semi_token,
                                }),
                            },
                            features: clone_features(features),
                        },
                    );
                }
            }
            Item::Use(item)
                if relative_to_workspace_root == Path::new("src/pat.rs")
                    && matches!(item.vis, Visibility::Public(_)) =>
            {
                load_aliases(item.tree, lookup);
            }
            _ => {}
        }
    }
    Ok(())
}

fn load_aliases(use_tree: UseTree, lookup: &mut Lookup) {
    match use_tree {
        UseTree::Path(use_tree) => load_aliases(*use_tree.tree, lookup),
        UseTree::Rename(use_tree) => {
            lookup.aliases.insert(use_tree.rename, use_tree.ident);
        }
        UseTree::Group(use_tree) => {
            for use_tree in use_tree.items {
                load_aliases(use_tree, lookup);
            }
        }
        UseTree::Name(_) | UseTree::Glob(_) => {}
    }
}

fn load_token_file(
    relative_to_workspace_root: impl AsRef<Path>,
) -> Result<BTreeMap<String, String>> {
    let path = workspace_path::get(relative_to_workspace_root);
    let src = fs::read_to_string(path)?;
    let file = syn::parse_file(&src)?;
    for item in file.items {
        if let Item::Macro(item) = item {
            match item.ident {
                Some(i) if i == "Token" => {}
                _ => continue,
            }
            let tokens = item.mac.parse_body_with(parsing::parse_token_macro)?;
            return Ok(tokens);
        }
    }

    panic!("failed to parse Token macro")
}
