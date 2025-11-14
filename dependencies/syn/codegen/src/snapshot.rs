use crate::operand::{Borrowed, Operand, Owned};
use crate::{file, lookup};
use anyhow::Result;
use proc_macro2::{Ident, Span, TokenStream};
use quote::{format_ident, quote};
use syn::Index;
use syn_codegen::{Data, Definitions, Node, Type};

const TESTS_DEBUG_SRC: &str = "tests/debug/gen.rs";

fn rust_type(ty: &Type) -> TokenStream {
    match ty {
        Type::Syn(ty) => {
            let ident = Ident::new(ty, Span::call_site());
            quote!(syn::#ident)
        }
        Type::Std(ty) => {
            let ident = Ident::new(ty, Span::call_site());
            quote!(#ident)
        }
        Type::Ext(ty) => {
            let ident = Ident::new(ty, Span::call_site());
            quote!(proc_macro2::#ident)
        }
        Type::Token(ty) | Type::Group(ty) => {
            let ident = Ident::new(ty, Span::call_site());
            quote!(syn::token::#ident)
        }
        Type::Punctuated(ty) => {
            let element = rust_type(&ty.element);
            let punct = Ident::new(&ty.punct, Span::call_site());
            quote!(syn::punctuated::Punctuated<#element, #punct>)
        }
        Type::Option(ty) => {
            let inner = rust_type(ty);
            quote!(Option<#inner>)
        }
        Type::Box(ty) => {
            let inner = rust_type(ty);
            quote!(Box<#inner>)
        }
        Type::Vec(ty) => {
            let inner = rust_type(ty);
            quote!(Vec<#inner>)
        }
        Type::Tuple(ty) => {
            let inner = ty.iter().map(rust_type);
            quote!((#(#inner,)*))
        }
    }
}

fn is_printable(ty: &Type) -> bool {
    match ty {
        Type::Ext(name) => name != "Span",
        Type::Box(ty) => is_printable(ty),
        Type::Tuple(ty) => ty.iter().any(is_printable),
        Type::Token(_) | Type::Group(_) => false,
        Type::Syn(_) | Type::Std(_) | Type::Punctuated(_) | Type::Option(_) | Type::Vec(_) => true,
    }
}

fn format_field(val: &Operand, ty: &Type) -> Option<TokenStream> {
    if !is_printable(ty) {
        return None;
    }
    let format = match ty {
        Type::Option(ty) => {
            if let Some(format) = format_field(&Borrowed(quote!(_val)), ty) {
                let ty = rust_type(ty);
                let val = val.ref_tokens();
                quote!({
                    #[derive(RefCast)]
                    #[repr(transparent)]
                    struct Print(Option<#ty>);
                    impl Debug for Print {
                        fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                            match &self.0 {
                                Some(_val) => {
                                    formatter.write_str("Some(")?;
                                    Debug::fmt(#format, formatter)?;
                                    formatter.write_str(")")?;
                                    Ok(())
                                }
                                None => formatter.write_str("None"),
                            }
                        }
                    }
                    Print::ref_cast(#val)
                })
            } else {
                let val = val.tokens();
                quote! {
                    &super::Option { present: #val.is_some() }
                }
            }
        }
        Type::Tuple(ty) => {
            let printable: Vec<TokenStream> = ty
                .iter()
                .enumerate()
                .filter_map(|(i, ty)| {
                    let index = Index::from(i);
                    let val = val.tokens();
                    let inner = Owned(quote!(#val.#index));
                    format_field(&inner, ty)
                })
                .collect();
            if printable.len() == 1 {
                printable.into_iter().next().unwrap()
            } else {
                quote! {
                    &(#(#printable),*)
                }
            }
        }
        _ => {
            let val = val.ref_tokens();
            quote! { Lite(#val) }
        }
    };
    Some(format)
}

fn syntax_tree_enum<'a>(outer: &str, inner: &str, fields: &'a [Type]) -> Option<&'a str> {
    if fields.len() != 1 {
        return None;
    }
    const WHITELIST: &[(&str, &str)] = &[
        ("Meta", "Path"),
        ("PathArguments", "AngleBracketed"),
        ("PathArguments", "Parenthesized"),
        ("Stmt", "Local"),
        ("TypeParamBound", "Lifetime"),
        ("Visibility", "Public"),
        ("Visibility", "Restricted"),
    ];
    match &fields[0] {
        Type::Syn(ty) if WHITELIST.contains(&(outer, inner)) || outer.to_owned() + inner == *ty => {
            Some(ty)
        }
        _ => None,
    }
}

fn expand_impl_body(defs: &Definitions, node: &Node, name: &str, val: &Operand) -> TokenStream {
    let ident = Ident::new(&node.ident, Span::call_site());

    match &node.data {
        Data::Enum(variants) if variants.is_empty() => quote!(unreachable!()),
        Data::Enum(variants) => {
            let arms = variants.iter().map(|(v, fields)| {
                let path = format!("{}::{}", name, v);
                let variant = Ident::new(v, Span::call_site());
                if fields.is_empty() {
                    quote! {
                        syn::#ident::#variant => formatter.write_str(#path),
                    }
                } else if let Some(inner) = syntax_tree_enum(name, v, fields) {
                    let format = expand_impl_body(
                        defs,
                        lookup::node(defs, inner),
                        &path,
                        &Borrowed(quote!(_val)),
                    );
                    quote! {
                        syn::#ident::#variant(_val) => {
                            #format
                        }
                    }
                } else if fields.len() == 1 {
                    let val = quote!(_val);
                    let format = if variant == "Verbatim" {
                        Some(quote! {
                            formatter.write_str("(`")?;
                            Display::fmt(#val, formatter)?;
                            formatter.write_str("`)")?;
                        })
                    } else {
                        let ty = &fields[0];
                        format_field(&Borrowed(val), ty).map(|format| {
                            quote! {
                                formatter.write_str("(")?;
                                Debug::fmt(#format, formatter)?;
                                formatter.write_str(")")?;
                            }
                        })
                    };
                    quote! {
                        syn::#ident::#variant(_val) => {
                            formatter.write_str(#path)?;
                            #format
                            Ok(())
                        }
                    }
                } else {
                    let pats = (0..fields.len()).map(|i| format_ident!("_v{}", i));
                    let fields = fields.iter().enumerate().filter_map(|(i, ty)| {
                        let index = format_ident!("_v{}", i);
                        let val = quote!(#index);
                        let format = format_field(&Borrowed(val), ty)?;
                        Some(quote! {
                            formatter.field(#format);
                        })
                    });
                    quote! {
                        syn::#ident::#variant(#(#pats),*) => {
                            let mut formatter = formatter.debug_tuple(#path);
                            #(#fields)*
                            formatter.finish()
                        }
                    }
                }
            });
            let nonexhaustive = if node.exhaustive {
                None
            } else {
                Some(quote!(_ => unreachable!()))
            };
            let val = val.ref_tokens();
            quote! {
                match #val {
                    #(#arms)*
                    #nonexhaustive
                }
            }
        }
        Data::Struct(fields) => {
            let fields = fields.iter().filter_map(|(f, ty)| {
                let ident = Ident::new(f, Span::call_site());
                if let Type::Option(ty) = ty {
                    Some(if let Some(format) = format_field(&Owned(quote!(self.0)), ty) {
                        let val = val.tokens();
                        let ty = rust_type(ty);
                        quote! {
                            if let Some(val) = &#val.#ident {
                                #[derive(RefCast)]
                                #[repr(transparent)]
                                struct Print(#ty);
                                impl Debug for Print {
                                    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                                        formatter.write_str("Some(")?;
                                        Debug::fmt(#format, formatter)?;
                                        formatter.write_str(")")?;
                                        Ok(())
                                    }
                                }
                                formatter.field(#f, Print::ref_cast(val));
                            }
                        }
                    } else {
                        let val = val.tokens();
                        quote! {
                            if #val.#ident.is_some() {
                                formatter.field(#f, &Present);
                            }
                        }
                    })
                } else {
                    let val = val.tokens();
                    let inner = Owned(quote!(#val.#ident));
                    let format = format_field(&inner, ty)?;
                    let mut call = quote! {
                        formatter.field(#f, #format);
                    };
                    if node.ident == "Block" && f == "stmts" {
                        // Format regardless of whether is_empty().
                    } else if let Type::Vec(_) | Type::Punctuated(_) = ty {
                        call = quote! {
                            if !#val.#ident.is_empty() {
                                #call
                            }
                        };
                    } else if let Type::Syn(inner) = ty {
                        for node in &defs.types {
                            if node.ident == *inner {
                                if let Data::Enum(variants) = &node.data {
                                    if variants.get("None").is_some_and(Vec::is_empty) {
                                        let ty = rust_type(ty);
                                        call = quote! {
                                            match #val.#ident {
                                                #ty::None => {}
                                                _ => { #call }
                                            }
                                        };
                                    }
                                }
                                break;
                            }
                        }
                    }
                    Some(call)
                }
            });
            quote! {
                let mut formatter = formatter.debug_struct(#name);
                #(#fields)*
                formatter.finish()
            }
        }
        Data::Private => {
            if node.ident == "LitInt" || node.ident == "LitFloat" {
                let val = val.ref_tokens();
                quote! {
                    write!(formatter, "{}", #val)
                }
            } else {
                let val = val.tokens();
                quote! {
                    write!(formatter, "{:?}", #val.value())
                }
            }
        }
    }
}

fn expand_impl(defs: &Definitions, node: &Node) -> TokenStream {
    let ident = Ident::new(&node.ident, Span::call_site());
    let body = expand_impl_body(defs, node, &node.ident, &Owned(quote!(self.value)));
    let formatter = match &node.data {
        Data::Enum(variants) if variants.is_empty() => quote!(_formatter),
        _ => quote!(formatter),
    };

    quote! {
        impl Debug for Lite<syn::#ident> {
            fn fmt(&self, #formatter: &mut fmt::Formatter) -> fmt::Result {
                #body
            }
        }
    }
}

fn expand_token_impl(name: &str, symbol: &str) -> TokenStream {
    let ident = Ident::new(name, Span::call_site());
    let repr = format!("Token![{}]", symbol);

    quote! {
        impl Debug for Lite<syn::token::#ident> {
            fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                formatter.write_str(#repr)
            }
        }
    }
}

pub fn generate(defs: &Definitions) -> Result<()> {
    let mut impls = TokenStream::new();
    for node in &defs.types {
        impls.extend(expand_impl(defs, node));
    }
    for (name, symbol) in &defs.tokens {
        impls.extend(expand_token_impl(name, symbol));
    }

    file::write(
        TESTS_DEBUG_SRC,
        quote! {
            // False positive: https://github.com/rust-lang/rust/issues/115922
            #![allow(repr_transparent_non_zst_fields)]

            #![allow(clippy::match_wildcard_for_single_variants)]

            use super::{Lite, Present};
            use ref_cast::RefCast;
            use std::fmt::{self, Debug, Display};

            #impls
        },
    )?;

    Ok(())
}
