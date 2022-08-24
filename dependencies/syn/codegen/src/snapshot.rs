use crate::{file, lookup};
use anyhow::Result;
use proc_macro2::{Ident, Span, TokenStream};
use quote::{format_ident, quote};
use syn::Index;
use syn_codegen::{Data, Definitions, Node, Type};

const DEBUG_SRC: &str = "../tests/debug/gen.rs";

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
        Type::Syn(name) => name != "Reserved",
        Type::Std(_) | Type::Punctuated(_) | Type::Option(_) | Type::Vec(_) => true,
    }
}

fn format_field(val: &TokenStream, ty: &Type) -> Option<TokenStream> {
    if !is_printable(ty) {
        return None;
    }
    let format = match ty {
        Type::Option(ty) => {
            let inner = quote!(_val);
            let format = format_field(&inner, ty).map(|format| {
                quote! {
                    formatter.write_str("(")?;
                    Debug::fmt(#format, formatter)?;
                    formatter.write_str(")")?;
                }
            });
            let ty = rust_type(ty);
            quote!({
                #[derive(RefCast)]
                #[repr(transparent)]
                struct Print(Option<#ty>);
                impl Debug for Print {
                    fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                        match &self.0 {
                            Some(#inner) => {
                                formatter.write_str("Some")?;
                                #format
                                Ok(())
                            }
                            None => formatter.write_str("None"),
                        }
                    }
                }
                Print::ref_cast(#val)
            })
        }
        Type::Tuple(ty) => {
            let printable: Vec<TokenStream> = ty
                .iter()
                .enumerate()
                .filter_map(|(i, ty)| {
                    let index = Index::from(i);
                    let val = quote!(&#val.#index);
                    format_field(&val, ty)
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
        _ => quote! { Lite(#val) },
    };
    Some(format)
}

fn syntax_tree_enum<'a>(outer: &str, inner: &str, fields: &'a [Type]) -> Option<&'a str> {
    if fields.len() != 1 {
        return None;
    }
    const WHITELIST: &[&str] = &["PathArguments", "Visibility"];
    match &fields[0] {
        Type::Syn(ty) if WHITELIST.contains(&outer) || outer.to_owned() + inner == *ty => Some(ty),
        _ => None,
    }
}

fn expand_impl_body(defs: &Definitions, node: &Node, name: &str) -> TokenStream {
    let ident = Ident::new(&node.ident, Span::call_site());

    match &node.data {
        Data::Enum(variants) => {
            let arms = variants.iter().map(|(v, fields)| {
                let variant = Ident::new(v, Span::call_site());
                if fields.is_empty() {
                    quote! {
                        syn::#ident::#variant => formatter.write_str(#v),
                    }
                } else if let Some(inner) = syntax_tree_enum(name, v, fields) {
                    let path = format!("{}::{}", name, v);
                    let format = expand_impl_body(defs, lookup::node(defs, inner), &path);
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
                        format_field(&val, ty).map(|format| {
                            quote! {
                                formatter.write_str("(")?;
                                Debug::fmt(#format, formatter)?;
                                formatter.write_str(")")?;
                            }
                        })
                    };
                    quote! {
                        syn::#ident::#variant(_val) => {
                            formatter.write_str(#v)?;
                            #format
                            Ok(())
                        }
                    }
                } else {
                    let pats = (0..fields.len()).map(|i| format_ident!("_v{}", i));
                    let fields = fields.iter().enumerate().filter_map(|(i, ty)| {
                        let index = format_ident!("_v{}", i);
                        let val = quote!(#index);
                        let format = format_field(&val, ty)?;
                        Some(quote! {
                            formatter.field(#format);
                        })
                    });
                    quote! {
                        syn::#ident::#variant(#(#pats),*) => {
                            let mut formatter = formatter.debug_tuple(#v);
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
            quote! {
                match _val {
                    #(#arms)*
                    #nonexhaustive
                }
            }
        }
        Data::Struct(fields) => {
            let fields = fields.iter().filter_map(|(f, ty)| {
                let ident = Ident::new(f, Span::call_site());
                if let Type::Option(ty) = ty {
                    let inner = quote!(_val);
                    let format = format_field(&inner, ty).map(|format| {
                        quote! {
                            let #inner = &self.0;
                            formatter.write_str("(")?;
                            Debug::fmt(#format, formatter)?;
                            formatter.write_str(")")?;
                        }
                    });
                    let ty = rust_type(ty);
                    Some(quote! {
                        if let Some(val) = &_val.#ident {
                            #[derive(RefCast)]
                            #[repr(transparent)]
                            struct Print(#ty);
                            impl Debug for Print {
                                fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                                    formatter.write_str("Some")?;
                                    #format
                                    Ok(())
                                }
                            }
                            formatter.field(#f, Print::ref_cast(val));
                        }
                    })
                } else {
                    let val = quote!(&_val.#ident);
                    let format = format_field(&val, ty)?;
                    let mut call = quote! {
                        formatter.field(#f, #format);
                    };
                    if let Type::Vec(_) | Type::Punctuated(_) = ty {
                        call = quote! {
                            if !_val.#ident.is_empty() {
                                #call
                            }
                        };
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
                quote! {
                    write!(formatter, "{}", _val)
                }
            } else {
                quote! {
                    write!(formatter, "{:?}", _val.value())
                }
            }
        }
    }
}

fn expand_impl(defs: &Definitions, node: &Node) -> TokenStream {
    if node.ident == "Reserved" {
        return TokenStream::new();
    }

    let ident = Ident::new(&node.ident, Span::call_site());
    let body = expand_impl_body(defs, node, &node.ident);

    quote! {
        impl Debug for Lite<syn::#ident> {
            fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
                let _val = &self.value;
                #body
            }
        }
    }
}

pub fn generate(defs: &Definitions) -> Result<()> {
    let mut impls = TokenStream::new();
    for node in &defs.types {
        impls.extend(expand_impl(&defs, node));
    }

    file::write(
        DEBUG_SRC,
        quote! {
            use super::{Lite, RefCast};
            use std::fmt::{self, Debug, Display};

            #impls
        },
    )?;

    Ok(())
}
