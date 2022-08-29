use crate::{cfg, file, lookup};
use anyhow::Result;
use proc_macro2::{Ident, Span, TokenStream};
use quote::{format_ident, quote};
use syn_codegen::{Data, Definitions, Node, Type};

const DEBUG_SRC: &str = "../src/gen/hash.rs";

fn skip(field_type: &Type) -> bool {
    match field_type {
        Type::Syn(node) => node == "Reserved",
        Type::Ext(ty) => ty == "Span",
        Type::Token(_) | Type::Group(_) => true,
        Type::Box(inner) => skip(inner),
        Type::Tuple(inner) => inner.iter().all(skip),
        _ => false,
    }
}

fn expand_impl_body(defs: &Definitions, node: &Node) -> TokenStream {
    let type_name = &node.ident;
    let ident = Ident::new(type_name, Span::call_site());

    match &node.data {
        Data::Enum(variants) => {
            let arms = variants
                .iter()
                .enumerate()
                .map(|(i, (variant_name, fields))| {
                    let i = i as u8;
                    let variant = Ident::new(variant_name, Span::call_site());
                    if fields.is_empty() {
                        quote! {
                            #ident::#variant => {
                                state.write_u8(#i);
                            }
                        }
                    } else {
                        let mut pats = Vec::new();
                        let mut hashes = Vec::new();
                        for (i, field) in fields.iter().enumerate() {
                            if skip(field) {
                                pats.push(format_ident!("_"));
                                continue;
                            }
                            let var = format_ident!("v{}", i);
                            let mut hashed_val = quote!(#var);
                            match field {
                                Type::Ext(ty) if ty == "TokenStream" => {
                                    hashed_val = quote!(TokenStreamHelper(#hashed_val));
                                }
                                Type::Ext(ty) if ty == "Literal" => {
                                    hashed_val = quote!(#hashed_val.to_string());
                                }
                                _ => {}
                            }
                            hashes.push(quote! {
                                #hashed_val.hash(state);
                            });
                            pats.push(var);
                        }
                        let mut cfg = None;
                        if node.ident == "Expr" {
                            if let Type::Syn(ty) = &fields[0] {
                                if !lookup::node(defs, ty).features.any.contains("derive") {
                                    cfg = Some(quote!(#[cfg(feature = "full")]));
                                }
                            }
                        }
                        quote! {
                            #cfg
                            #ident::#variant(#(#pats),*) => {
                                state.write_u8(#i);
                                #(#hashes)*
                            }
                        }
                    }
                });
            let nonexhaustive = if node.exhaustive {
                None
            } else if node.ident == "Expr" {
                Some(quote! {
                    #[cfg(any(syn_no_non_exhaustive, not(feature = "full")))]
                    _ => unreachable!(),
                })
            } else {
                Some(quote! {
                    #[cfg(syn_no_non_exhaustive)]
                    _ => unreachable!(),
                })
            };
            quote! {
                match self {
                    #(#arms)*
                    #nonexhaustive
                }
            }
        }
        Data::Struct(fields) => fields
            .iter()
            .filter_map(|(f, ty)| {
                if skip(ty) {
                    return None;
                }
                let ident = Ident::new(f, Span::call_site());
                let mut val = quote!(self.#ident);
                if let Type::Ext(ty) = ty {
                    if ty == "TokenStream" {
                        val = quote!(TokenStreamHelper(&#val));
                    }
                }
                Some(quote! {
                    #val.hash(state);
                })
            })
            .collect(),
        Data::Private => unreachable!(),
    }
}

fn expand_impl(defs: &Definitions, node: &Node) -> TokenStream {
    let manual_hash = node.data == Data::Private
        || node.ident == "Member"
        || node.ident == "Index"
        || node.ident == "Lifetime";
    if manual_hash {
        return TokenStream::new();
    }

    let ident = Ident::new(&node.ident, Span::call_site());
    let cfg_features = cfg::features(&node.features);

    let body = expand_impl_body(defs, node);
    let state = if body.is_empty() {
        quote!(_state)
    } else {
        quote!(state)
    };

    quote! {
        #cfg_features
        #[cfg_attr(doc_cfg, doc(cfg(feature = "extra-traits")))]
        impl Hash for #ident {
            fn hash<H>(&self, #state: &mut H)
            where
                H: Hasher,
            {
                #body
            }
        }
    }
}

pub fn generate(defs: &Definitions) -> Result<()> {
    let mut impls = TokenStream::new();
    for node in &defs.types {
        impls.extend(expand_impl(defs, node));
    }

    file::write(
        DEBUG_SRC,
        quote! {
            #[cfg(any(feature = "derive", feature = "full"))]
            use crate::tt::TokenStreamHelper;
            use crate::*;
            use std::hash::{Hash, Hasher};

            #impls
        },
    )?;

    Ok(())
}
