use crate::{cfg, file, lookup};
use anyhow::Result;
use proc_macro2::{Ident, Span, TokenStream};
use quote::{format_ident, quote};
use syn_codegen::{Data, Definitions, Node, Type};

const DEBUG_SRC: &str = "../src/gen/clone.rs";

fn expand_impl_body(defs: &Definitions, node: &Node) -> TokenStream {
    let type_name = &node.ident;
    let ident = Ident::new(type_name, Span::call_site());

    match &node.data {
        Data::Enum(variants) => {
            let arms = variants.iter().map(|(variant_name, fields)| {
                let variant = Ident::new(variant_name, Span::call_site());
                if fields.is_empty() {
                    quote! {
                        #ident::#variant => #ident::#variant,
                    }
                } else {
                    let mut pats = Vec::new();
                    let mut clones = Vec::new();
                    for i in 0..fields.len() {
                        let pat = format_ident!("v{}", i);
                        clones.push(quote!(#pat.clone()));
                        pats.push(pat);
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
                        #ident::#variant(#(#pats),*) => #ident::#variant(#(#clones),*),
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
        Data::Struct(fields) => {
            let fields = fields.keys().map(|f| {
                let ident = Ident::new(f, Span::call_site());
                quote! {
                    #ident: self.#ident.clone(),
                }
            });
            quote!(#ident { #(#fields)* })
        }
        Data::Private => unreachable!(),
    }
}

fn expand_impl(defs: &Definitions, node: &Node) -> TokenStream {
    let manual_clone = node.data == Data::Private || node.ident == "Lifetime";
    if manual_clone {
        return TokenStream::new();
    }

    let ident = Ident::new(&node.ident, Span::call_site());
    let cfg_features = cfg::features(&node.features);

    let copy = node.ident == "AttrStyle"
        || node.ident == "BinOp"
        || node.ident == "RangeLimits"
        || node.ident == "TraitBoundModifier"
        || node.ident == "UnOp";
    if copy {
        return quote! {
            #cfg_features
            #[cfg_attr(doc_cfg, doc(cfg(feature = "clone-impls")))]
            impl Copy for #ident {}
            #cfg_features
            #[cfg_attr(doc_cfg, doc(cfg(feature = "clone-impls")))]
            impl Clone for #ident {
                fn clone(&self) -> Self {
                    *self
                }
            }
        };
    }

    let body = expand_impl_body(defs, node);

    quote! {
        #cfg_features
        #[cfg_attr(doc_cfg, doc(cfg(feature = "clone-impls")))]
        impl Clone for #ident {
            fn clone(&self) -> Self {
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
            #![allow(clippy::clone_on_copy, clippy::expl_impl_clone_on_copy)]

            use crate::*;

            #impls
        },
    )?;

    Ok(())
}
