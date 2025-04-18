use crate::{cfg, file, full, lookup};
use anyhow::Result;
use proc_macro2::{Ident, Span, TokenStream};
use quote::{format_ident, quote};
use syn_codegen::{Data, Definitions, Node, Type};

const CLONE_SRC: &str = "src/gen/clone.rs";

fn expand_impl_body(defs: &Definitions, node: &Node) -> TokenStream {
    let type_name = &node.ident;
    let ident = Ident::new(type_name, Span::call_site());

    match &node.data {
        Data::Enum(variants) if variants.is_empty() => quote!(match *self {}),
        Data::Enum(variants) => {
            let mixed_derive_full = full::is_mixed_derive_full_enum(defs, node);
            let arms = variants.iter().map(|(variant_name, fields)| {
                let variant = Ident::new(variant_name, Span::call_site());
                if fields.is_empty() {
                    quote! {
                        crate::#ident::#variant => crate::#ident::#variant,
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
                    if mixed_derive_full {
                        if let Type::Syn(ty) = &fields[0] {
                            let features = &lookup::node(defs, ty).features;
                            if features.any.contains("full") && !features.any.contains("derive") {
                                cfg = Some(quote!(#[cfg(feature = "full")]));
                            }
                        }
                    }
                    quote! {
                        #cfg
                        crate::#ident::#variant(#(#pats),*) => crate::#ident::#variant(#(#clones),*),
                    }
                }
            });
            let nonexhaustive = if mixed_derive_full {
                Some(quote! {
                    #[cfg(not(feature = "full"))]
                    _ => unreachable!(),
                })
            } else {
                None
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
            quote!(crate::#ident { #(#fields)* })
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
    let cfg_features = cfg::features(&node.features, "clone-impls");

    let copy = node.ident == "AttrStyle"
        || node.ident == "BinOp"
        || node.ident == "RangeLimits"
        || node.ident == "TraitBoundModifier"
        || node.ident == "UnOp";
    if copy {
        return quote! {
            #cfg_features
            impl Copy for crate::#ident {}
            #cfg_features
            impl Clone for crate::#ident {
                fn clone(&self) -> Self {
                    *self
                }
            }
        };
    }

    let body = expand_impl_body(defs, node);

    quote! {
        #cfg_features
        impl Clone for crate::#ident {
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
        CLONE_SRC,
        quote! {
            #![allow(clippy::clone_on_copy, clippy::expl_impl_clone_on_copy)]

            #impls
        },
    )?;

    Ok(())
}
