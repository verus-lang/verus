use crate::{cfg, file, full, lookup};
use anyhow::Result;
use proc_macro2::{Ident, Span, TokenStream};
use quote::{format_ident, quote};
use syn_codegen::{Data, Definitions, Node, Type};

const EQ_SRC: &str = "src/gen/eq.rs";

fn always_eq(field_type: &Type) -> bool {
    match field_type {
        Type::Ext(ty) => ty == "Span",
        Type::Token(_) | Type::Group(_) => true,
        Type::Box(inner) => always_eq(inner),
        Type::Tuple(inner) => inner.iter().all(always_eq),
        _ => false,
    }
}

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
                        (crate::#ident::#variant, crate::#ident::#variant) => true,
                    }
                } else {
                    let mut this_pats = Vec::new();
                    let mut other_pats = Vec::new();
                    let mut comparisons = Vec::new();
                    for (i, field) in fields.iter().enumerate() {
                        if always_eq(field) {
                            this_pats.push(format_ident!("_"));
                            other_pats.push(format_ident!("_"));
                            continue;
                        }
                        let this = format_ident!("self{}", i);
                        let other = format_ident!("other{}", i);
                        comparisons.push(match field {
                            Type::Ext(ty) if ty == "TokenStream" => {
                                quote!(TokenStreamHelper(#this) == TokenStreamHelper(#other))
                            }
                            Type::Ext(ty) if ty == "Literal" => {
                                quote!(#this.to_string() == #other.to_string())
                            }
                            _ => quote!(#this == #other),
                        });
                        this_pats.push(this);
                        other_pats.push(other);
                    }
                    if comparisons.is_empty() {
                        comparisons.push(quote!(true));
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
                        (crate::#ident::#variant(#(#this_pats),*), crate::#ident::#variant(#(#other_pats),*)) => {
                            #(#comparisons)&&*
                        }
                    }
                }
            });
            let fallthrough = if variants.len() == 1 {
                None
            } else {
                Some(quote!(_ => false,))
            };
            quote! {
                match (self, other) {
                    #(#arms)*
                    #fallthrough
                }
            }
        }
        Data::Struct(fields) => {
            let mut comparisons = Vec::new();
            for (f, ty) in fields {
                if always_eq(ty) {
                    continue;
                }
                let ident = Ident::new(f, Span::call_site());
                comparisons.push(match ty {
                    Type::Ext(ty) if ty == "TokenStream" => {
                        quote!(TokenStreamHelper(&self.#ident) == TokenStreamHelper(&other.#ident))
                    }
                    _ => quote!(self.#ident == other.#ident),
                });
            }
            if comparisons.is_empty() {
                quote!(true)
            } else {
                quote!(#(#comparisons)&&*)
            }
        }
        Data::Private => unreachable!(),
    }
}

fn expand_impl(defs: &Definitions, node: &Node) -> TokenStream {
    if node.ident == "Member" || node.ident == "Index" || node.ident == "Lifetime" {
        return TokenStream::new();
    }

    let ident = Ident::new(&node.ident, Span::call_site());
    let cfg_features = cfg::features(&node.features, "extra-traits");

    let eq = quote! {
        #cfg_features
        impl Eq for crate::#ident {}
    };

    let manual_partial_eq = node.data == Data::Private;
    if manual_partial_eq {
        return eq;
    }

    let body = expand_impl_body(defs, node);
    let other = match &node.data {
        Data::Enum(variants) if variants.is_empty() => quote!(_other),
        Data::Struct(fields) if fields.values().all(always_eq) => quote!(_other),
        _ => quote!(other),
    };

    quote! {
        #eq

        #cfg_features
        impl PartialEq for crate::#ident {
            fn eq(&self, #other: &Self) -> bool {
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
        EQ_SRC,
        quote! {
            #[cfg(any(feature = "derive", feature = "full"))]
            use crate::tt::TokenStreamHelper;

            #impls
        },
    )?;

    Ok(())
}
