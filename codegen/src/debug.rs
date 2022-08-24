use crate::{cfg, file, lookup};
use anyhow::Result;
use proc_macro2::{Ident, Span, TokenStream};
use quote::{format_ident, quote};
use syn_codegen::{Data, Definitions, Node, Type};

const DEBUG_SRC: &str = "../src/gen/debug.rs";

fn expand_impl_body(defs: &Definitions, node: &Node) -> TokenStream {
    let type_name = &node.ident;
    let ident = Ident::new(type_name, Span::call_site());

    match &node.data {
        Data::Enum(variants) => {
            let arms = variants.iter().map(|(variant_name, fields)| {
                let variant = Ident::new(variant_name, Span::call_site());
                if fields.is_empty() {
                    quote! {
                        #ident::#variant => formatter.write_str(#variant_name),
                    }
                } else {
                    let pats = (0..fields.len())
                        .map(|i| format_ident!("v{}", i))
                        .collect::<Vec<_>>();
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
                            let mut formatter = formatter.debug_tuple(#variant_name);
                            #(formatter.field(#pats);)*
                            formatter.finish()
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
        Data::Struct(fields) => {
            let fields = fields.keys().map(|f| {
                let ident = Ident::new(f, Span::call_site());
                quote! {
                    formatter.field(#f, &self.#ident);
                }
            });
            quote! {
                let mut formatter = formatter.debug_struct(#type_name);
                #(#fields)*
                formatter.finish()
            }
        }
        Data::Private => unreachable!(),
    }
}

fn expand_impl(defs: &Definitions, node: &Node) -> TokenStream {
    let manual_debug = node.data == Data::Private || node.ident == "LitBool";
    if manual_debug {
        return TokenStream::new();
    }

    let ident = Ident::new(&node.ident, Span::call_site());
    let cfg_features = cfg::features(&node.features);
    let body = expand_impl_body(defs, node);

    quote! {
        #cfg_features
        #[cfg_attr(doc_cfg, doc(cfg(feature = "extra-traits")))]
        impl Debug for #ident {
            fn fmt(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
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
            use crate::*;
            use std::fmt::{self, Debug};

            #impls
        },
    )?;

    Ok(())
}
