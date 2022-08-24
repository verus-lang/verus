use crate::operand::{Borrowed, Operand, Owned};
use crate::{file, full, gen};
use anyhow::Result;
use proc_macro2::{Ident, Span, TokenStream};
use quote::{format_ident, quote};
use syn::Index;
use syn_codegen::{Data, Definitions, Features, Node, Type};

const VISIT_MUT_SRC: &str = "../src/gen/visit_mut.rs";

fn simple_visit(item: &str, name: &Operand) -> TokenStream {
    let ident = gen::under_name(item);
    let method = format_ident!("visit_{}_mut", ident);
    let name = name.ref_mut_tokens();
    quote! {
        v.#method(#name)
    }
}

fn noop_visit(name: &Operand) -> TokenStream {
    let name = name.tokens();
    quote! {
        skip!(#name)
    }
}

fn visit(
    ty: &Type,
    features: &Features,
    defs: &Definitions,
    name: &Operand,
) -> Option<TokenStream> {
    match ty {
        Type::Box(t) => {
            let name = name.owned_tokens();
            visit(t, features, defs, &Owned(quote!(*#name)))
        }
        Type::Vec(t) => {
            let operand = Borrowed(quote!(it));
            let val = visit(t, features, defs, &operand)?;
            let name = name.ref_mut_tokens();
            Some(quote! {
                for it in #name {
                    #val;
                }
            })
        }
        Type::Punctuated(p) => {
            let operand = Borrowed(quote!(it));
            let val = visit(&p.element, features, defs, &operand)?;
            let name = name.ref_mut_tokens();
            Some(quote! {
                for el in Punctuated::pairs_mut(#name) {
                    let (it, p) = el.into_tuple();
                    #val;
                    if let Some(p) = p {
                        tokens_helper(v, &mut p.spans);
                    }
                }
            })
        }
        Type::Option(t) => {
            let it = Borrowed(quote!(it));
            let val = visit(t, features, defs, &it)?;
            let name = name.owned_tokens();
            Some(quote! {
                if let Some(it) = &mut #name {
                    #val;
                }
            })
        }
        Type::Tuple(t) => {
            let mut code = TokenStream::new();
            for (i, elem) in t.iter().enumerate() {
                let name = name.tokens();
                let i = Index::from(i);
                let it = Owned(quote!((#name).#i));
                let val = visit(elem, features, defs, &it).unwrap_or_else(|| noop_visit(&it));
                code.extend(val);
                code.extend(quote!(;));
            }
            Some(code)
        }
        Type::Token(t) => {
            let name = name.tokens();
            let repr = &defs.tokens[t];
            let is_keyword = repr.chars().next().unwrap().is_alphabetic();
            let spans = if is_keyword {
                quote!(span)
            } else {
                quote!(spans)
            };
            Some(quote! {
                tokens_helper(v, &mut #name.#spans);
            })
        }
        Type::Group(_) => {
            let name = name.tokens();
            Some(quote! {
                tokens_helper(v, &mut #name.span);
            })
        }
        Type::Syn(t) => {
            fn requires_full(features: &Features) -> bool {
                features.any.contains("full") && features.any.len() == 1
            }
            let mut res = simple_visit(t, name);
            let target = defs.types.iter().find(|ty| ty.ident == *t).unwrap();
            if requires_full(&target.features) && !requires_full(features) {
                res = quote!(full!(#res));
            }
            Some(res)
        }
        Type::Ext(t) if gen::TERMINAL_TYPES.contains(&&t[..]) => Some(simple_visit(t, name)),
        Type::Ext(_) | Type::Std(_) => None,
    }
}

fn node(traits: &mut TokenStream, impls: &mut TokenStream, s: &Node, defs: &Definitions) {
    let under_name = gen::under_name(&s.ident);
    let ty = Ident::new(&s.ident, Span::call_site());
    let visit_mut_fn = format_ident!("visit_{}_mut", under_name);

    let mut visit_mut_impl = TokenStream::new();

    match &s.data {
        Data::Enum(variants) => {
            let mut visit_mut_variants = TokenStream::new();

            for (variant, fields) in variants {
                let variant_ident = Ident::new(variant, Span::call_site());

                if fields.is_empty() {
                    visit_mut_variants.extend(quote! {
                        #ty::#variant_ident => {}
                    });
                } else {
                    let mut bind_visit_mut_fields = TokenStream::new();
                    let mut visit_mut_fields = TokenStream::new();

                    for (idx, ty) in fields.iter().enumerate() {
                        let binding = format_ident!("_binding_{}", idx);

                        bind_visit_mut_fields.extend(quote! {
                            #binding,
                        });

                        let borrowed_binding = Borrowed(quote!(#binding));

                        visit_mut_fields.extend(
                            visit(ty, &s.features, defs, &borrowed_binding)
                                .unwrap_or_else(|| noop_visit(&borrowed_binding)),
                        );

                        visit_mut_fields.extend(quote!(;));
                    }

                    visit_mut_variants.extend(quote! {
                        #ty::#variant_ident(#bind_visit_mut_fields) => {
                            #visit_mut_fields
                        }
                    });
                }
            }

            let nonexhaustive = if s.exhaustive {
                None
            } else {
                Some(quote! {
                    #[cfg(syn_no_non_exhaustive)]
                    _ => unreachable!(),
                })
            };

            visit_mut_impl.extend(quote! {
                match node {
                    #visit_mut_variants
                    #nonexhaustive
                }
            });
        }
        Data::Struct(fields) => {
            for (field, ty) in fields {
                if let Type::Syn(ty) = ty {
                    if ty == "Reserved" {
                        continue;
                    }
                }

                let id = Ident::new(&field, Span::call_site());
                let ref_toks = Owned(quote!(node.#id));
                let visit_mut_field = visit(&ty, &s.features, defs, &ref_toks)
                    .unwrap_or_else(|| noop_visit(&ref_toks));
                visit_mut_impl.extend(quote! {
                    #visit_mut_field;
                });
            }
        }
        Data::Private => {
            if ty == "Ident" {
                visit_mut_impl.extend(quote! {
                    let mut span = node.span();
                    v.visit_span_mut(&mut span);
                    node.set_span(span);
                });
            }
        }
    }

    traits.extend(quote! {
        fn #visit_mut_fn(&mut self, i: &mut #ty) {
            #visit_mut_fn(self, i);
        }
    });

    impls.extend(quote! {
        pub fn #visit_mut_fn<V>(v: &mut V, node: &mut #ty)
        where
            V: VisitMut + ?Sized,
        {
            #visit_mut_impl
        }
    });
}

pub fn generate(defs: &Definitions) -> Result<()> {
    let (traits, impls) = gen::traverse(defs, node);
    let full_macro = full::get_macro();
    file::write(
        VISIT_MUT_SRC,
        quote! {
            #![allow(unused_variables)]

            #[cfg(any(feature = "full", feature = "derive"))]
            use crate::gen::helper::visit_mut::*;
            #[cfg(any(feature = "full", feature = "derive"))]
            use crate::punctuated::Punctuated;
            use crate::*;
            use proc_macro2::Span;

            #full_macro

            macro_rules! skip {
                ($($tt:tt)*) => {};
            }

            /// Syntax tree traversal to mutate an exclusive borrow of a syntax tree in
            /// place.
            ///
            /// See the [module documentation] for details.
            ///
            /// [module documentation]: self
            ///
            /// *This trait is available only if Syn is built with the `"visit-mut"` feature.*
            pub trait VisitMut {
                #traits
            }

            #impls
        },
    )?;
    Ok(())
}
