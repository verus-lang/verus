use std::sync::atomic::AtomicBool;

use quote::quote;
#[cfg(verus_keep_ghost)]
use syn::spanned::Spanned;

#[cfg(verus_keep_ghost)]
use crate::cfg_erase;

pub fn attribute_is_variant(
    attr: proc_macro2::TokenStream,
    s: synstructure::Structure,
) -> proc_macro2::TokenStream {
    attribute_is_variant_internal(attr, s, false)
}

pub fn attribute_is_variant_no_deprecation_warning(
    attr: proc_macro2::TokenStream,
    s: synstructure::Structure,
) -> proc_macro2::TokenStream {
    attribute_is_variant_internal(attr, s, true)
}

static IS_VARIANT_DEPRECATION_EMITTED: AtomicBool = AtomicBool::new(false);

fn attribute_is_variant_internal(
    _attr: proc_macro2::TokenStream,
    s: synstructure::Structure,
    #[cfg_attr(not(verus_keep_ghost), allow(unused_variables))] no_deprecation_warning: bool,
) -> proc_macro2::TokenStream {
    let ast = &s.ast();
    match ast.data {
        syn::Data::Enum(_) => {}
        _ => {
            return quote! { compile_error!("#[is_variant] is only allowed on enums\nthis message will only be emitted for the first invocation encountered"); };
        }
    }

    if IS_VARIANT_DEPRECATION_EMITTED
        .compare_exchange(
            false,
            true,
            std::sync::atomic::Ordering::SeqCst,
            std::sync::atomic::Ordering::SeqCst,
        )
        .is_ok()
    {
        #[cfg(verus_keep_ghost)]
        if !cfg_erase().erase() && !no_deprecation_warning {
            proc_macro::Diagnostic::spanned(
                ast.span().unwrap(),
                proc_macro::Level::Warning,
                "`#[is_variant]` is deprecated - use `->` or `matches` instead",
            )
            .emit();
        }
    }

    let struct_name = &s.ast().ident;
    let vis = &ast.vis;
    let publish = if matches!(vis, syn::Visibility::Inherited) {
        quote! {}
    } else {
        quote! {
            #[verus::internal(open)]
        }
    };
    let is_impls = s
        .variants()
        .iter()
        .map(|v| {
            let variant_ident = v.ast().ident;
            let variant_ident_str = variant_ident.to_string();
            let fun_ident =
                syn::Ident::new(&format!("is_{}", &variant_ident_str), v.ast().ident.span());
            let get_fns = match v.ast().fields {
                &syn::Fields::Named(syn::FieldsNamed { named: ref fields, .. }) => fields
                    .iter()
                    .map(|f| {
                        let field_ty = &f.ty;
                        let field_ident = f.ident.as_ref().expect("missing field ident");
                        let get_ident = syn::Ident::new(
                            &format!("get_{}_{}", variant_ident_str, field_ident.to_string()),
                            v.ast().ident.span(),
                        );
                        let field_str = field_ident.to_string();

                        quote_spanned_builtin! { builtin, get_ident.span() =>
                            #[cfg(verus_keep_ghost)]
                            #[allow(non_snake_case)]
                            #[verus::internal(spec)]
                            #[verifier::inline]
                            #publish
                            #vis fn #get_ident(self) -> #field_ty {
                                #builtin::get_variant_field(self, #variant_ident_str, #field_str)
                            }
                        }
                    })
                    .collect::<proc_macro2::TokenStream>(),
                &syn::Fields::Unnamed(syn::FieldsUnnamed { unnamed: ref fields, .. }) => fields
                    .iter()
                    .zip(0..)
                    .map(|(f, i)| {
                        let field_ty = &f.ty;
                        let field_lit = format!("{}", i);
                        let get_ident = syn::Ident::new(
                            &format!("get_{}_{}", variant_ident, i),
                            v.ast().ident.span(),
                        );

                        quote_spanned_builtin! { builtin, get_ident.span() =>
                            #[cfg(verus_keep_ghost)]
                            #[allow(non_snake_case)]
                            #[verus::internal(spec)]
                            #[verifier::inline]
                            #publish
                            #vis fn #get_ident(self) -> #field_ty {
                                #builtin::get_variant_field(self, #variant_ident_str, #field_lit)
                            }
                        }
                    })
                    .collect::<proc_macro2::TokenStream>(),
                &syn::Fields::Unit => quote! {},
            };

            quote_spanned_builtin! { builtin, variant_ident.span() =>
                ::builtin_macros::verus! {
                    #[cfg(verus_keep_ghost)]
                    #[allow(non_snake_case)]
                    #[verus::internal(spec)]
                    #[verifier::inline]
                    #publish
                    #vis fn #fun_ident(&self) -> bool {
                        #builtin::is_variant(self, #variant_ident_str)
                    }

                    #get_fns
                }
            }
        })
        .collect::<proc_macro2::TokenStream>();

    let generics = &ast.generics;
    let (impl_generics, ty_generics, where_clause) = generics.split_for_impl();

    quote! {
        #ast

        #[verus::internal(verus_macro)]
        #[cfg(verus_keep_ghost)]
        #[automatically_derived]
        impl #impl_generics #struct_name #ty_generics #where_clause {
            #is_impls
        }
    }
}
