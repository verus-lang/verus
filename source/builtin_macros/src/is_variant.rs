use quote::quote;

pub fn attribute_is_variant(
    _attr: proc_macro2::TokenStream,
    s: synstructure::Structure,
) -> proc_macro2::TokenStream {
    let ast = &s.ast();
    match ast.data {
        syn::Data::Enum(_) => {}
        _ => return quote! { compile_error!("#[is_variant] is only allowed on enums"); },
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

                        quote! {
                            #[cfg(verus_keep_ghost)]
                            #[allow(non_snake_case)]
                            #[verus::internal(spec)]
                            #[verifier::inline]
                            #publish
                            #vis fn #get_ident(self) -> #field_ty {
                                ::builtin::get_variant_field(self, #variant_ident_str, #field_str)
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

                        quote! {
                            #[cfg(verus_keep_ghost)]
                            #[allow(non_snake_case)]
                            #[verus::internal(spec)]
                            #[verifier::inline]
                            #publish
                            #vis fn #get_ident(self) -> #field_ty {
                                ::builtin::get_variant_field(self, #variant_ident_str, #field_lit)
                            }
                        }
                    })
                    .collect::<proc_macro2::TokenStream>(),
                &syn::Fields::Unit => quote! {},
            };

            quote! {
                ::builtin_macros::verus! {
                    #[cfg(verus_keep_ghost)]
                    #[allow(non_snake_case)]
                    #[verus::internal(spec)]
                    #[verifier::inline]
                    #publish
                    #vis fn #fun_ident(&self) -> bool {
                        ::builtin::is_variant(self, #variant_ident_str)
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

        #[cfg(verus_keep_ghost)]
        #[automatically_derived]
        impl #impl_generics #struct_name #ty_generics #where_clause {
            #is_impls
        }
    }
}
