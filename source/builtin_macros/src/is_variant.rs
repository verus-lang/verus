use quote::quote;

pub fn attribute_is_variant(
    _attr: proc_macro2::TokenStream,
    s: synstructure::Structure,
) -> proc_macro2::TokenStream {
    let ast = &s.ast();
    match ast.data {
        syn::Data::Enum(_) => {}
        _ => panic!("#[is_variant] is only allowed on enums"),
    }
    let struct_name = &s.ast().ident;
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

                        quote! {
                            #[spec]
                            #[allow(non_snake_case)]
                            #[verifier(get_variant(#variant_ident, #field_ident))]
                            pub fn #get_ident(self) -> #field_ty {
                                unimplemented!()
                            }
                        }
                    })
                    .collect::<proc_macro2::TokenStream>(),
                &syn::Fields::Unnamed(syn::FieldsUnnamed { unnamed: ref fields, .. }) => fields
                    .iter()
                    .zip(0..)
                    .map(|(f, i)| {
                        let field_ty = &f.ty;
                        let field_lit = syn::Lit::Int(syn::LitInt::new(
                            &format!("{}", i),
                            v.ast().ident.span(),
                        ));
                        let get_ident = syn::Ident::new(
                            &format!("get_{}_{}", variant_ident, i),
                            v.ast().ident.span(),
                        );

                        quote! {
                            #[spec]
                            #[allow(non_snake_case)]
                            #[verifier(get_variant(#variant_ident_str, #field_lit))]
                            pub fn #get_ident(self) -> #field_ty {
                                unimplemented!()
                            }
                        }
                    })
                    .collect::<proc_macro2::TokenStream>(),
                &syn::Fields::Unit => quote! {},
            };

            quote! {
                #[spec]
                #[verifier(is_variant(#variant_ident_str))]
                #[allow(non_snake_case)]
                pub fn #fun_ident(&self) -> bool { unimplemented!() }

                #get_fns
            }
        })
        .collect::<proc_macro2::TokenStream>();

    let generics = &ast.generics;
    quote! {
        #ast

        #[automatically_derived]
        impl#generics #struct_name#generics {
            #is_impls
        }
    }
}
