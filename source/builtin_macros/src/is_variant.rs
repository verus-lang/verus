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
            let get_ident =
                syn::Ident::new(&format!("get_{}", &variant_ident_str), v.ast().ident.span());
            let get_fn = match v.ast().fields {
                &syn::Fields::Named(_) | &syn::Fields::Unit => { quote! { } }
                &syn::Fields::Unnamed(syn::FieldsUnnamed { unnamed: ref fields, .. }) => {
                    let field_tys = fields.iter().map(|f| &f.ty).collect::<Vec<_>>();
                    let field_idents = fields.iter().zip(0..).map(|(_, i)| syn::Ident::new(&format!("e{}", i), v.ast().ident.span())).collect::<Vec<_>>();
                    quote! {
                        #[allow(non_snake_case)]
                        #[spec]
                        pub fn #get_ident(self) -> (#(#field_tys),*,) {
                            match self {
                                #struct_name::#variant_ident(#(#field_idents),*) => (#(#field_idents),*,),
                                _ => arbitrary(),
                            }
                        }
                    }
                },
            };

            quote! {
                #[doc(hidden)]
                #[spec]
                #[verifier(is_variant)]
                #[allow(non_snake_case)]
                pub fn #fun_ident(&self) -> bool { unimplemented!() }

                #get_fn
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
