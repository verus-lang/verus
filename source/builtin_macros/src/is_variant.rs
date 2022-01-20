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
            let variant_ident = v.ast().ident.to_string();

            let fun_ident =
                syn::Ident::new(&format!("is_{}", &variant_ident), v.ast().ident.span());
            quote! {
                #[doc(hidden)]
                #[spec]
                #[verifier(is_variant)]
                #[allow(non_snake_case)]
                fn #fun_ident(&self) -> bool { unimplemented!() }
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
