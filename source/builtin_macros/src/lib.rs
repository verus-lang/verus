use quote::quote;
use synstructure::decl_derive;

decl_derive!([Structural] => derive_structural);

fn derive_structural(s: synstructure::Structure) -> proc_macro2::TokenStream {
    let assert_receiver_is_structural_body = s
        .variants()
        .iter()
        .flat_map(|v| v.ast().fields)
        .map(|f| {
            let ty = &f.ty;
            quote! {
                let _: ::builtin::AssertParamIsStructural<#ty>;
            }
        })
        .collect::<proc_macro2::TokenStream>();
    s.gen_impl(quote! {
        #[automatically_derived]
        gen impl ::builtin::Structural for @Self {
            #[inline]
            #[doc(hidden)]
            fn assert_receiver_is_structural(&self) -> () {
                #assert_receiver_is_structural_body
            }
        }
    })
}
