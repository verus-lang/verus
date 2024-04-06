use syn_verus::spanned::Spanned;

pub fn derive_structural(s: synstructure::Structure) -> proc_macro2::TokenStream {
    let assert_receiver_is_structural_body = s
        .variants()
        .iter()
        .flat_map(|v| v.ast().fields)
        .map(|f| {
            let ty = &f.ty;
            quote_spanned_builtin! { builtin, ty.span() =>
                let _: #builtin::AssertParamIsStructural<#ty>;
            }
        })
        .collect::<proc_macro2::TokenStream>();
    s.gen_impl(quote_spanned_builtin! { builtin, s.ast().span() =>
        #[automatically_derived]
        gen impl #builtin::Structural for @Self {
            #[inline]
            #[doc(hidden)]
            fn assert_receiver_is_structural(&self) -> () {
                #assert_receiver_is_structural_body
            }
        }
    })
}
