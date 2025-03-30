use syn_verus::spanned::Spanned;

pub fn derive_structural(mut s: synstructure::Structure) -> proc_macro2::TokenStream {
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

    // TODO: this feature has disappeared in the latest version of synstructure
    // (this is why we still use a specific commit of synstructure)
    // see 'path.segments.iter().find(|s| s.starts_with("_DERIVE_builtin_Structural_FOR_")).is_some()' in rust_to_vir
    s.underscore_const(false);

    s.gen_impl(quote_spanned_builtin! { builtin, s.ast().span() =>
        #[automatically_derived]
        #[allow(non_local_definitions)]
        gen unsafe impl #builtin::Structural for @Self {
            #[inline]
            #[doc(hidden)]
            fn assert_receiver_is_structural(&self) -> () {
                #assert_receiver_is_structural_body
            }
        }
    })
}
