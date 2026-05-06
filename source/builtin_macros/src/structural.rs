use verus_syn::spanned::Spanned;

pub fn derive_structural_mut(s: &mut synstructure::Structure) -> proc_macro2::TokenStream {
    if crate::cfg_erase() == crate::EraseGhost::EraseAll {
        return proc_macro2::TokenStream::new();
    }
    let assert_receiver_is_structural_body = s
        .variants()
        .iter()
        .flat_map(|v| v.ast().fields)
        .map(|f| {
            let ty = &f.ty;
            quote_spanned_builtin! { verus_builtin, ty.span() =>
                let _: #verus_builtin::AssertParamIsStructural<#ty>;
            }
        })
        .collect::<proc_macro2::TokenStream>();

    let mut tokens1 = quote::quote_spanned!(s.ast().span() =>
        #[verus::internal(structural_const_wrapper)]
    );
    let tokens2 = s.gen_impl(quote_spanned_builtin! { verus_builtin, s.ast().span() =>
        #[automatically_derived]
        #[allow(non_local_definitions)]
        gen unsafe impl #verus_builtin::Structural for @Self {
            #[inline]
            #[doc(hidden)]
            fn assert_receiver_is_structural(&self) -> () {
                #assert_receiver_is_structural_body
            }
        }
    });
    tokens1.extend(tokens2.into_iter());
    tokens1
}

pub fn derive_structural(mut s: synstructure::Structure) -> proc_macro2::TokenStream {
    derive_structural_mut(&mut s)
}

pub fn derive_structural_eq(mut s: synstructure::Structure) -> proc_macro2::TokenStream {
    if crate::cfg_erase() == crate::EraseGhost::EraseAll {
        return proc_macro2::TokenStream::new();
    }
    let mut tokens1 = derive_structural_mut(&mut s);
    let name = &s.ast().ident;
    let tokens2 = quote_spanned_builtin! { builtin, s.ast().span() =>
        #[automatically_derived]
        #[allow(non_local_definitions)]
        impl vstd::std_specs::cmp::PartialEqSpecImpl for #name {
            #[verus::internal(spec)]
            #[verus::internal(open)]
            fn obeys_eq_spec() -> bool {
                true
            }
            #[verus::internal(spec)]
            #[verus::internal(open)]
            fn eq_spec(&self, other: &Self) -> bool {
                #builtin::spec_eq(self, other)
            }
        }
    };
    tokens1.extend(tokens2.into_iter());
    tokens1
}
