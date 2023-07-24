use proc_macro2::TokenStream;
use quote::quote;

#[inline(always)]
pub fn fndecl(input: TokenStream) -> TokenStream {
    quote! {
        #[cfg_attr(verus_macro_keep_ghost, verifier::spec)] #[cfg_attr(verus_macro_keep_ghost, verifier::external_body)] /* vattr */ #input { unimplemented!() }
    }
}
