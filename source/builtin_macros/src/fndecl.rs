use proc_macro2::TokenStream;
use quote::quote;

#[inline(always)]
pub fn fndecl(input: TokenStream) -> TokenStream {
    quote! {
        #[verifier::spec] #[verifier::external_body] /* vattr */ #input { unimplemented!() }
    }
}
