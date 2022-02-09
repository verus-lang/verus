use proc_macro2::TokenStream;
use quote::quote;

#[inline(always)]
pub fn fndecl(input: TokenStream) -> TokenStream {
    quote! {
        #[spec] #[verifier(external_body)] #input { unimplemented!() }
    }
}
