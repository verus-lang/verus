use proc_macro2::TokenStream;
use quote::quote;
use syn::{braced, parse_macro_input, Error, Expr, Field, FieldsNamed, Ident, Token, Type};

#[inline(always)]
pub fn fndef(input: TokenStream) -> TokenStream {
    quote! {
        #[spec] #[verifier(external_body)] #input { unimplemented!() }
    }
}
