use proc_macro2::TokenStream;
use quote::quote;

pub enum Operand {
    Borrowed(TokenStream),
    Owned(TokenStream),
}

pub use self::Operand::*;

impl Operand {
    pub fn tokens(&self) -> &TokenStream {
        match self {
            Borrowed(n) | Owned(n) => n,
        }
    }

    pub fn ref_tokens(&self) -> TokenStream {
        match self {
            Borrowed(n) => n.clone(),
            Owned(n) => quote!(&#n),
        }
    }

    pub fn ref_mut_tokens(&self) -> TokenStream {
        match self {
            Borrowed(n) => n.clone(),
            Owned(n) => quote!(&mut #n),
        }
    }

    pub fn owned_tokens(&self) -> TokenStream {
        match self {
            Borrowed(n) => quote!(*#n),
            Owned(n) => n.clone(),
        }
    }
}
