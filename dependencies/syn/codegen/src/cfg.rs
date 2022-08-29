use proc_macro2::TokenStream;
use quote::quote;
use syn_codegen::Features;

pub fn features(features: &Features) -> TokenStream {
    let features = &features.any;
    match features.len() {
        0 => quote!(),
        1 => quote!(#[cfg(feature = #(#features)*)]),
        _ => quote!(#[cfg(any(#(feature = #features),*))]),
    }
}
