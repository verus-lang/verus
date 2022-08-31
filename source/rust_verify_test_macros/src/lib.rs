#![feature(proc_macro_span)]
#![feature(path_file_prefix)]

mod examples;
mod rust_code;

use proc_macro::TokenStream;
use quote::quote;

#[proc_macro]
pub fn code(input: TokenStream) -> TokenStream {
    let src = rust_code::rust_code_core(input);
    quote!(#src.to_string()).into()
}

#[proc_macro]
pub fn verus_code(input: TokenStream) -> TokenStream {
    let src = "::builtin_macros::verus!{\n".to_string() + &rust_code::rust_code_core(input) + "}\n";
    quote!(#src.to_string()).into()
}

#[proc_macro]
pub fn code_str(input: TokenStream) -> TokenStream {
    let src = rust_code::rust_code_core(input);
    quote!(#src).into()
}

#[proc_macro]
pub fn verus_code_str(input: TokenStream) -> TokenStream {
    let src = "::builtin_macros::verus!{\n".to_string() + &rust_code::rust_code_core(input) + "}\n";
    quote!(#src).into()
}

#[proc_macro]
pub fn examples_in_dir(input: TokenStream) -> TokenStream {
    examples::examples_in_dir(input)
}
