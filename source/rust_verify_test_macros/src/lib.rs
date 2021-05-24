#![feature(proc_macro_span)]

// ACKNOWLEDGEMENT: adapted from Mara Bos' (@m_ou_se) https://blog.m-ou.se/writing-python-inside-rust-2/

use proc_macro::TokenStream;
use quote::quote;

fn rust_code_core(input: TokenStream) -> String {
    let mut tokens = input.into_iter();
    let mut span = tokens.next().unwrap().span();
    while let Some(token) = tokens.next() {
        span = span.join(token.span()).unwrap();
    }

    let src = span.source_text().unwrap();
    let n = span.start().column;
    let original_src = src;
    let mut src = String::new();
    let mut lines = original_src.lines();
    src += lines.next().unwrap();
    src += "\n";
    for line in lines {
        let (indent, line) = line.split_at(n.min(line.len()));
        assert!(!indent.contains(|c| c != ' '), "Invalid indentation");
        src += line;
        src += "\n";
    }
    src
}

#[proc_macro]
pub fn rust_code(input: TokenStream) -> TokenStream {
    let src = rust_code_core(input);
    quote!(#src.to_string()).into()
}

#[proc_macro]
pub fn rust_code_str(input: TokenStream) -> TokenStream {
    let src = rust_code_core(input);
    quote!(#src).into()
}
