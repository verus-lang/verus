#![allow(unused_imports)]
#![feature(box_patterns)]

extern crate proc_macro;

mod ast;
mod concurrency_tokens;
mod ident_visitor;
mod parse_token_stream;
mod parse_transition;
mod to_token_stream;
mod transitions;
mod weakest;

use parse_token_stream::{parse_result_to_smir, ParseResult};
use proc_macro::TokenStream;
use syn::{braced, parse_macro_input, Error, Expr, Field, FieldsNamed, Ident, ItemFn, Token, Type};
use to_token_stream::output_token_stream;

fn construct_state_machine(input: TokenStream, concurrent: bool) -> TokenStream {
    let pr: ParseResult = parse_macro_input!(input as ParseResult);

    let smir_res = parse_result_to_smir(pr, concurrent);
    let smir = match smir_res {
        Ok(smir) => smir,
        Err(err) => {
            return TokenStream::from(err.to_compile_error());
        }
    };

    let token_stream = match output_token_stream(smir, concurrent) {
        Ok(ts) => ts,
        Err(err) => {
            return TokenStream::from(err.to_compile_error());
        }
    };

    token_stream.into()
}

#[proc_macro]
pub fn state_machine(input: TokenStream) -> TokenStream {
    construct_state_machine(input, false)
}

#[proc_macro]
pub fn concurrent_state_machine(input: TokenStream) -> TokenStream {
    construct_state_machine(input, true)
}
