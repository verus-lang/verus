#![feature(box_patterns)]
#![feature(format_args_capture)]

extern crate proc_macro;

mod ast;
mod concurrency_tokens;
mod ident_visitor;
mod lemmas;
mod parse_token_stream;
mod parse_transition;
mod safety_conditions;
mod to_relation;
mod to_token_stream;
mod transitions;
mod util;

use lemmas::check_lemmas;
use parse_token_stream::{parse_result_to_smir, ParseResult};
use proc_macro::TokenStream;
use syn::parse_macro_input;
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

    match check_lemmas(&smir) {
        Ok(_) => {}
        Err(err) => {
            return TokenStream::from(err.to_compile_error());
        }
    }

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
