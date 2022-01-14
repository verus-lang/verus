extern crate proc_macro;

mod parse_token_stream;

use proc_macro::TokenStream;
use parse_token_stream::{parse_result_to_smir, ParseResult};
use syn::{parse_macro_input, ItemFn, braced, Ident, Field, Token, Error, FieldsNamed, Expr, Type};

#[proc_macro]
pub fn construct_state_machine(input: TokenStream) -> TokenStream {
    let pr: ParseResult = parse_macro_input!(input as ParseResult);

    let smir_res = parse_result_to_smir(pr);
    let smir = match smir_res {
        Ok(smir) => smir,
        Err(err) => { return TokenStream::from(err.to_compile_error()); }
    };

    panic!("not impl construct_state_machine");
}
