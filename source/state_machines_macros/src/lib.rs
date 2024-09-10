#![cfg_attr(verus_keep_ghost, feature(proc_macro_expand))]

extern crate proc_macro;

#[macro_use]
mod vstd_path;

mod ast;
mod case_macro;
mod check_bind_stmts;
mod check_birds_eye;
mod concurrency_tokens;
mod field_access_visitor;
mod ident_visitor;
mod inherent_safety_conditions;
mod lemmas;
mod parse_token_stream;
mod parse_transition;
mod safety_conditions;
mod self_type_visitor;
mod simplification;
mod simplify_asserts;
mod to_relation;
mod to_token_stream;
mod token_transition_checks;
mod transitions;
mod util;

use case_macro::case_on;
use lemmas::check_lemmas;
use parse_token_stream::{parse_result_to_smir, ParseResult};
use proc_macro::TokenStream;
use syn_verus::parse_macro_input;
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
    crate::vstd_path::set_is_vstd(false);
    crate::vstd_path::set_is_core(cfg_verify_core());
    construct_state_machine(input, false)
}

#[proc_macro]
pub fn tokenized_state_machine(input: TokenStream) -> TokenStream {
    crate::vstd_path::set_is_vstd(false);
    crate::vstd_path::set_is_core(cfg_verify_core());
    construct_state_machine(input, true)
}

#[proc_macro]
pub fn tokenized_state_machine_vstd(input: TokenStream) -> TokenStream {
    crate::vstd_path::set_is_vstd(true);
    crate::vstd_path::set_is_core(cfg_verify_core());
    construct_state_machine(input, true)
}

#[proc_macro]
pub fn case_on_next(input: TokenStream) -> TokenStream {
    case_on(input, false, false)
}

#[proc_macro]
pub fn case_on_next_strong(input: TokenStream) -> TokenStream {
    case_on(input, false, true)
}

#[proc_macro]
pub fn case_on_init(input: TokenStream) -> TokenStream {
    case_on(input, true, false)
}

#[cfg(verus_keep_ghost)]
pub(crate) fn cfg_verify_core() -> bool {
    static CFG_VERIFY_CORE: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *CFG_VERIFY_CORE.get_or_init(|| {
        let ts: proc_macro::TokenStream = quote::quote! { ::core::cfg!(verus_verify_core) }.into();
        let bool_ts = match ts.expand_expr() {
            Ok(name) => name.to_string(),
            _ => {
                panic!("cfg_verify_core call failed")
            }
        };
        match bool_ts.as_str() {
            "true" => true,
            "false" => false,
            _ => {
                panic!("cfg_verify_core call failed")
            }
        }
    })
}

// Because 'expand_expr' is unstable, we need a different impl when `not(verus_keep_ghost)`.
#[cfg(not(verus_keep_ghost))]
pub(crate) fn cfg_verify_core() -> bool {
    false
}
