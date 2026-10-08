#![cfg_attr(verus_keep_ghost, feature(proc_macro_expand))]

extern crate proc_macro;

#[macro_use]
mod vstd_path;

mod ast;
mod case_macro;
mod check_bind_stmts;
mod check_birds_eye;
mod concurrency_tokens;
mod expand;
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
use proc_macro::TokenStream;

fn construct_state_machine(input: TokenStream, concurrent: bool) -> TokenStream {
    match expand::expand(input.into(), concurrent) {
        Ok(tokens) => tokens.into(),
        Err(error) => error.to_compile_error().into(),
    }
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
