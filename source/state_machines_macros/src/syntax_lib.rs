//! Ordinary-library access to the same state-machine parser and generator.
#[macro_use]
mod vstd_path;
mod ast;
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

pub fn expand(
    input: proc_macro2::TokenStream,
    concurrent: bool,
    in_vstd: bool,
) -> verus_syn::Result<proc_macro2::TokenStream> {
    // The generator's path configuration is global. Ordinary-library calls can
    // run concurrently, unlike invocations in a compiler proc-macro server.
    static EXPANSION: std::sync::Mutex<()> = std::sync::Mutex::new(());
    let _guard = EXPANSION.lock().unwrap_or_else(|error| error.into_inner());
    vstd_path::set_is_vstd(in_vstd);
    vstd_path::set_is_core(false);
    expand::expand(input, concurrent)
}
