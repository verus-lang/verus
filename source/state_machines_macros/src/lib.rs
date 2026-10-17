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
mod verified_tokens;
mod verified_general;
mod verified_monoids;
mod verified_ownership;
mod verified_model;
mod verified_state_relations;
mod verified_ergonomics;
mod verified_readiness;
mod verified_field_tokens;
mod verified_field_monoids;
mod verified_field_logical;
mod verified_field_collections;
mod verified_field_scalars;
mod verified_field_optional;
mod verified_field_mixed;
mod verified_field_control;
mod verified_field_storage;
mod verified_field_storage_grouped;

use case_macro::case_on;
use lemmas::check_lemmas;
use parse_token_stream::{ParseResult, parse_result_to_smir};
use proc_macro::TokenStream;
use to_token_stream::output_token_stream;
use verus_syn::parse_macro_input;

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

/// Emits checked nominal field APIs and frame-preserving protocol proofs.
/// Use `#[verified_raw_tokens]` inside the machine to request raw resources.
/// The former `#[verified_field_tokens]` marker remains compatible.
#[proc_macro]
pub fn verified_tokenized_state_machine(input: TokenStream) -> TokenStream {
    crate::vstd_path::set_is_vstd(false);
    crate::vstd_path::set_is_core(cfg_verify_core());
    let pr: ParseResult = parse_macro_input!(input as ParseResult);
    let result = verified_readiness::construct(pr);
    match result {
        Ok(output) => output.into(),
        Err(err) => err.to_compile_error().into(),
    }
}

/// Defines exact pure weak/strong state relations without resource APIs or
/// generated safety assumptions. Induction hooks remain checked proofs.
#[proc_macro]
pub fn verified_state_machine_model(input: TokenStream) -> TokenStream {
    crate::vstd_path::set_is_vstd(false);
    crate::vstd_path::set_is_core(cfg_verify_core());
    verified_model::construct(input)
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

mod verified_field_storage_roles;
mod verified_field_storage_readers;

mod verified_field_storage_borrows;

mod verified_field_sets;
mod verified_field_set_mixed;

mod verified_field_storage_heterogeneous;

mod verified_field_storage_counting;

mod verified_field_persistent_maps;

mod verified_field_storage_map;

mod verified_field_map_ordered;

mod verified_field_storage_multiple;

mod verified_storage_carrier;
mod verified_storage_homogeneous_carrier;

mod verified_field_storage_logical_map;

mod verified_field_storage_collections;

mod verified_field_interner;

mod verified_field_storage_rwlock;

mod verified_field_storage_imap_roles;
mod verified_field_storage_map_pair;
mod verified_field_storage_map_pair_transitions;

mod verified_field_storage_distributed_rwlock;
mod verified_field_variable_map;

mod verified_hidden_constants;

mod verified_field_top_sort;

mod verified_steps;
mod verified_take_step;

mod verified_field_storage_binding_maps;
mod verified_field_storage_bindings;
mod verified_field_storage_refutable;

mod verified_field_storage_general_bulk;

mod verified_field_nondet;

mod verified_storage_owned_imap;

// Complete mixed-storage field facade.
mod verified_field_storage_maps;
mod verified_field_storage_persistent_sets;
mod verified_field_storage_properties;
mod verified_field_storage_unique;
mod verified_field_storage_wide;
mod verified_field_storage_wide_transfers;
mod verified_field_storage_wide_transitions;
mod verified_field_storage_wide_transitions_plain;
