// Branch-condition (MC/DC) coverage tests: the tokenized state machine macros (state_machines_macros).
// Each test's comment names the decisions (file:line) and the conditions (atoms, numbered from 0
// in source order) for which the test supplies an evaluation that no other test supplies, so that
// the condition is shown to independently change the decision's outcome. See
// COVERAGE-UNREACHABLE.md for the conditions that no test can cover.
#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

// Independence pair for state_machines_macros/src/parse_transition.rs:705 atom 0; state_machines_macros/src/to_token_stream.rs:245 atoms 0, 1, 2, 3, 4, 5, 6
test_verify_one_file! {
    #[test] sm_attrs_deleted verus_code! {
        use vstd::prelude::*;
        use verus_state_machines_macros::*;

        pub enum E { A, B, C, D }
        state_machine!{ X {
            fields { pub x: int, pub e: E }

            #[invariant]
            #[safety]
            #[transition]
            #[readonly]
            #[init]
            #[sharding(variable)]
            #[allow(dead_code)]
            pub fn inv_pos(&self) -> bool { self.x >= 0 }

            init!{
                initialize() {
                    init x = 0;
                    init e = E::A;
                }
            }

            transition!{
                step() {
                    match pre.e {
                        E::A | E::B => { update x = pre.x + 1; }
                        | E::C => { update x = pre.x + 2; }
                        E::D => { }
                    }
                }
            }

            #[inductive(initialize)]
            fn init_ok(post: Self) { }

            #[inductive(step)]
            fn step_ok(pre: Self, post: Self) { }

        }}
    } => Ok(())
}

// Independence pair for state_machines_macros/src/parse_token_stream.rs:210 atom 0 `name == "spec"`, atom 1 `name == "proof"`, atom 2 `name == "exec"`
test_verify_one_file! {
    #[test] sm_field_mode_exec verus_code! {
        use vstd::prelude::*;
        use verus_state_machines_macros::*;

        state_machine!{  X {
            fields { #[verifier::opaque] #[verifier::exec] pub x: int }

            init!{ initialize() { init x = 0; } }
        }}
    } => Err(err) => assert_vir_error_msg(err, "a state field is implied to be 'spec'; it should not be explicitly labelled")
}

// Independence pair for state_machines_macros/src/ident_visitor.rs:272 atom 0 `expr_path.qself.is_none()`
test_verify_one_file! {
    #[test] sm_ident_shadow verus_code! {
        use vstd::prelude::*;
        use verus_state_machines_macros::*;

        state_machine!{ X {
            fields { pub x: int, pub y: int }
            #[invariant]
            pub fn inv(&self) -> bool { self.y >= 0 }
            init!{ initialize() { init x = 0; init y = 0; } }
            transition!{
                step() {
                    let x: int = 7;
                    let m: int = <u8>::MAX as int;
                    update x = x + m;
                    update y = pre.y + 1;
                }
            }
            #[inductive(initialize)]
            fn init_ok(post: Self) { }
            #[inductive(step)]
            fn step_ok(pre: Self, post: Self) { assert(post.x == 7 + 255); }
        }}
    } => Ok(())
}

// Independence pair for state_machines_macros/src/ident_visitor.rs:277 atom 0 `self.field_names.contains(&id)`, atom 1 `!self.bound_names.contains(&id)`
test_verify_one_file! {
    #[test] sm_ident_unbound_field verus_code! {
        use vstd::prelude::*;
        use verus_state_machines_macros::*;

        state_machine!{ X {
            fields { pub x: int, pub y: int }
            init!{ initialize() { init x = 0; init y = 0; } }
            transition!{
                step() {
                    let x: int = 7;
                    update x = x + ::core::primitive::u8::MAX as int;
                    update y = y + 1;
                }
            }
        }}
    } => Err(err) => assert_vir_error_msg(err, "Use `pre.y` to access this field's value")
}

// Independence pair for state_machines_macros/src/parse_token_stream.rs:746 atom 0 `attrs.len() > 0`
test_verify_one_file! {
    #[test] sm_label_attr verus_code! {
        use vstd::prelude::*;
        use verus_state_machines_macros::*;

        state_machine!{  X<T> {
            fields { pub t: Option<T>, pub x: int }
            pub type Label<#[cfg(all())] T> = Option<T>;
            init!{ initialize() { init x = 0; } }
        }}
    } => Err(err) => assert_vir_error_msg(err, "unsupported type param")
}

// Independence pair for state_machines_macros/src/parse_token_stream.rs:746 atom 1 `colon_token.is_some()`
test_verify_one_file! {
    #[test] sm_label_colon verus_code! {
        use vstd::prelude::*;
        use verus_state_machines_macros::*;

        state_machine!{  X<T> {
            fields { pub t: Option<T>, pub x: int }
            pub type Label<T:> = Option<T>;
            init!{ initialize() { init x = 0; } }
        }}
    } => Err(err) => assert_vir_error_msg(err, "unsupported type param")
}

// Independence pair for state_machines_macros/src/parse_token_stream.rs:746 atom 3 `eq_token.is_some()`
test_verify_one_file! {
    #[test] sm_label_default verus_code! {
        use vstd::prelude::*;
        use verus_state_machines_macros::*;

        state_machine!{  X<T> {
            fields { pub t: Option<T>, pub x: int }
            pub struct Label<T = u8> { pub t: Option<T> }
            init!{ initialize() { init x = 0; } }
        }}
    } => Err(err) => assert_vir_error_msg(err, "unsupported type param")
}

// Independence pair for state_machines_macros/src/ident_visitor.rs:272 atom 2 `expr_path.path.leading_colon.is_n...`
test_verify_one_file! {
    #[test] sm_leading_colon code! {
        use vstd::prelude::*;
        use verus_state_machines_macros::state_machine;

        state_machine!{ X {
            fields { pub t: int }

            transition!{
                tr() {
                    update t = ::t;
                }
            }
        }}
    } => Err(err) => assert_rust_error_msg(err, "cannot find crate `t` in the list of imported crates")
}

// Independence pair for state_machines_macros/src/lemmas.rs:341 atom 0 `path.is_ident("requires")`, atom 1 `path.is_ident("ensures")`
test_verify_one_file! {
    #[test] sm_lemma_header_ensures verus_code! {
        use vstd::prelude::*;
        use verus_state_machines_macros::*;

        pub proof fn noop() {}
        state_machine!{ X {
            fields { pub x: int }
            #[invariant]
            pub fn inv(&self) -> bool { self.x >= 0 }
            init!{ initialize() { init x = 0; } }
            transition!{ step() { update x = pre.x + 1; } }
            #[inductive(initialize)]
            fn init_ok(post: Self) { noop(); }
            #[inductive(step)]
            fn step_ok(pre: Self, post: Self) { ensures(true); }
        }}
    } => Err(err) => assert_vir_error_msg(err, "header statement here was probably a mistake: in an inductiveness lemma, the precondition and")
}

// Independence pair for state_machines_macros/src/parse_transition.rs:705 atom 3 `!input.peek(Token![|=])`
test_verify_one_file! {
    #[test] sm_match_oreq1 verus_code! {
        use vstd::prelude::*;
        use verus_state_machines_macros::*;

        pub enum E { A, B, C, D, F }
        state_machine!{ X {
            fields { pub e: E }
            init!{ initialize() { init e = E::A; } }
            transition!{
                step() {
                    match pre.e {
                        E::D | E::F => { }
                        E::A |= E::B => { }
                        _ => { }
                    }
                }
            }
        }}
    } => Err(err) => assert_vir_error_msg(err, "expected `=>`")
}

// Independence pair for state_machines_macros/src/parse_transition.rs:710 atom 2 `!input.peek(Token![|=])`
test_verify_one_file! {
    #[test] sm_match_oreq2 verus_code! {
        use vstd::prelude::*;
        use verus_state_machines_macros::*;

        pub enum E { A, B, C, D, F }
        state_machine!{ X {
            fields { pub e: E }
            init!{ initialize() { init e = E::A; } }
            transition!{
                step() {
                    match pre.e {
                        E::D | E::F => { }
                        E::A | E::B |= E::C => { }
                        _ => { }
                    }
                }
            }
        }}
    } => Err(err) => assert_vir_error_msg(err, "expected `=>`")
}

// Independence pair for state_machines_macros/src/parse_transition.rs:705 atom 2 `!input.peek(Token![||])`
test_verify_one_file! {
    #[test] sm_match_oror1 verus_code! {
        use vstd::prelude::*;
        use verus_state_machines_macros::*;

        pub enum E { A, B, C, D, F }
        state_machine!{ X {
            fields { pub e: E }
            init!{ initialize() { init e = E::A; } }
            transition!{
                step() {
                    match pre.e {
                        E::D | E::F => { }
                        E::A || E::B => { }
                        _ => { }
                    }
                }
            }
        }}
    } => Err(err) => assert_vir_error_msg(err, "expected `=>`")
}

// Independence pair for state_machines_macros/src/parse_transition.rs:710 atom 1 `!input.peek(Token![||])`
test_verify_one_file! {
    #[test] sm_match_oror2 verus_code! {
        use vstd::prelude::*;
        use verus_state_machines_macros::*;

        pub enum E { A, B, C, D, F }
        state_machine!{ X {
            fields { pub e: E }
            init!{ initialize() { init e = E::A; } }
            transition!{
                step() {
                    match pre.e {
                        E::D | E::F => { }
                        E::A | E::B || E::C => { }
                        _ => { }
                    }
                }
            }
        }}
    } => Err(err) => assert_vir_error_msg(err, "expected `=>`")
}

// Independence pair for state_machines_macros/src/parse_token_stream.rs:220 atom 0 `name == "accept_recursive_types"`, atom 1 `name == "reject_recursive_types"`, atom 2 `name == "reject_recursive_types_i...`
test_verify_one_file! {
    #[test] sm_polarity verus_code! {
        use vstd::prelude::*;
        use verus_state_machines_macros::*;

        state_machine!{ #[verifier::accept_recursive_types(T)] #[verifier::reject_recursive_types(T)] #[verifier::reject_recursive_types_in_ground_variants(T)] #[verifier::external_body(T)] X<T> {
            fields { pub t: Option<T>, pub x: int }

            init!{ initialize() { init x = 0; } }
        }}
    } => Err(err) => assert_vir_error_msg(err, "the only attributes allowed here are verus_keep_ghost, verifier::accept_recursive_types,")
}
