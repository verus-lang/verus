// Branch-condition (MC/DC) coverage tests: VIR well-formedness, termination, trait, type-invariant and pruning checks.
// Each test's comment names the decisions (file:line) and the conditions (atoms, numbered from 0
// in source order) for which the test supplies an evaluation that no other test supplies, so that
// the condition is shown to independently change the decision's outcome. See
// COVERAGE-UNREACHABLE.md for the conditions that no test can cover.
#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

// Independence pair for vir/src/headers.rs:423 atom 0 `fun == const_name`
test_verify_one_file! {
    #[test] headers_static_ensures_other_static verus_code! {
        use vstd::prelude::*;

        exec static A: u64 = 0;
        exec static B: u64 ensures B == 2, A == 0 { 2 }
    } => Err(err) => assert_vir_error_msg(err, "cannot read static with mode exec")
}

// Independence pair for vir/src/prune.rs:866 atom 0 `let Some(call_f) = function_map.g...`
test_verify_one_file! {
    #[test] prune_broadcast_trigger_external_call code! {
        use vstd::prelude::*;
        #[verifier::external]
        fn ext(x: u8) -> u8 { x }
        verus! {
        #[verifier::assume(externals_available_without_declaration)]
        broadcast proof fn lem(x: u8)
            ensures #[trigger] ext(x) == ext(x),
        {
        }
        broadcast use lem;
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot call external function from non-exec mode")
}

// Independence pair for vir/src/prune.rs:899 atom 0 `calls.len() == 0`, atom 1 `typs.len() == 0`
test_verify_one_file! {
    #[test] prune_broadcast_trigger_no_calls verus_code! {
        use vstd::prelude::*;

        broadcast proof fn p<T>(x: T)
            ensures #[trigger] x == x
        {
        }
        proof fn q() {
            broadcast use p;
        }
    } => Err(err) => assert_vir_error_msg(err, "trigger must be a function call, a field access, or arithmetic operator")
}

// Independence pair for vir/src/well_formed.rs:575 atom 0 `!scope_map.contains_key(&x)`, atom 1 `!referenced.contains(x)`
test_verify_one_file! {
    #[test] wf575_const_ensures_assertquery verus_code! {
        use vstd::prelude::*;

        exec const E: u64
            ensures ({ assert(true) by (nonlinear_arith) { assert(E == E); }; E == 3 })
        { 3 }
    } => Err(err) => assert_vir_error_msg(err, "variable %return not mentioned in requires/ensures")
}

// Independence pair for vir/src/well_formed.rs:575 atom 1 `!referenced.contains(x)`
test_verify_one_file! {
    #[test] wf575_pairs verus_code! {
        use vstd::prelude::*;

        proof fn a() {
            assert(true) by (nonlinear_arith) { let z = choose|i: int| i == 0; }
        }
        exec const E: u64
            ensures ({ assert(true) by (nonlinear_arith) requires E == E { assert(E == E); }; E == 3 })
        { 3 }
    } => Err(err) => assert_vir_error_msg(err, "expected pure mathematical expression")
}

// Independence pair for vir/src/well_formed.rs:1527 atom 3 `function.x.attrs.exec_assume_term...`
test_verify_one_file! {
    #[test] wf_exec_decreases_assume_termination verus_code! {
        use vstd::prelude::*;

        #[verifier::assume_termination]
        fn f(x: u8) decreases x { if x > 0 { f(x - 1) } }
    } => Ok(_) => ()
}

// Independence pair for vir/src/well_formed.rs:1112 atom 0 `param_name == outer_ret_name`
test_verify_one_file! {
    #[test] wf_param_named_as_ret_legacy code! {
        use vstd::prelude::*;
        #[verifier::verify]
        fn f(r: u8) -> u8 {
            ::verus_builtin::ensures(|r: u8| [r == 1u8]);
            r
        }
    } => Err(err) => assert_vir_error_msg(err, "parameter name cannot be the same as the return value name")
}

// Independence pair for vir/src/well_formed.rs:1057 atom 1 `matches!(*function.x.outer_ret.x....`
test_verify_one_file_with_options! {
    #[test] decreases_by_opaque_assoc_return ["no-auto-import-verus_builtin", "vstd"] => code! {
        #![feature(impl_trait_in_assoc_type)]
        use vstd::prelude::*;
        pub trait Tr { type O; fn mk() -> Self::O; }
        pub struct S;
        impl Tr for S { type O = impl Copy; fn mk() -> Self::O { 0u8 } }
        verus! {
        pub trait Marker {}
        impl Marker for u64 {}

        spec fn f(n: nat) -> u64
            decreases n
        {
            decreases_by(f_dec);
            0u64
        }

        #[verifier::decreases_by]
        proof fn f_dec(n: nat) -> <S as Tr>::O
        {
            arbitrary()
        }

        } // verus!
    } => Err(err) => assert_vir_error_msg(err, "Opaque type is not supported in proof mode")
}
