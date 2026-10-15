// Tests for pruning of unused items (vir/src/prune.rs).
// Each test exercises verifier code (a check, an error path or an encoding case) that no other test
// of the suite exercises; its comment names the source lines it covers.
#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

// Covers prune.rs:550
test_verify_one_file! {
    #[test] expr_049_isize_div verus_code! {
        use vstd::prelude::*;

        fn f(a: isize, b: isize) -> isize requires b != 0, !(a == isize::MIN && b == -1) { a / b }
    } => Ok(())
}

// Covers prune.rs:298, 299
test_verify_one_file! {
    #[test] final_msg524_a3_dyn_cycle verus_code! {
        use vstd::prelude::*;

        trait T { spec fn v(&self) -> int; }
        trait U: T {}
        struct D { b: Box<dyn U> }
        impl T for D { spec fn v(&self) -> int { self.b.v() } }
        impl U for D {}
    } => Ok(())
}

// Covers external.rs:342; prune.rs:961
test_verify_one_file! {
    #[test] s_broadcast2_rs verus_code! {
        use vstd::prelude::*;

        #[verifier::opaque]
        pub open spec fn f(x: int) -> int { x * x + 1 }
        pub broadcast proof fn lem_f(x: int) ensures #[trigger] f(x) > 0 { reveal(f); assert(x * x >= 0) by (nonlinear_arith); }
        pub broadcast group grp { lem_f }
        broadcast use grp;
        proof fn p(y: int) { assert(f(y) > 0); }
    } => Err(err) => assert_vir_error_msg(err, "found a cyclic self-reference in a definition, which may result in nontermination")
}
