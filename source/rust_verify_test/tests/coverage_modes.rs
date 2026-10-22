// Branch-condition (MC/DC) coverage tests: mode checking (vir/src/modes.rs).
// Each test's comment names the decisions (file:line) and the conditions (atoms, numbered from 0
// in source order) for which the test supplies an evaluation that no other test supplies, so that
// the condition is shown to independently change the decision's outcome. See
// COVERAGE-UNREACHABLE.md for the conditions that no test can cover.
#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

// Independence pair for vir/src/modes.rs:1956 atom 0 `ctxt.check_ghost_blocks`, atom 1 `typing.block_ghostness == Ghost::...`
test_verify_one_file! {
    #[test] gw_1956 verus_code! {
        use vstd::prelude::*;

        fn f1<F: Fn(u8) -> u8>(g: F) -> bool {
            #[verifier::ghost_block_wrapped] { ::verus_builtin::call_requires(g, (1u8,)) }
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot call spec function from exec mode")
}

// Independence pair for vir/src/modes.rs:2305 atom 1 `typing.block_ghostness == Ghost::...`
test_verify_one_file! {
    #[test] gw_2295 code! {
        use vstd::prelude::*;
        macro_rules! sc { () => { ::verus_builtin::closure_to_fn_spec(|x: u8| x) } }
        verus! {
        fn f2() -> u8 {
            #[verifier::ghost_block_wrapped] { sc!() };
            0
        }
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot use spec_fn closure in 'exec' mode")
}

// Independence pair for vir/src/modes.rs:2350 atom 1 `typing.block_ghostness == Ghost::...`
test_verify_one_file! {
    #[test] gw_2340 code! {
        use vstd::prelude::*;
        macro_rules! pc { () => { ::verus_builtin::closure_to_fn_proof(|x: u8| x) } }
        verus! {
        fn f2() -> u8 {
            #[verifier::ghost_block_wrapped] { let c: proof_fn(u8) -> u8 = pc!(); };
            0
        }
        }
    } => Err(err) => assert_vir_error_msg(err, "proof closure can only appear in proof mode")
}

// Independence pair for vir/src/modes.rs:3330 atom 0 `borrow_mut_tracked`, atom 1 `typing.block_ghostness != Ghost::...`
test_verify_one_file! {
    #[test] gw_3320 verus_code! {
        use vstd::prelude::*;

        fn f4(x: &mut u8) {
            let r = #[verifier::ghost_block_wrapped] { ::verus_builtin::mut_ref_tracked(x) };
        }
    } => Err(err) => assert_vir_error_msg(err, "mut_ref_tracked not allowed in exec context")
}

// Independence pair for vir/src/modes.rs:3393 atom 1 `typing.block_ghostness == Ghost::...`
test_verify_one_file! {
    #[test] gw_3383 verus_code! {
        use vstd::prelude::*;

        fn f3(x: u8) -> bool {
            #[verifier::ghost_block_wrapped] { ::verus_builtin::has_resolved(x) }
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot use `has_resolved` in exec mode")
}

// Independence pair for vir/src/modes.rs:1434 atom 0 `ctxt.check_ghost_blocks`
test_verify_one_file! {
    #[test] legacy_spec_decl code! {
        use vstd::prelude::*;
        #[verifier::verify]
        fn f(a: &[u8; 4], b: bool) -> u8 {
            #[verifier::spec] let x: u8 = 5;
            #[verifier::spec] let y: u8;
            assert_(x == 5);
            let i: usize = 1;
            let r = if b { a[i] } else { 0 };
            match b { true => r, false => 0 }
        }
    } => Ok(())
}

// Independence pair for vir/src/modes.rs:1434 atom 1 `matches!(typing.block_ghostness, ...`
test_verify_one_file! {
    #[test] modes1434_inv_index_oob verus_code! {
        use vstd::prelude::*;
        use vstd::invariant::*;

        pub struct P;
        impl InvariantPredicate<int, u8> for P {
            open spec fn inv(k: int, v: u8) -> bool { true }
        }
        macro_rules! idx { ($a:expr, $i:expr) => { $a[$i] } } // FAILS
        fn f(Tracked(invs): Tracked<&[AtomicInvariant<int, u8, P>; 2]>, i: usize) {
            open_atomic_invariant!(&idx!(invs, i) => x => { });
        }
    } => Err(err) => assert_one_fails(err)
}
// Independence pair for vir/src/modes.rs:2177 atom 0 `matches!(&*crate::ast_util::undecor...`, atom 1 `mode != Mode::Exec`
test_verify_one_file! {
    #[test] to_dyn_mut_ref_modes verus_code! {
        use vstd::prelude::*;
        trait T {}
        struct S;
        impl T for S {}
        proof fn f(tracked x: &mut S) {
            let tracked y: &mut dyn T = x;
        }
        fn g(x: &mut S) {
            let y: &mut dyn T = x;
        }
        fn h(x: &S) {
            let y: &dyn T = x;
        }
    } => Err(err) => assert_vir_error_msg(err, "coercing mutable references to a trait object is not supported in spec/proof mode")
}

// Independence pair for vir/src/modes.rs:3306 atom 1 `outer_mode == Mode::Spec`
test_verify_one_file! {
    #[test] dual_const_ghost_wrapped_reborrow code! {
        use vstd::prelude::*;
        verus! {
        fn g(x: &mut u8) {}
        fn h0(y: u8) -> u8 { y }
        const fn gc(x: &mut [u8; 0]) {}
        const fn hc(y: u8) -> u8 { y }
        const fn mk0() -> &'static mut [u8; 0] { &mut [] }
        pub uninterp spec fn spec_mk() -> &'static mut [u8; 0];
        #[verifier::when_used_as_spec(spec_mk)]
        pub const fn mk() -> &'static mut [u8; 0] { &mut [] }

        const C: &'static mut [u8; 0] = {
            #[verifier::ghost_block_wrapped] { mk() }
        };
        } // verus!
        fn main() { println!("{}", C.len()); }
    } => Err(err) => assert_vir_error_msg(err, "expression has mode spec, expected mode exec")
}
