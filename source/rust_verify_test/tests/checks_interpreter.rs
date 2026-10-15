// Tests for the assert-by-compute interpreter (vir/src/interpreter.rs).
// Each test exercises verifier code (a check, an error path or an encoding case) that no other test
// of the suite exercises; its comment names the source lines it covers.
#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

// Covers interpreter.rs:535, 1070; sst_to_air.rs:1575
test_verify_one_file! {
    #[test] macros_encoding_interp_eq_neg verus_code! {
        use vstd::prelude::*;

        pub struct S { pub a: int, pub b: int }
        spec fn u(x: int) -> int;
        spec fn g(x: int, y: int) -> bool;
        spec fn ub(b: bool) -> bool;

        proof fn n_xor() { assert(ub((true ^ true) == true) == ub(true)) by (compute); } // FAILS
        proof fn n_one_plus(x: int) { assert(ub(1 + x != x + 1) == ub(true)) by (compute); } // FAILS
        proof fn n_ctor_second_field() { assert(ub(S { a: 1, b: 2 } == S { a: 1, b: 3 }) == ub(true)) by (compute); } // FAILS
        proof fn n_ctor_first_field() { assert(ub(S { a: 1, b: 2 } == S { a: 2, b: 2 }) == ub(true)) by (compute); } // FAILS
        proof fn n_variant(x: int) { assert(ub(Some(x) == None::<int>) == ub(true)) by (compute); } // FAILS
        proof fn n_lambda_call_fn(f: spec_fn(int) -> int, h: spec_fn(int) -> int) { assert(ub(f(1) == h(1)) == ub(true)) by (compute); } // FAILS
        proof fn n_lambda_call_arg(f: spec_fn(int) -> int) { assert(ub(f(1) == f(2)) == ub(true)) by (compute); } // FAILS
        proof fn n_field(s: S) { assert(ub(s.a == s.b) == ub(true)) by (compute); } // FAILS
        proof fn n_field2(s: S, t: S) { assert(ub(s.a == t.a) == ub(true)) by (compute); } // FAILS
        proof fn n_subrange_rev() { assert(ub(seq![1int, 2, 3].subrange(2, 1).len() == 0) == ub(true)) by (compute); } // FAILS
        proof fn n_subrange_rev2() { assert(ub(seq![1int, 2, 3].subrange(2, 1).len() != 0) == ub(true)) by (compute); } // FAILS
        proof fn n_subrange_long() { assert(ub(seq![1int, 2, 3].subrange(0, 5).len() == 5) == ub(true)) by (compute); } // FAILS
        proof fn n_subrange_long2() { assert(ub(seq![1int, 2, 3].subrange(0, 5).len() != 5) == ub(true)) by (compute); } // FAILS
        proof fn n_choose_typ() { assert(ub((choose|x: u8| u(x as int) == 5) as int != (choose|x: u16| u(x as int) == 5) as int) == ub(true)) by (compute); } // FAILS
        proof fn n_choose_cond() { assert(ub((choose|x: int| u(x) > 0) == (choose|x: int| u(x) > 1)) == ub(true)) by (compute); } // FAILS
        proof fn n_choose_cond2() { assert(ub((choose|x: int| u(x) > 0) != (choose|x: int| u(x) > 1)) == ub(true)) by (compute); } // FAILS
        proof fn n_forall_arity() { assert(ub((forall|x: int| g(x, 1)) == (forall|x: int, y: int| g(x, y))) == ub(true)) by (compute); } // FAILS
        proof fn n_forall_typ() { assert(ub((forall|x: int| g(x, 1)) == (forall|x: nat| g(x as int, 1))) == ub(true)) by (compute); } // FAILS
        proof fn n_forall_typ2() { assert(ub((forall|x: int| g(x, 1)) != (forall|x: nat| g(x as int, 1))) == ub(true)) by (compute); } // FAILS
        proof fn n_forall_capture(y: int) { assert(ub((forall|x: int| g(x, y)) == (forall|y: int| g(y, y))) == ub(true)) by (compute); } // FAILS
        /* FAILS */ proof fn n_forall_capture2(y: int) { assert(ub((forall|x: int| g(x, y)) != (forall|y: int| g(y, y))) == ub(true)) by (compute); }
    } => Err(err) => assert_fails(err, 21)
}

// Covers interpreter.rs:400, 450, 478, 486, 524
test_verify_one_file! {
    #[test] macros_encoding_interp_eq_true verus_code! {
        use vstd::prelude::*;

        pub struct S { pub a: int, pub b: int }
        spec fn u(x: int) -> int;
        spec fn g(x: int, y: int) -> bool;

        proof fn t_xor() { assert((true ^ true) == false) by (compute_only); }
        proof fn t_one_plus(x: int) { assert(1 + x == x + 1) by (compute); }
        proof fn t_uninterp() { assert(u(1) == u(1)) by (compute_only); }
        proof fn t_ctor_second_field() { assert(S { a: 1, b: 2 } != S { a: 1, b: 3 }) by (compute_only); }
        proof fn t_ctor_first_field() { assert(S { a: 1, b: 2 } != S { a: 2, b: 2 }) by (compute_only); }
        proof fn t_ctor_sym(x: int) { assert(S { a: x, b: 1 } != S { a: x, b: 2 }) by (compute_only); }
        proof fn t_variant(x: int) { assert(Some(x) != None::<int>) by (compute_only); }
        proof fn t_choose() { assert((choose|x: int| u(x) > 0) == (choose|x: int| u(x) > 0)) by (compute_only); }
        proof fn t_lambda_call(f: spec_fn(int) -> int) { assert(f(1) == f(1)) by (compute_only); }
        proof fn t_field(s: S) { assert(s.a == s.a) by (compute_only); }
        proof fn t_lambda_eq() { assert((|x: int| x + 1) == (|x: int| x + 1)) by (compute_only); }
        proof fn t_forall_alpha() { assert((forall|x: int| g(x, 1)) == (forall|z: int| g(z, 1))) by (compute_only); }
        proof fn t_seq_len_differs() { assert(seq![1int, 2] != seq![1int, 2, 3]) by (compute_only); }
    } => Ok(_) => ()
}

// Covers interpreter.rs:452, 504
test_verify_one_file! {
    #[test] macros_encoding_interp_misc_sym verus_code! {
        use vstd::prelude::*;

        spec fn ub(b: bool) -> bool;
        uninterp spec fn ui(x: int) -> int;
        #[verifier::opaque]
        spec fn op(x: int) -> int { x + 1 }
        spec fn fo(x: int) -> Option<int>;
        pub mod m { use vstd::prelude::*; verus! { pub closed spec fn cf(x: int) -> int { x + 1 } } }

        proof fn t_uninterp() { assert(ui(1) == ui(1)) by (compute_only); }
        proof fn t_opaque() { assert(op(1) == op(1)) by (compute_only); }
        proof fn n_closed_other_module() { assert(ub(m::cf(1) == 2) == ub(true)) by (compute); } // FAILS
        proof fn t_closed_call() { assert(m::cf(1) == m::cf(1)) by (compute_only); }
        proof fn t_opaque_seen_through() { assert(ub(op(1) == 2) == ub(true)) by (compute); }
        proof fn t_isvariant(o: Option<int>) { assert((fo(1) is Some) == (fo(1) is Some)) by (compute_only); }
        proof fn n_isvariant_arg() { assert(ub((fo(1) is Some) == (fo(2) is Some)) == ub(true)) by (compute); } // FAILS
        proof fn n_isvariant_var(o: Option<int>) { assert(ub((o is Some) == (o is None)) == ub(true)) by (compute); } // FAILS
        proof fn n_isvariant_dt(o: Option<int>, r: Result<int, int>) { assert(ub((o is Some) == (r is Ok)) == ub(true)) by (compute); } // FAILS
        fn t_old(x: &mut u8, y: &mut u8)
            requires *old(x) < 100,
        {
            proof {
                assert(ub(*old(x) == *old(x)) == ub(true)) by (compute);
                assert(ub(*old(x) == *old(y)) == ub(true)) by (compute); // FAILS
            }
        }
    } => Err(err) => assert_fails(err, 5)
}

// Covers interpreter.rs:1627
test_verify_one_file! {
    #[test] propose_1_10120 verus_code! {
        use vstd::prelude::*;

        proof fn p(x: int) {
            assert(2 * x == 0) by (compute); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

// Covers interpreter.rs:1448
test_verify_one_file! {
    #[test] r2_interp_interp_eval_both_ways verus_code! {
        use vstd::prelude::*;

        uninterp spec fn ub(b: bool) -> bool;
        proof fn p_0() { assert(((-7int) / 2) == -4) by (compute); }
        proof fn n_0() { assert(ub(((-7int) / 2) == -3) == ub(true)) by (compute); } // FAILS
        proof fn p_1() { assert(((-7int) % 2) == 1) by (compute); }
        proof fn n_1() { assert(ub(((-7int) % 2) == 2) == ub(true)) by (compute); } // FAILS
        proof fn p_2() { assert((7int / -2) == -3) by (compute); }
        proof fn n_2() { assert(ub((7int / -2) == -2) == ub(true)) by (compute); } // FAILS
        proof fn p_3() { assert((7int % -2) == 1) by (compute); }
        proof fn n_3() { assert(ub((7int % -2) == 2) == ub(true)) by (compute); } // FAILS
        proof fn p_4() { assert(((-7int) / -2) == 4) by (compute); }
        proof fn n_4() { assert(ub(((-7int) / -2) == 5) == ub(true)) by (compute); } // FAILS
        proof fn p_5() { assert(((-7int) % -2) == 1) by (compute); }
        proof fn n_5() { assert(ub(((-7int) % -2) == 2) == ub(true)) by (compute); } // FAILS
        proof fn p_6() { assert((300int as u8) == 44) by (compute); } // FAILS
        proof fn n_6() { assert(ub((300int as u8) == 45) == ub(true)) by (compute); } // FAILS
        proof fn p_7() { assert(((-1int) as u8) == 255) by (compute); } // FAILS
        proof fn n_7() { assert(ub(((-1int) as u8) == 256) == ub(true)) by (compute); } // FAILS
        proof fn p_8() { assert(((-129int) as i8) == 127) by (compute); } // FAILS
        proof fn n_8() { assert(ub(((-129int) as i8) == 128) == ub(true)) by (compute); } // FAILS
        proof fn p_9() { assert((128int as i8) == -128) by (compute); } // FAILS
        proof fn n_9() { assert(ub((128int as i8) == -127) == ub(true)) by (compute); } // FAILS
        proof fn p_10() { assert((0xF0u8 & 0x3Cu8) == 0x30u8) by (compute); }
        proof fn n_10() { assert(ub((0xF0u8 & 0x3Cu8) == 49u8) == ub(true)) by (compute); } // FAILS
        proof fn p_11() { assert((0xF0u8 | 0x0Fu8) == 0xFFu8) by (compute); }
        proof fn n_11() { assert(ub((0xF0u8 | 0x0Fu8) == 254u8) == ub(true)) by (compute); } // FAILS
        proof fn p_12() { assert((0xF0u8 ^ 0xFFu8) == 0x0Fu8) by (compute); }
        proof fn n_12() { assert(ub((0xF0u8 ^ 0xFFu8) == 16u8) == ub(true)) by (compute); } // FAILS
        proof fn p_13() { assert((!0u8) == 255u8) by (compute); }
        proof fn n_13() { assert(ub((!0u8) == 254u8) == ub(true)) by (compute); } // FAILS
        proof fn p_14() { assert((!0i8) == -1i8) by (compute); }
        proof fn n_14() { assert(ub((!0i8) == 0i8) == ub(true)) by (compute); } // FAILS
        proof fn p_15() { assert((!(-128i8)) == 127i8) by (compute); }
        proof fn n_15() { assert(ub((!(-128i8)) == 126i8) == ub(true)) by (compute); } // FAILS
        proof fn p_16() { assert((0x81u8 >> 1u8) == 0x40u8) by (compute); }
        proof fn n_16() { assert(ub((0x81u8 >> 1u8) == 65u8) == ub(true)) by (compute); } // FAILS
        proof fn p_17() { assert((0x81u8 << 1u8) == 0x02u8) by (compute); }
        proof fn n_17() { assert(ub((0x81u8 << 1u8) == 3u8) == ub(true)) by (compute); } // FAILS
        proof fn p_18() { assert(((-128i8) >> 1u8) == -64i8) by (compute); }
        proof fn n_18() { assert(ub(((-128i8) >> 1u8) == -63i8) == ub(true)) by (compute); } // FAILS
        proof fn p_19() { assert(((-1i8) >> 7u8) == -1i8) by (compute); }
        proof fn n_19() { assert(ub(((-1i8) >> 7u8) == 0i8) == ub(true)) by (compute); } // FAILS
        proof fn p_20() { assert((255u8 + 1u8) == 256int) by (compute); }
        proof fn n_20() { assert(ub((255u8 + 1u8) == 257int) == ub(true)) by (compute); } // FAILS
        proof fn p_21() { assert((0u8 - 1u8) == -1int) by (compute); }
        proof fn n_21() { assert(ub((0u8 - 1u8) == 0int) == ub(true)) by (compute); } // FAILS
        proof fn p_22() { assert(((-128i8) * (-1i8)) == 128int) by (compute); }
        proof fn n_22() { assert(ub(((-128i8) * (-1i8)) == 129int) == ub(true)) by (compute); } // FAILS
        proof fn p_23() { assert((true ^ true) == false) by (compute); }
        proof fn n_23() { assert(ub((true ^ true) == true) == ub(true)) by (compute); } // FAILS
        proof fn p_24() { assert((false ^ true) == true) by (compute); }
        proof fn n_24() { assert(ub((false ^ true) == false) == ub(true)) by (compute); } // FAILS
        proof fn p_25() { assert((Some(1int) is Some) == true) by (compute); }
        proof fn n_25() { assert(ub((Some(1int) is Some) == false) == ub(true)) by (compute); } // FAILS
        proof fn p_26() { assert((Option::<int>::None is Some) == false) by (compute); }
        proof fn n_26() { assert(ub((Option::<int>::None is Some) == true) == ub(true)) by (compute); } // FAILS
        proof fn p_27() { assert(((1int, 2int) == (1int, 3int)) == false) by (compute); }
        proof fn n_27() { assert(ub(((1int, 2int) == (1int, 3int)) == true) == ub(true)) by (compute); } // FAILS
        proof fn p_28() { assert((Some(1int) == Option::<int>::None) == false) by (compute); }
        /* FAILS */ proof fn n_28() { assert(ub((Some(1int) == Option::<int>::None) == true) == ub(true)) by (compute); }
    } => Err(err) => assert_fails(err, 33)
}
