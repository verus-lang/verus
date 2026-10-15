// Tests for vIR to SST to AIR encoding, polymorphism and simplification.
// Each test exercises verifier code (a check, an error path or an encoding case) that no other test
// of the suite exercises; its comment names the source lines it covers.
#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

// Covers ast_to_sst.rs:2733; sst_to_air.rs:2897
test_verify_one_file! {
    #[test] expr_029_loop_ensures_no_isolation verus_code! {
        use vstd::prelude::*;

        #[verifier::loop_isolation(false)]
        #[verifier::allow_complex_invariants]
        fn t() {
            let mut i = 0u8;
            loop
                invariant_except_break i <= 10,
                invariant i <= 10,
                ensures i == 10,
                decreases 10 - i,
            {
                if i == 10 { break; }
                i = i + 1;
            }
            assert(i == 10);
        }
    } => Ok(())
}

// Covers ast_to_sst.rs:2039
test_verify_one_file! {
    #[test] final_all_t4_t4_all_82 code! {
        use vstd::prelude::*;
        verus! {
        fn f(r: &mut Option<u8>, c: bool) {
            match r { y @ Some(_) if c => { } _ => { } }
        }
        } // verus!
        fn main() { let mut o = Some(1u8); f(&mut o, true); f(&mut o, false); println!("{:?}", o); }
    } => Ok(())
}

// Covers rust_to_vir_expr.rs:3740; sst_to_air.rs:2492, 2777
test_verify_one_file! {
    #[test] final_poly1129_a3_exec_temp_mix verus_code! {
        use vstd::prelude::*;

        fn inc(x: u64) -> (r: u64) requires x < 100 ensures r == x + 1 { x + 1 }
        fn dbl(x: u64) -> (r: u64) requires x < 100 ensures r == 2 * x { 2 * x }
        spec fn sp(n: int) -> int recommends n > 0 { n }
        fn mix(a: u64, b: bool) -> (r: u64)
            requires a < 10
            ensures r < 200
        {
            let t = if b { inc(a) } else { dbl(a) };
            let u = if a > 3 { inc(a) } else { return 0; };
            let arr = [inc(a), dbl(a), if b { inc(1) } else { 2 }];
            let mut i: u64 = 0;
            let v = #[verifier::loop_isolation(false)] loop
                invariant i <= 5
                decreases 5 - i
            {
                if i >= 5 { break if b { inc(i) } else { dbl(i) }; }
                i = i + 1;
            };
            let c = |z: u64| -> (w: u64) requires z < 50 ensures w == z + 1 { if z > 1 { inc(z) } else { z + 1 } };
            let w = c(a);
            assert(sp(3) == 3) by (compute_only);
            let r = if t > 0 { inc(t) } else { dbl(u) };
            assert(r == 0); // FAILS
            r
        }
    } => Err(err) => assert_one_fails(err)
}

// Covers sst_to_air.rs:2438, 2441, 2523, 2549, 2857
test_verify_one_file! {
    #[test] macros_encoding_air_for_continue code! {
        use vstd::prelude::*;
        verus! {
        fn sum_odd(n: u32) -> (s: u32)
            requires n <= 100,
            ensures s <= n,
        {
            let mut s: u32 = 0;
            for i in 0..n
                invariant s <= i, i <= n,
            {
                if i % 2 == 0 {
                    continue;
                }
                s = s + 1;
            }
            s
        }
        }
        fn main() {
            let r = sum_odd(10);
            println!("{}", r);
        }
    } => Err(err) => assert_vir_error_msg(err, "for-loops do not yet support continue")
}

// Covers ast_to_sst.rs:2705
test_verify_one_file_with_options! {
    #[test] macros_encoding_attr_for_loop_erase ["--compile"] => code! {
        use vstd::prelude::*;

        #[verus_spec(r =>
            requires n <= 100,
            ensures r == n,
        )]
        fn count(n: u32) -> u32 {
            let mut c: u32 = 0;
            #[verus_spec(
                invariant c == i, i <= n,
            )]
            for i in 0..n {
                c += 1;
            }
            c
        }

        fn main() {
            let r = count(7);
            assert!(r == 7);
            println!("{}", r);
        }
    } => Ok(())
}

// Covers poly.rs:427, 1281, 1341
test_verify_one_file! {
    #[test] macros_encoding_poly_unit_trait_call verus_code! {
        use vstd::prelude::*;

        pub trait Tr {
            fn m(&self);
            proof fn p(&self);
            spec fn s(&self) -> ();
            fn r(&self) -> (out: u8) ensures out == 3;
        }
        struct A;
        impl Tr for A {
            fn m(&self) {}
            proof fn p(&self) {}
            open spec fn s(&self) -> () { () }
            fn r(&self) -> (out: u8) { 3 }
        }
        fn caller<X: Tr>(x: &X) {
            let u = x.m();
            let v: () = x.m();
            let w = x.r();
            assert(w == 3);
            proof {
                let q = x.p();
                let z = x.s();
                assert(z == ());
            }
        }
        fn main() { caller(&A); }
    } => Ok(())
}

// Covers sst_to_air.rs:2154
test_verify_one_file! {
    #[test] spec_checked_const_ensures0 verus_code! {
        use vstd::prelude::*;

        pub open spec fn f(x: int) -> int recommends x > 0 { x }
        pub spec(checked) const C: int = f(0);
        /* FAILS */ proof fn p() ensures !(C == 0) {}
    } => Err(err) => assert_one_fails(err)
}

// Covers ast_to_sst.rs:4543
test_verify_one_file! {
    #[test] propose_2_4040_index_place_overflow verus_code! {
        use vstd::prelude::*;

        fn f(a: &mut [u8; 256], i: u8)
        {
            a[(i + 1) as usize] = 0; // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

// Covers sst_to_air.rs:2401
test_verify_one_file! {
    #[test] r2_encoding_poly_mutparam_trait_ctl verus_code! {
        use vstd::prelude::*;

        pub struct S { pub a: u8, pub b: u8 }
        pub trait Tr {
            fn f(&self, s: S, x: u8) -> (r: u8) requires s.b == 9;
            fn h(&self, p: (u8, bool)) -> (r: (u8, bool));
        }
        pub struct T { pub v: u8 }
        impl Tr for T {
            fn f(&self, mut s: S, mut x: u8) -> (r: u8) {
                x = 4;
                s.a = 1;
                assert(s.b == 1); // FAILS: s.b == 9
                x
            }
            fn h(&self, mut p: (u8, bool)) -> (r: (u8, bool)) {
                p.0 = 3;
                assert(p.0 == 4); // FAILS
                p
            }
        }
    } => Err(err) => assert_fails(err, 2)
}

// Covers ast_to_sst.rs:1214
test_verify_one_file! {
    #[test] r2_encoding_poly_trait_closure_return code! {
        use vstd::prelude::*;
        verus! {
        pub trait Tr { fn m(&self, x: u8) -> (r: u8) ensures r == if x < 10 { (x + 1) as u8 } else { 0u8 }; }
        pub struct T;
        impl Tr for T {
            fn m(&self, x: u8) -> (r: u8) {
                let c = |y: u8| -> (z: u8)
                    ensures z == if y < 10 { (y + 1) as u8 } else { 0u8 }
                {
                    if y < 10 { return y + 1; }
                    0
                };
                if x < 10 { return c(x); }
                c(x)
            }
        }
        }
        #[verifier::external]
        fn main() {
            for x in [0u8, 9, 10, 255] {
                let r = T.m(x);
                assert!(r == if x < 10 { x + 1 } else { 0 }, "m({x}) = {r}");
            }
            println!("runtime ok");
        }
    } => Ok(())
}

// Covers ast_to_sst.rs:4814; sst_to_air.rs:2514
test_verify_one_file! {
    #[test] r2_encoding_poly_trait_closure_return_conflict verus_code! {
        use vstd::prelude::*;

        pub trait Tr { fn m(&self, x: u8) -> (r: u8); }
        pub struct T;
        impl Tr for T {
            fn m(&self, x: u8) -> (r: u8) {
                let c = |y: u8| -> (z: u8)
                    ensures z == if y < 10 { (y + 2) as u8 } else { 0u8 } // FAILS
                {
                    if y < 10 { return y + 1; }
                    0
                };
                c(x)
            }
        }
    } => Err(err) => assert_one_fails(err)
}

// Covers sst_to_air.rs:1947
test_verify_one_file! {
    #[test] r2_interp_call_requires_fndef_adv code! {
        use vstd::prelude::*;
        verus! {
        uninterp spec fn flag() -> bool;
        fn zero() requires flag() {}
        fn one(x: u8) requires x > 3 {}

        proof fn ok_cr_zero() ensures call_requires(zero, ()) <==> flag() {} // FAILS
        proof fn ok_cr_one(x: u8) ensures call_requires(one, (x,)) <==> x > 3 {} // FAILS
        proof fn bad_cr_zero() { assert(call_requires(zero, ())); } // FAILS
        proof fn bad_cr_one() { assert(call_requires(one, (3u8,))); } // FAILS

        fn bad_direct_zero() { let f = zero; zero(); } // FAILS
        fn bad_direct_one(x: u8) requires call_requires(one, (x,)) || x == 0 { let f = one; one(x); } // FAILS
        fn ok_direct_one(x: u8) requires call_requires(one, (x,)) { let f = one; one(x); }
        fn ok_direct_zero() requires call_requires(zero, ()) { let f = zero; zero(); }
        fn ok_one_via_value(x: u8) {
            let f = one;
            if x > 3 { f(x); } else { assert(!call_requires(f, (x,))); } // FAILS
        }
        }

        #[verifier::external]
        fn main() {
            for x in [0u8, 3, 4, 255] { ok_one_via_value(x); if x > 3 { ok_direct_one(x); } }
            println!("call_requires_fndef_adv: runtime ok");
        }
    } => Err(err) => assert_fails(err, 7)
}

// Covers sst_to_air_func.rs:209
test_verify_one_file! {
    #[test] s_broadcast_rs verus_code! {
        use vstd::prelude::*;

        #[verifier::opaque]
        spec fn f(x: int) -> int { x * x + 1 }
        broadcast proof fn lem_f(x: int) ensures #[trigger] f(x) > 0 { reveal(f); assert(x * x >= 0) by (nonlinear_arith); }
        proof fn p(y: int) { broadcast use lem_f; assert(f(y) > 0); }
        pub broadcast group grp { lem_f }
        proof fn q(y: int) { broadcast use grp; assert(f(y + 1) > 0); }
    } => Ok(())
}

// Covers sst_to_air.rs:2577, 2580, 2581, 2589
test_verify_one_file! {
    #[test] s_fuel3_rs verus_code! {
        use vstd::prelude::*;

        spec fn sum(n: nat) -> nat decreases n { if n == 0 { 0 } else { n + sum((n - 1) as nat) } }
        proof fn p1() { reveal_with_fuel(sum, 2); assert(sum(1) == 1); }
        proof fn p2() { reveal_with_fuel(sum, 3); assert(sum(2) == 3); }
    } => Ok(())
}

// Covers sst_to_air.rs:2673, 2837, 2952, 2956
test_verify_one_file! {
    #[test] s_loop_exit2_rs verus_code! {
        use vstd::prelude::*;

        fn lt(a: u32, b: u32) -> (r: bool) ensures r == (a < b) { a < b }
        fn f() -> (r: u32) ensures r == 10 {
            let mut i: u32 = 0;
            while lt(i, 10)
                invariant i <= 10,
                decreases 10 - i,
            {
                i = i + 1;
            }
            i
        }
    } => Ok(())
}

// Covers ast_to_sst.rs:1358; ast_to_sst_func.rs:766, 770, 771; modes.rs:3778; poly.rs:861, 972, 979, 982; sst_to_air.rs:2529
test_verify_one_file! {
    #[test] s_typ_inv_rs verus_code! {
        use vstd::prelude::*;

        struct S { a: u8, b: i16 }
        fn id8(x: u8) -> (r: u8) ensures r == x { x }
        fn f(x: u8, y: u16, z: i8, s: S, v: Vec<u8>) {
            assert(x < 256);
            assert(y <= 65535);
            assert(-128 <= z);
            assert(s.a <= 255);
            assert(s.b >= -32768);
            let w = id8(x);
            assert(w <= 255);
            if v.len() > 0 { assert(v[0] <= 255); }
            let mut t = S { a: 1, b: 2 };
            t.a = x;
            assert(t.a <= 255);
        }
        proof fn g(n: nat) { assert(n >= 0); }
    } => Ok(())
}

// Covers sst_to_air.rs:2464
test_verify_one_file! {
    #[test] w_loop_break_inv_rs verus_code! {
        use vstd::prelude::*;

        fn f() {
            let mut i: u32 = 0;
            loop
                invariant_except_break i <= 3,
                ensures i == 7,
                decreases 3 - i,
            {
                if i == 3 { break; } // FAILS
                i = i + 1;
            }
        }
    } => Err(err) => assert_one_fails(err)
}

// Covers sst_to_air.rs:2881, 2887, 2892
test_verify_one_file! {
    #[test] w_loop_dec_rs verus_code! {
        use vstd::prelude::*;

        fn f() {
            let mut i: u32 = 0;
            while i < 10 // FAILS
                invariant i <= 10,
                decreases i,
            {
                i = i + 1;
            }
        }
    } => Err(err) => assert_one_fails(err)
}

// Covers sst_to_air.rs:2879, 2927, 2934
test_verify_one_file! {
    #[test] w_loop_front_inv_rs verus_code! {
        use vstd::prelude::*;

        fn f() {
            let mut i: u32 = 5;
            while i < 10
                invariant i == 0 || i >= 1, i <= 10, i == 0, // FAILS
                decreases 10 - i,
            {
                i = i + 1;
            }
        }
    } => Err(err) => assert_fails(err, 2)
}

// Covers modes.rs:1084; sst_to_air.rs:2794, 2943, 2944
test_verify_one_file! {
    #[test] w_loop_mutparam_rs verus_code! {
        use vstd::prelude::*;

        fn f(x: &mut u32) requires *old(x) == 0 {
            while *x < 10
                invariant *x <= 10,
                decreases 10 - *x,
            {
                *x = *x + 1;
            }
            assert(*x == *old(x)); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

// Covers sst_to_air.rs:2270
test_verify_one_file! {
    #[test] w_nonlinear_rs verus_code! {
        use vstd::prelude::*;

        proof fn p(x: int, y: int) requires x == 2, x * y == 6 {
            assert(y == 4) by (nonlinear_arith) requires x == 2, x * y == 6; // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}
