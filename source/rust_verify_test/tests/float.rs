#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] f32_basics verus_code! {
        fn test1() {
            use vstd::std_specs::ops::{AddSpec, add_ensures};
            use vstd::std_specs::cmp::{PartialOrdSpec, PartialOrdIs, lt_ensures};
            use vstd::float::FloatBitsProperties;

            assume(forall|a: f32, b: f32| a.add_req(b));
            assume(forall|a: f32, b: f32, o: f32|
                !a.is_nan_spec() && !b.is_nan_spec() && add_ensures(a, b, o)
                ==> o == a.add_spec(b)
            );
            assume(forall|a: f32, b: f32, o: bool|
                !a.is_nan_spec() && !b.is_nan_spec() && lt_ensures(a, b, o)
                ==> o == a.is_lt(&b) && a.partial_cmp_spec(&b).is_some()
            );

            let p0: f32 = 3.14;
            let p1: f32 = 3.1400001;
            let p2: f32 = 3.1400002;
            let p3: f32 = 3.1400003;
            assert(p0 == p1);
            assert(p0 == p2);
            assert(p0 != p3);

            let p4: f32 = p0.clone();
            assert(p4 == p0);

            let n0: f32 = -3.14;

            let q = p0 + p3;
            let b = p0 < p3;

            assert(q == p0.add_spec(p3));
            assert(b == p0.is_lt(&p3));
            assert(b == !p0.is_ge(&p3));

            assert(f32_to_bits(0.0) == 0);
            assert(f32_to_bits(-0.0f32) == 0x80000000);
            assert(p0.is_finite_spec());

            assert(f32_to_bits(n0) == 0x80000000 + f32_to_bits(p0));
            assert(f32_to_bits(n0) == 0x80000001 + f32_to_bits(p0)); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] int_to_f64_cast verus_code! {
        fn test_i32_as_f64(n: i32) {
            use vstd::float::i32_as_f64_ensures;
            let x: f64 = n as f64;
            // The ensures predicate should hold for the cast result
            assert(i32_as_f64_ensures(n, x));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] int_to_f32_cast verus_code! {
        fn test_u32_as_f32(n: u32) {
            use vstd::float::u32_as_f32_ensures;
            let x: f32 = n as f32;
            assert(u32_as_f32_ensures(n, x));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] f64_to_int_cast verus_code! {
        fn test_f64_as_u32(f: f64) {
            use vstd::float::f64_as_u32_ensures;
            let n: u32 = f as u32;
            assert(f64_as_u32_ensures(f, n));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] f32_to_int_cast verus_code! {
        fn test_f32_as_i64(f: f32) {
            use vstd::float::f32_as_i64_ensures;
            let n: i64 = f as i64;
            assert(f32_as_i64_ensures(f, n));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] float_to_float_cast verus_code! {
        fn test_f32_as_f64(f: f32) {
            use vstd::float::f32_as_f64_ensures;
            let d: f64 = f as f64;
            assert(f32_as_f64_ensures(f, d));
        }

        fn test_f64_as_f32(d: f64) {
            use vstd::float::f64_as_f32_ensures;
            let f: f32 = d as f32;
            assert(f64_as_f32_ensures(d, f));
        }
    } => Ok(())
}

test_verify_one_file_with_options! {
    #[test] cast_nondeterministic_fail ["vstd"] => verus_code! {
        fn test_nondeterministic(n: i32) {
            let x: f64 = n as f64;
            let y: f64 = n as f64;
            assert(x == y); // FAILS: each cast is nondeterministic
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] cast_same_float_identity verus_code! {
        fn test_f64_identity(f: f64) {
            let g: f64 = f as f64;
            assert(f == g); // Same-type cast is identity
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] cast_usize_and_isize verus_code! {
        fn test_usize_as_f64(n: usize) {
            use vstd::float::usize_as_f64_ensures;
            let x: f64 = n as f64;
            assert(usize_as_f64_ensures(n, x));
        }

        fn test_f64_as_isize(f: f64) {
            use vstd::float::f64_as_isize_ensures;
            let n: isize = f as isize;
            assert(f64_as_isize_ensures(f, n));
        }
    } => Ok(())
}
