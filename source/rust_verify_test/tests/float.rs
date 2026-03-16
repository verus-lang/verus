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
            use vstd::float::float_cast_spec;
            let x: f64 = n as f64;
            // The ensures predicate should hold for the cast result
            assert(float_cast_spec(n, x));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] int_to_f32_cast verus_code! {
        fn test_u32_as_f32(n: u32) {
            use vstd::float::float_cast_spec;
            let x: f32 = n as f32;
            assert(float_cast_spec(n, x));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] f64_to_int_cast verus_code! {
        fn test_f64_as_u32(f: f64) {
            use vstd::float::float_cast_spec;
            let n: u32 = f as u32;
            assert(float_cast_spec(f, n));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] f32_to_int_cast verus_code! {
        fn test_f32_as_i64(f: f32) {
            use vstd::float::float_cast_spec;
            let n: i64 = f as i64;
            assert(float_cast_spec(f, n));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] float_to_float_cast verus_code! {
        fn test_f32_as_f64(f: f32) {
            use vstd::float::float_cast_spec;
            let d: f64 = f as f64;
            assert(float_cast_spec(f, d));
        }

        fn test_f64_as_f32(d: f64) {
            use vstd::float::float_cast_spec;
            let f: f32 = d as f32;
            assert(float_cast_spec(d, f));
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
    #[test] cast_usize_to_f64_unsupported verus_code! {
        fn test_usize_as_f64(n: usize) {
            let x: f64 = n as f64;
        }
    } => Err(err) => assert_vir_error_msg(err, "Verus does not support `as` cast from `usize` to `f64`")
}

test_verify_one_file! {
    #[test] cast_f64_to_isize_unsupported verus_code! {
        fn test_f64_as_isize(f: f64) {
            let n: isize = f as isize;
        }
    } => Err(err) => assert_vir_error_msg(err, "Verus does not support `as` cast from `f64` to `isize`")
}

test_verify_one_file_with_options! {
    #[test] cast_int_to_f16_unsupported ["no-auto-import-verus_builtin"] => code! {
        #![cfg_attr(verus_keep_ghost, feature(f16))]

        use verus_builtin::*;
        use verus_builtin_macros::*;

        verus! {
            fn test_i32_as_f16(n: i32) {
                let y: f16 = n as f16;
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "Verus does not support `as` cast to `f16`")
}

test_verify_one_file_with_options! {
    #[test] cast_f16_to_int_unsupported ["no-auto-import-verus_builtin"] => code! {
        #![cfg_attr(verus_keep_ghost, feature(f16))]

        use verus_builtin::*;
        use verus_builtin_macros::*;

        verus! {
            fn test_f16_as_i32(f: f16) {
                let n: i32 = f as i32;
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "Verus does not support `as` cast from `f16`")
}

test_verify_one_file_with_options! {
    #[test] cast_f16_to_f64_unsupported ["no-auto-import-verus_builtin"] => code! {
        #![cfg_attr(verus_keep_ghost, feature(f16))]

        use verus_builtin::*;
        use verus_builtin_macros::*;

        verus! {
            fn test_f16_as_f64(f: f16) {
                let d: f64 = f as f64;
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "Verus does not support `as` cast from `f16` to `f64`")
}

test_verify_one_file! {
    #[test] f32_ieee verus_code! {
        // TODO: replace explicit calls to ieee_cast with "as" when support for "as" is added
        // (and use this to replace === with ==)
        fn test1(x: f32, y: f32) {
            assert(2.0f32 <= x <= 5.0f32 ==> x + x <= 10.0f32) by(bit_vector);
            assert(2.0f32 <= x <= 5.0f32 && 2.0f32 <= y <= 5.0f32 ==> x + y == y + x) by(bit_vector);
            assert(0.5f32.ieee_cast() === 0.5real) by(bit_vector);
            assert(0.5f32 === 0.5real.ieee_cast()) by(bit_vector);
            assert(4f32.ieee_cast() === 4u8) by(bit_vector);
            assert(4f32 === 4u8.ieee_cast()) by(bit_vector);
            assert(4f32 === 4f64.ieee_cast()) by(bit_vector);
            assert(4f32.ieee_cast() === 4f64) by(bit_vector);
        }
        fn test2(x: f32, y: f32) {
            assert(2.0f32 <= x <= 7.0f32 ==> x + x <= 10.0f32) by(bit_vector); // FAILS
        }
        fn test3(x: f32, y: f32) {
            assert(2.0f32 <= x <= 5.0f32 && 2.0f32 <= y <= 5.0f32 ==> x + y == x + x) by(bit_vector); // FAILS
        }
        fn test4(x: f32, y: f32) {
            assert(0.5f32.ieee_cast() === 0.6real) by(bit_vector); // FAILS
        }
        fn test5(x: f32, y: f32) {
            assert(0.5f32 === 0.6real.ieee_cast()) by(bit_vector); // FAILS
        }
        fn test6(x: f32, y: f32) {
            assert(4f32.ieee_cast() === 5u8) by(bit_vector); // FAILS
        }
        fn test7(x: f32, y: f32) {
            assert(4f32 === 5u8.ieee_cast()) by(bit_vector); // FAILS
        }
        fn test8(x: f32, y: f32) {
            assert(4f32 === 5f64.ieee_cast()) by(bit_vector); // FAILS
        }
        fn test9(x: f32, y: f32) {
            assert(4f32.ieee_cast() === 5f64) by(bit_vector); // FAILS
        }
    } => Err(err) => assert_fails(err, 8)
}
