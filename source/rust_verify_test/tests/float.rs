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

test_verify_one_file_with_options! {
    #[test] pointer_sized_float_cast ["vstd", "--compile"] => verus_code! {
        use vstd::float::float_cast_spec;

        fn test_to_float(u: usize, i: isize) {
            let a: f32 = u as f32;
            let b: f64 = u as f64;
            let c: f32 = i as f32;
            let d: f64 = i as f64;
            assert(float_cast_spec(u, a) && float_cast_spec(u, b));
            assert(float_cast_spec(i, c) && float_cast_spec(i, d));
        }

        fn test_from_float(single: f32, double: f64) {
            let a: usize = single as usize;
            let b: usize = double as usize;
            let c: isize = single as isize;
            let d: isize = double as isize;
            assert(float_cast_spec(single, a) && float_cast_spec(double, b));
            assert(float_cast_spec(single, c) && float_cast_spec(double, d));
        }
    } => Ok(())
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
    } => Err(err) => assert_vir_error_msg(err, "Verus does not currently support `as` cast from `i32` to `f16`")
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
    } => Err(err) => assert_vir_error_msg(err, "Verus does not currently support `as` cast from `f16`")
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
    } => Err(err) => assert_vir_error_msg(err, "Verus does not currently support `as` cast from `f16` to `f64`")
}

test_verify_one_bv_file! {
    #[test] pointer_sized_float_ieee verus_code! {
        proof fn test_to_float(u: usize, i: isize) {
            assert(u == 16_777_217usize ==> u as f32 == 16_777_216f32) by(bit_vector);
            assert(u == 4_294_967_295usize ==> u as f64 == 4_294_967_295f64) by(bit_vector);
            assert(1isize as f64 == 1f64) by(bit_vector);
            assert(i == -1isize ==> i as f64 == -1f64) by(bit_vector);
        }

        proof fn test_from_float() {
            assert(3.75f32 as usize == 3usize) by(bit_vector);
            assert(4_294_967_295f64 as usize == 4_294_967_295usize) by(bit_vector);
            assert(-3.75f32 as isize == -3isize) by(bit_vector);
        }
    } => Ok(())
}

test_verify_one_bv_file! {
    #[test] pointer_sized_float_ieee_64 verus_code! {
        use vstd::prelude::*;
        global size_of usize == 8;

        proof fn test_to_float(u: usize, i: isize) {
            assert(u == 9_007_199_254_740_993usize ==> u as f64 == 9_007_199_254_740_992f64) by(bit_vector);
            assert(i == -9_007_199_254_740_993isize ==> i as f64 == -9_007_199_254_740_992f64) by(bit_vector);
        }

        proof fn test_from_float() {
            assert(4_294_967_296f64 as usize == 4_294_967_296usize) by(bit_vector);
            assert(-4_294_967_296f64 as isize == -4_294_967_296isize) by(bit_vector);
        }
    } => Ok(())
}

test_verify_one_bv_file! {
    #[test] float_to_usize_arch_split_fail verus_code! {
        proof fn test() {
            assert(4_294_967_296f64 as usize as u64 == 4_294_967_296u64) by(bit_vector); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] f32_ieee verus_code! {
        fn test1(x: f32, y: f32) {
            assert(2.0f32 <= x <= 5.0f32 ==> x + x <= 10.0f32) by(bit_vector);
            assert(2.0f32 <= x <= 5.0f32 && 2.0f32 <= y <= 5.0f32 ==> x + y == y + x) by(bit_vector);
            assert(0.5f32 as real == 0.5real) by(bit_vector);
            assert(0.5f32 == 0.5real as f32) by(bit_vector);
            assert(4f32 as u8 == 4u8) by(bit_vector);
            assert(4f32 == 4u8 as f32) by(bit_vector);
            assert(4f32 == 4f64 as f32) by(bit_vector);
            assert(4f32 as f64 == 4f64) by(bit_vector);
        }
        fn test2(x: f32, y: f32) {
            assert(2.0f32 <= x <= 7.0f32 ==> x + x <= 10.0f32) by(bit_vector); // FAILS
        }
        fn test3(x: f32, y: f32) {
            assert(2.0f32 <= x <= 5.0f32 && 2.0f32 <= y <= 5.0f32 ==> x + y == x + x) by(bit_vector); // FAILS
        }
        fn test4(x: f32, y: f32) {
            assert(0.5f32 as real == 0.6real) by(bit_vector); // FAILS
        }
        fn test5(x: f32, y: f32) {
            assert(0.5f32 == 0.6real as f32) by(bit_vector); // FAILS
        }
        fn test6(x: f32, y: f32) {
            assert(4f32 as u8 == 5u8) by(bit_vector); // FAILS
        }
        fn test7(x: f32, y: f32) {
            assert(4f32 == 5u8 as f32) by(bit_vector); // FAILS
        }
        fn test8(x: f32, y: f32) {
            assert(4f32 == 5f64 as f32) by(bit_vector); // FAILS
        }
        fn test9(x: f32, y: f32) {
            assert(4f32 as f64 == 5f64) by(bit_vector); // FAILS
        }
    } => Err(err) => assert_fails(err, 8)
}

test_verify_one_file! {
    #[test] float_cast_target_type_github3136 verus_code! {
        proof fn test1(f: f32) {
            assert(f == 200f32 ==> (f as u8) as i32 == 200i32) by(bit_vector);
            assert((f as i8) as i32 <= 127i32) by(bit_vector);
            assert((f as u8) as i32 == (f as u8) as i32) by(bit_vector);
        }
        proof fn test2(f: f32) {
            assert((f as u8) as i32 == (f as i8) as i32) by(bit_vector); // FAILS
        }
        proof fn test3(x: i32) {
            assert((x as f32) as i64 == (x as f64) as i64) by(bit_vector); // FAILS
        }
        proof fn test4(f: f32) {
            assert((f as u8) as i32 == (f as i8) as i32) by(compute); // FAILS
        }
    } => Err(err) => assert_fails(err, 3)
}

test_verify_one_file! {
    #[test] f32_neg verus_code! {
        fn test() {
            let x: f32 = 1.0;
            let y = -x;

            let x2 = &x;
            let y = -x2;
        }
    } => Err(err) => assert_vir_error_msg(err, "Verus does not currently support unary negation of floating point")
}

test_verify_one_file! {
    #[test] f32_ops verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::ops::*;
        use vstd::std_specs::cmp::*;

        fn test_add(a: f32, b: f32) {
            let x = a + b;
            let y = a + b;
            assert(add_ensures(a, b, x));
            assert(add_ensures(a, b, y));
        }

        fn test_add_determinism_fails(a: f32, b: f32) {
            let x = a + b;
            let y = a + b;
            assert(x == y); // FAILS
        }

        fn test_sub(a: f32, b: f32) {
            let x = a - b;
            let y = a - b;
            assert(sub_ensures(a, b, x));
            assert(sub_ensures(a, b, y));
        }

        fn test_sub_determinism_fails(a: f32, b: f32) {
            let x = a - b;
            let y = a - b;
            assert(x == y); // FAILS
        }

        fn test_mul(a: f32, b: f32) {
            let x = a * b;
            let y = a * b;
            assert(mul_ensures(a, b, x));
            assert(mul_ensures(a, b, y));
        }

        fn test_mul_determinism_fails(a: f32, b: f32) {
            let x = a * b;
            let y = a * b;
            assert(x == y); // FAILS
        }

        fn test_div(a: f32, b: f32) {
            let x = a / b;
            let y = a / b;
            assert(div_ensures(a, b, x));
            assert(div_ensures(a, b, y));
        }

        fn test_div_determinism_fails(a: f32, b: f32) {
            let x = a / b;
            let y = a / b;
            assert(x == y); // FAILS
        }

        fn test_eq(a: f32, b: f32) {
            let x = a == b;
            let y = a == b;
            assert(eq_ensures(a, b, x));
            assert(eq_ensures(a, b, y));
        }

        fn test_eq_determinism_fails(a: f32, b: f32) {
            let x = a == b;
            let y = a == b;
            assert(x == y); // FAILS
        }

        fn test_ne(a: f32, b: f32) {
            let x = a != b;
            let y = a != b;
            assert(ne_ensures(a, b, x));
            assert(ne_ensures(a, b, y));
        }

        fn test_ne_determinism_fails(a: f32, b: f32) {
            let x = a != b;
            let y = a != b;
            assert(x == y); // FAILS
        }

        fn test_le(a: f32, b: f32) {
            let x = a <= b;
            let y = a <= b;
            assert(le_ensures(a, b, x));
            assert(le_ensures(a, b, y));
        }

        fn test_le_determinism_fails(a: f32, b: f32) {
            let x = a <= b;
            let y = a <= b;
            assert(x == y); // FAILS
        }

        fn test_lt(a: f32, b: f32) {
            let x = a < b;
            let y = a < b;
            assert(lt_ensures(a, b, x));
            assert(lt_ensures(a, b, y));
        }

        fn test_lt_determinism_fails(a: f32, b: f32) {
            let x = a < b;
            let y = a < b;
            assert(x == y); // FAILS
        }

        fn test_ge(a: f32, b: f32) {
            let x = a >= b;
            let y = a >= b;
            assert(ge_ensures(a, b, x));
            assert(ge_ensures(a, b, y));
        }

        fn test_ge_determinism_fails(a: f32, b: f32) {
            let x = a >= b;
            let y = a >= b;
            assert(x == y); // FAILS
        }

        fn test_gt(a: f32, b: f32) {
            let x = a > b;
            let y = a > b;
            assert(gt_ensures(a, b, x));
            assert(gt_ensures(a, b, y));
        }

        fn test_gt_determinism_fails(a: f32, b: f32) {
            let x = a > b;
            let y = a > b;
            assert(x == y); // FAILS
        }
    } => Err(err) => assert_fails(err, 10)
}

test_verify_one_file! {
    #[test] f64_ops verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::ops::*;
        use vstd::std_specs::cmp::*;

        fn test_add(a: f64, b: f64) {
            let x = a + b;
            let y = a + b;
            assert(add_ensures(a, b, x));
            assert(add_ensures(a, b, y));
        }

        fn test_add_determinism_fails(a: f64, b: f64) {
            let x = a + b;
            let y = a + b;
            assert(x == y); // FAILS
        }

        fn test_sub(a: f64, b: f64) {
            let x = a - b;
            let y = a - b;
            assert(sub_ensures(a, b, x));
            assert(sub_ensures(a, b, y));
        }

        fn test_sub_determinism_fails(a: f64, b: f64) {
            let x = a - b;
            let y = a - b;
            assert(x == y); // FAILS
        }

        fn test_mul(a: f64, b: f64) {
            let x = a * b;
            let y = a * b;
            assert(mul_ensures(a, b, x));
            assert(mul_ensures(a, b, y));
        }

        fn test_mul_determinism_fails(a: f64, b: f64) {
            let x = a * b;
            let y = a * b;
            assert(x == y); // FAILS
        }

        fn test_div(a: f64, b: f64) {
            let x = a / b;
            let y = a / b;
            assert(div_ensures(a, b, x));
            assert(div_ensures(a, b, y));
        }

        fn test_div_determinism_fails(a: f64, b: f64) {
            let x = a / b;
            let y = a / b;
            assert(x == y); // FAILS
        }

        fn test_eq(a: f64, b: f64) {
            let x = a == b;
            let y = a == b;
            assert(eq_ensures(a, b, x));
            assert(eq_ensures(a, b, y));
        }

        fn test_eq_determinism_fails(a: f64, b: f64) {
            let x = a == b;
            let y = a == b;
            assert(x == y); // FAILS
        }

        fn test_ne(a: f64, b: f64) {
            let x = a != b;
            let y = a != b;
            assert(ne_ensures(a, b, x));
            assert(ne_ensures(a, b, y));
        }

        fn test_ne_determinism_fails(a: f64, b: f64) {
            let x = a != b;
            let y = a != b;
            assert(x == y); // FAILS
        }

        fn test_le(a: f64, b: f64) {
            let x = a <= b;
            let y = a <= b;
            assert(le_ensures(a, b, x));
            assert(le_ensures(a, b, y));
        }

        fn test_le_determinism_fails(a: f64, b: f64) {
            let x = a <= b;
            let y = a <= b;
            assert(x == y); // FAILS
        }

        fn test_lt(a: f64, b: f64) {
            let x = a < b;
            let y = a < b;
            assert(lt_ensures(a, b, x));
            assert(lt_ensures(a, b, y));
        }

        fn test_lt_determinism_fails(a: f64, b: f64) {
            let x = a < b;
            let y = a < b;
            assert(x == y); // FAILS
        }

        fn test_ge(a: f64, b: f64) {
            let x = a >= b;
            let y = a >= b;
            assert(ge_ensures(a, b, x));
            assert(ge_ensures(a, b, y));
        }

        fn test_ge_determinism_fails(a: f64, b: f64) {
            let x = a >= b;
            let y = a >= b;
            assert(x == y); // FAILS
        }

        fn test_gt(a: f64, b: f64) {
            let x = a > b;
            let y = a > b;
            assert(gt_ensures(a, b, x));
            assert(gt_ensures(a, b, y));
        }

        fn test_gt_determinism_fails(a: f64, b: f64) {
            let x = a > b;
            let y = a > b;
            assert(x == y); // FAILS
        }
    } => Err(err) => assert_fails(err, 10)
}

test_verify_one_file! {
    #[test] f32_assign_ops verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::ops::*;

        fn test_add(a: f32, b: f32) {
            let mut x = a; x += b;
            let mut y = a; y += b;
            assert(add_ensures(a, b, x));
            assert(add_ensures(a, b, y));
        }

        fn test_add_determinism_fails(a: f32, b: f32) {
            let mut x = a; x += b;
            let mut y = a; y += b;
            assert(x == y); // FAILS
        }

        fn test_sub(a: f32, b: f32) {
            let mut x = a; x -= b;
            let mut y = a; y -= b;
            assert(sub_ensures(a, b, x));
            assert(sub_ensures(a, b, y));
        }

        fn test_sub_determinism_fails(a: f32, b: f32) {
            let mut x = a; x -= b;
            let mut y = a; y -= b;
            assert(x == y); // FAILS
        }

        fn test_mul(a: f32, b: f32) {
            let mut x = a; x *= b;
            let mut y = a; y *= b;
            assert(mul_ensures(a, b, x));
            assert(mul_ensures(a, b, y));
        }

        fn test_mul_determinism_fails(a: f32, b: f32) {
            let mut x = a; x *= b;
            let mut y = a; y *= b;
            assert(x == y); // FAILS
        }

        fn test_div(a: f32, b: f32) {
            let mut x = a; x /= b;
            let mut y = a; y /= b;
            assert(div_ensures(a, b, x));
            assert(div_ensures(a, b, y));
        }

        fn test_div_determinism_fails(a: f32, b: f32) {
            let mut x = a; x /= b;
            let mut y = a; y /= b;
            assert(x == y); // FAILS
        }
    } => Err(err) => assert_fails(err, 4)
}

test_verify_one_file! {
    #[test] f32_assign_ops_ordering verus_code! {
        use vstd::prelude::*;
        use vstd::std_specs::ops::*;

        // check rhs before lhs

        fn test_add(a: f32, b: f32) {
            let mut a = a;
            let mut z = 0;
            *({ z = 1; &mut a }) += ({ z = z * 2; b });
            assert(z == 1);
        }

        fn test_sub(a: f32, b: f32) {
            let mut a = a;
            let mut z = 0;
            *({ z = 1; &mut a }) -= ({ z = z * 2; b });
            assert(z == 1);
        }

        fn test_mul(a: f32, b: f32) {
            let mut a = a;
            let mut z = 0;
            *({ z = 1; &mut a }) *= ({ z = z * 2; b });
            assert(z == 1);
        }

        fn test_div(a: f32, b: f32) {
            let mut a = a;
            let mut z = 0;
            *({ z = 1; &mut a }) /= ({ z = z * 2; b });
            assert(z == 1);
        }
    } => Ok(())
}

// Spec `==` on floats is equality of IEEE bit patterns, including NaN payloads and signed zero.
// `ieee_eq` stays SMT `fp.eq` (NaN compares unequal, and +0 equals -0).
test_verify_one_bv_file_with_options! {
    #[test] bitvector_float_eq_bit_patterns ["vstd"] => verus_code! {
        proof fn same_nan_f32() {
            assert(spec_literal_decimal::<f32>("NaN") == spec_literal_decimal::<f32>("NaN")) by(bit_vector);
        }

        proof fn same_nan_f32_var(x: f32)
            requires
                x == spec_literal_decimal::<f32>("NaN"),
        {
            assert(x == spec_literal_decimal::<f32>("NaN")) by(bit_vector)
                requires
                    x == spec_literal_decimal::<f32>("NaN"),
            ;
        }

        proof fn ieee_eq_zeros() {
            assert((0.0f32).ieee_eq(-0.0f32)) by(bit_vector);
            assert((0.0f64).ieee_eq(-0.0f64)) by(bit_vector);
        }
    } => Ok(())
}

test_verify_one_bv_file_with_options! {
    #[test] bitvector_float_eq_bit_patterns_fail ["vstd"] => verus_code! {
        proof fn distinct_nan_f32()
            ensures
                false,
        {
            assert(spec_literal_decimal::<f32>("NaN") == spec_literal_decimal::<f32>("-NaN")) by(bit_vector); // FAILS
        }

        proof fn distinct_nan_f32_vars(x: f32, y: f32)
            requires
                x == spec_literal_decimal::<f32>("NaN"),
                y == spec_literal_decimal::<f32>("-NaN"),
            ensures
                false,
        {
            assert(x == y) by(bit_vector) // FAILS
                requires
                    x == spec_literal_decimal::<f32>("NaN"),
                    y == spec_literal_decimal::<f32>("-NaN"),
            ;
        }

        proof fn distinct_nan_f64()
            ensures
                false,
        {
            assert(spec_literal_decimal::<f64>("NaN") == spec_literal_decimal::<f64>("-NaN")) by(bit_vector); // FAILS
        }

        proof fn distinct_nan_f64_vars(x: f64, y: f64)
            requires
                x == spec_literal_decimal::<f64>("NaN"),
                y == spec_literal_decimal::<f64>("-NaN"),
            ensures
                false,
        {
            assert(x == y) by(bit_vector) // FAILS
                requires
                    x == spec_literal_decimal::<f64>("NaN"),
                    y == spec_literal_decimal::<f64>("-NaN"),
            ;
        }

        proof fn neg_zero_f32() {
            assert(0.0f32 == -0.0f32) by(bit_vector); // FAILS
        }

        proof fn neg_zero_f64() {
            assert(0.0f64 == -0.0f64) by(bit_vector); // FAILS
        }

        proof fn ieee_eq_nans() {
            assert(spec_literal_decimal::<f32>("NaN").ieee_eq(spec_literal_decimal::<f32>("-NaN"))) by(bit_vector); // FAILS
            assert(spec_literal_decimal::<f64>("NaN").ieee_eq(spec_literal_decimal::<f64>("-NaN"))) by(bit_vector); // FAILS
        }
    } => Err(err) => assert_fails(err, 8)
}

// Floats are encoded as integer bit patterns, and the same bits mean different values in f32
// and f64, so spec IEEE operations on equal bit patterns of different widths must stay unrelated.
test_verify_one_file! {
    #[test] ieee_ops_width_github3073 verus_code! {
        use vstd::prelude::*;
        use vstd::float::*;

        // a = b = 1.0f32 (bits 0x3F80_0000), so a + b = 2.0f32 (bits 0x4000_0000).
        // c = d have the same bits as f64, a subnormal, so c + d = 2c (bits 0x7F00_0000).
        proof fn conflate_add(a: f32, b: f32, c: f64, d: f64)
            requires
                a.to_bits_spec() as int == c.to_bits_spec() as int,
                b.to_bits_spec() as int == d.to_bits_spec() as int,
        {
            assert(a.ieee_add(b).to_bits_spec() as int == c.ieee_add(d).to_bits_spec() as int); // FAILS
        }

        // Bits 0x7FC0_0000 are NaN as f32 but a subnormal as f64.
        proof fn conflate_nan(a: f32, c: f64)
            requires
                a.to_bits_spec() as int == c.to_bits_spec() as int,
        {
            assert(a.ieee_is_nan() == c.ieee_is_nan()); // FAILS
        }

        proof fn conflate_neg(a: f32, c: f64)
            requires
                a.to_bits_spec() as int == c.to_bits_spec() as int,
        {
            assert((-a).to_bits_spec() as int == (-c).to_bits_spec() as int); // FAILS
        }

        proof fn conflate_lt(a: f32, b: f32, c: f64, d: f64)
            requires
                a.to_bits_spec() as int == c.to_bits_spec() as int,
                b.to_bits_spec() as int == d.to_bits_spec() as int,
        {
            assert((a < b) == (c < d)); // FAILS
        }
    } => Err(err) => assert_fails(err, 4)
}

// 1.0f32 and 5.263544247e-315f64 both have bits 0x3F80_0000: normal as f32, subnormal as f64.
test_verify_one_file! {
    #[test] ieee_ops_width_mixed_bv_github3073 verus_code! {
        proof fn normal_vs_subnormal(a: f32, c: f64)
            requires
                a == 1.0f32,
                c == 5.263544247e-315f64,
        {
            assert(a.ieee_is_normal()) by(bit_vector)
                requires
                    a == 1.0f32,
            ;
            assert(!c.ieee_is_normal()) by(bit_vector)
                requires
                    c == 5.263544247e-315f64,
            ;
            assert(false); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] ieee_unary_op_generic_operand verus_code! {
        #[verifier::allow(undeclared_external_trait)]
        proof fn generic_is_nan<T: IeeeFloat>(x: T) {
            let b = x.ieee_is_nan();
        }
    } => Err(err) => assert_vir_error_msg(err, "IEEE floating point operations require f32 or f64 operands (got `T`)")
}

test_verify_one_file! {
    #[test] ieee_binary_op_generic_operand verus_code! {
        #[verifier::allow(undeclared_external_trait)]
        proof fn generic_add<T: IeeeFloat>(x: T) {
            let y = x.ieee_add(x);
        }
    } => Err(err) => assert_vir_error_msg(err, "IEEE floating point operations require f32 or f64 operands (got `T`)")
}
