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
    #[test] f32_ieee verus_code! {
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

test_verify_one_file! {
    #[test] f32_assume_ieee verus_code! {
        use vstd::std_specs::cmp::{PartialEqSpec, PartialOrdSpec, PartialOrdIs};

        fn test1(x: f32, y: f32) -> (z: f32)
            requires
                1.0f32.is_le(&x),
                x.is_le(&2.0),
                4.0f32.is_le(&y),
                y.is_le(&8.0),
            ensures
                5.0f32.is_le(&z),
                z.is_le(&10.0),
        {
            broadcast use vstd::contrib::assume_ieee_float::assume_ieee_float;

            let z = x + y;
            assert(5.0f32.ieee_le(x.ieee_add(y)) && x.ieee_add(y).ieee_le(10.0)) by(bit_vector)
                requires
                    1.0f32.ieee_le(x),
                    x.ieee_le(2.0),
                    4.0f32.ieee_le(y),
                    y.ieee_le(8.0);
            z
        }

        fn test2(x: f32, y: f32) -> (z: f32)
            requires
                1.0f32.is_le(&x),
                x.is_le(&2.0),
                4.0f32.is_le(&y),
                y.is_le(&8.0),
            ensures
                5.0f32.is_le(&z),
                z.is_lt(&10.0),
        {
            broadcast use vstd::contrib::assume_ieee_float::assume_ieee_float;

            let z = x + y;
            assert(5.0f32.ieee_le(x.ieee_add(y)) && x.ieee_add(y).ieee_lt(10.0)) by(bit_vector) // FAILS
                requires
                    1.0f32.ieee_le(x),
                    x.ieee_le(2.0),
                    4.0f32.ieee_le(y),
                    y.ieee_le(8.0);
            z
        }
    } => Err(err) => assert_one_fails(err)
}
