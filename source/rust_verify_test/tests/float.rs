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
