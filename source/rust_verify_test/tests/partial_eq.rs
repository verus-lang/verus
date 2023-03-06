#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    // TODO: support floating point
    // NOTE (SOUNDNESS): need to make sure that executable code doesn't assume equality on NAN
    // (f32/f64 do not implement Structural)
    #[test] #[ignore] test_float_nan verus_code! {
        fn float_nan() {
            assert(f64::NAN == f64::NAN); // this should succeed (ghost equality)
            let n1 = f64::NAN;
            let n2 = f64::NAN;
            assert(n1 == n2); // this should succeed
            let b = (n1 == n2); // exec equality is not naive value equality; it's more complicated
            // this should fail:
            assert(b); // FAILS
        }
    } => Err(e) => assert_one_fails(e)
}
