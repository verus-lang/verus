#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    // TODO: SOUNDNESS; when the `f64::NAN` expression is supported, this may be unsound
    #[test] #[ignore] test_float_nan code! {
        fn float_nan() {
            assert(f64::NAN != f64::NAN);
        }
    } => Ok(())
}
