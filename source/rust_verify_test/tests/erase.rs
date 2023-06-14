#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test_regression_78 verus_code! {
        use vstd::prelude::*;

        proof fn f1<T>(t: Ghost<Option<T>>) {
            let x = t.view().get_Some_0();
        }

        spec fn f2() -> bool {
            let x: Option<usize> = Option::None;
            x.is_None()
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_regression_70 verus_code! {
        fn m(v: &mut u64) { }

        fn main() {
            let v = 6;
            m(&mut v);
        }
    } => Err(err) => assert_rust_error_msg(err, "cannot borrow `v` as mutable, as it is not declared as mutable")
}
