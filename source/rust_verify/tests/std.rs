#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] rc_arc code! {
        use std::rc::Rc;
        use std::sync::Arc;

        fn foo() {
            let x = Rc::new(5);
            assert_by(*x == 5, {});

            let x1 = x.clone();
            assert_by(*x1 == 5, {});

            let y = Arc::new(5);
            assert_by(*y == 5, {});

            let y1 = y.clone();
            assert_by(*y1 == 5, {});
        }
    } => Ok(())
}
