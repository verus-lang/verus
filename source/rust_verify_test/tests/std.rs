#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] rc_arc verus_code! {
        use std::rc::Rc;
        use std::sync::Arc;

        fn foo() {
            let x = Rc::new(5);
            assert(*x == 5) by {}

            let x1 = x.clone();
            assert(*x1 == 5) by {}

            let y = Arc::new(5);
            assert(*y == 5) by {}

            let y1 = y.clone();
            assert(*y1 == 5) by {}
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] ref_clone verus_code! {
        struct X { }

        fn test2(x: &X) { }

        fn test(x: &X) {
            // Since X is not clone, Rust resolves this to a clone of the reference type &X
            // So this is basically the same as `let y = x;`
            let y = x.clone();
            assert(x == y);
            test2(y);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] external_clone_fail verus_code! {
        // Make sure the support for &X clone doesn't mistakenly trigger in other situations

        struct X { }

        #[verifier(external)]
        impl Clone for X {
            fn clone(&self) -> Self {
                X { }
            }
        }

        fn foo(x: &X) {
            let y = x.clone();
        }
    } => Err(err) => assert_vir_error_msg(err, "method call to method not defined in this crate")
}

test_verify_one_file! {
    #[test] box_new verus_code! {
        fn foo() {
            let x:Box<u32> = Box::new(5);
            assert(*x == 5);
        }
    } => Ok(())
}
