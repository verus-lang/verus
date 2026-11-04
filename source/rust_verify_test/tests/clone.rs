#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] trivial_clone_ok verus_code! {
        use vstd::prelude::*;
        use std::clone::TrivialClone;

        struct X { u: u64 }

        unsafe impl TrivialClone for X { }

        impl Clone for X {
            fn clone(&self) -> Self {
                X { u: self.u }
            }
        }

        fn test(x: X) {
            let y = x.clone();
            assert(y == x);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] trivial_clone_fail verus_code! {
        use vstd::prelude::*;
        use std::clone::TrivialClone;

        struct X { u: u64 }

        unsafe impl TrivialClone for X { }

        impl Clone for X {
            fn clone(&self) -> Self { // FAILS
                X { u: 20 }
            }
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] trivial_clone_generic verus_code! {
        use vstd::prelude::*;
        use std::clone::TrivialClone;

        struct X<T> { t: T }

        unsafe impl<T: TrivialClone> TrivialClone for X<T> { }

        impl<T: Clone> Clone for X<T> {
            fn clone(&self) -> Self { // FAILS
                X { t: self.t.clone() }
            }
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] trivial_clone_derive verus_code! {
        use vstd::prelude::*;

        #[derive(Clone, Copy)]
        struct X { u: u64 }

        fn test(x: X) {
            let y = x.clone();
            assert(y == x);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] trivial_clone_derive_fail verus_code! {
        use vstd::prelude::*;
        use std::clone::TrivialClone;

        #[derive(Clone, Copy)]
        struct X { u: Box<u64> } // FAILS

        unsafe impl TrivialClone for X { }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] trivial_clone_external_clone verus_code! {
        use vstd::prelude::*;
        use std::clone::TrivialClone;

        struct X { u: u64 }

        unsafe impl TrivialClone for X { }

        #[verifier::external]
        impl Clone for X {
            fn clone(&self) -> Self {
                X { u: 20 }
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "the `Clone` impl corresponding to this `TrivialClone` impl is not known to Verus")
}
