#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_with_pervasive! {
    #[test] test_box_unbox_struct code! {
        #[derive(Eq, PartialEq)]
        struct Thing<A> {
            a: A,
        }

        fn one(v: int) {
            let t1 = Thing { a: v };
            let t2 = Thing { a: v };
            let a: int = t2.a;
        }
    } => Ok(())
}

test_verify_with_pervasive! {
    #[test] test_box_enum code! {
        #[derive(Eq, PartialEq)]
        enum Thing<A> {
            First(A),
        }

        fn one(v: int) {
            let t1 = Thing::First(v);
        }
    } => Ok(())
}
