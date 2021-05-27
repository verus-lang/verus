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

test_verify_with_pervasive! {
    #[test] test_generic_adt_eq code! {
        #[derive(Eq, PartialEq)]
        struct Thing<A> {
            a: A,
        }

        fn one(v: int) {
            let t1 = Thing { a: v };
            let t2 = Thing { a: v };
            let a1: int = t1.a;
            let a2: int = t2.a;
            assert(a1 == a2);
            assert(a1 != a2); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}
