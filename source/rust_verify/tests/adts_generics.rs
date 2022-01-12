#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test_box_unbox_struct code! {
        #[derive(Eq, PartialEq)]
        struct Thing<A> {
            a: A,
        }

        #[proof]
        fn one(v: int) {
            let t1 = Thing { a: v };
            let t2 = Thing { a: v };
            let a: int = t2.a;
        }

        fn two(v: Thing<u8>) {
            assert(v.a >= 0);
        }
    } => Ok(())
}

test_verify_one_file! {
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

test_verify_one_file! {
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

test_verify_one_file! {
    #[test] test_generic_adt_u8 code! {
        #[derive(Eq, PartialEq)]
        struct Thing<A> {
            a: A,
        }

        fn two(v: Thing<u8>) {
            assert(v.a >= 1); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_refinements1 code! {
        struct X {
            u: u64,
        }

        fn aa<A>(a: A) -> A {
            a
        }

        #[spec]
        #[opaque]
        fn id<A>(a: A) -> A {
            a
        }

        fn f() -> X {
            let x = X { u: 3 };
            let y = aa(x);
            assert(id(y.u) >= 0);
            assert(y.u >= 0);
            y
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_refinements1_fail code! {
        struct X {
            u: u64,
        }

        fn aa<A>(a: A) -> A {
            a
        }

        #[spec]
        #[opaque]
        fn id<A>(a: A) -> A {
            a
        }

        fn f() -> X {
            let x = X { u: 3 };
            let y = aa(x);
            assert(id(y.u) >= 1); // FAILS
            assert(y.u >= 0);
            y
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_refinements2 code! {
        struct P<A> {
            a: A,
        }

        #[spec]
        #[opaque]
        fn id<A>(a: A) -> A {
            a
        }

        fn fp(p: P<u64>) {
            assert(p.a >= 0);
            let p2: P<u8> = P { a: 2 };
            assert(id(p).a >= 0);
            assert(id(p2).a >= 0);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_refinements2_fails code! {
        struct P<A> {
            a: A,
        }

        #[spec]
        #[opaque]
        fn id<A>(a: A) -> A {
            a
        }

        fn fp(p: P<u64>) {
            assert(p.a >= 0);
            let p2: P<u8> = P { a: 2 };
            assert(id(p).a >= 0);
            assert(id(p2).a >= 1); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_out_of_order code! {
        struct XY {
            tz: TZ,
        }
        struct TZ {
            p: (u64, u64),
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_triggers code! {
        struct S {
            i: int,
        }

        #[opaque]
        #[spec]
        fn fi(i: int) -> bool {
            true
        }

        #[opaque]
        #[spec]
        fn fs(s: S) -> bool {
            true
        }

        fn test_struct_field_trigger(s: S) {
            requires(forall(|s: S| fi(s.i)));
            assert(fi(s.i));
        }

        fn test_struct_constructor_arg_trigger() {
            requires(forall(|i: int| fs(S {i: i})));
            assert(fs(S {i: 5}));
        }
    } => Ok(())
}
