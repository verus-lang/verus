#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test1 verus_code! {
        #[verifier(inline)]
        spec fn fi(x: int, y: int) -> int {
            x + 2 * y
        }

        spec fn f1(x: int, y: int) -> int {
            x + 2 * y
        }

        #[verifier(inline)]
        spec fn f2(x: int, y: int) -> int {
            f1(x, y)
        }

        #[verifier(inline)]
        spec fn f3(a: int, b: int) -> int {
            f1(a, b)
        }

        #[verifier(inline)]
        spec fn f4(a: int, b: int) -> int {
            let za = a + 1;
            let zb = b + 1;
            f1(za - 1, zb - 1)
        }

        #[verifier(inline)]
        spec fn fg<A, B>(a: A, b: B) -> (B, A) {
            (b, a)
        }

        spec fn fx(x: int) -> bool;

        #[verifier(inline)]
        spec fn fy(x: int) -> bool {
            fx(x)
        }

        spec fn fpx<A>(x: A) -> bool;

        #[verifier(inline)]
        spec fn fpy<A>(x: A) -> bool {
            fpx(x)
        }

        proof fn test()
            requires
                forall|i: int| fy(i),
                forall|i: u8| fpy(i),
        {
            assert(fi(33, 44) == 121);
            assert(f1(33, 44) == 121);
            assert(f2(33, 44) == 121);
            assert(f3(33, 44) == 121);
            assert({let za = 44; f4(33, za) == 121});
            assert(fg(10u8, true) === (true, 10u8));
            assert(fx(7));
            assert(fy(6));
            assert(fpx(7u8));
            assert(fpy(6u8));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_private_fails verus_code! {
        #[verifier(inline)]
        pub closed spec fn f(x: int, y: int) -> int {
            x + 2 * y
        }
    } => Err(err) => assert_vir_error_msg(err, "'inline' is only allowed for private or 'open spec' functions")
}

test_verify_one_file! {
    #[test] test_nonspec_fails verus_code! {
        #[verifier(inline)]
        proof fn f() {
        }
    } => Err(err) => assert_vir_error_msg(err, "'inline' is only allowed for 'spec' functions")
}

test_verify_one_file! {
    #[test] test_rec_fails1 verus_code! {
        #[verifier(inline)]
        spec fn f(n: nat) -> nat
            decreases n
        {
            0
        }
    } => Err(err) => assert_vir_error_msg(err, "'inline' functions cannot be recursive")
}

test_verify_one_file! {
    #[test] test_rec_fails2 verus_code! {
        #[verifier(inline)]
        spec fn f(n: nat) -> nat
        {
            if n == 0 {
                0
            } else {
                f((n - 1) as nat)
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "recursive function must have a decreases clause")
}

test_verify_one_file! {
    #[test] test_no_body_fails verus_code! {
        #[verifier(inline)]
        spec fn f(n: nat) -> nat;
    } => Err(err) => assert_vir_error_msg(err, "'inline' functions must have a body")
}

test_verify_one_file! {
    #[test] test_spec_fn verus_code! {
        #[verifier(inline)]
        spec fn f1(i: int, j: int) -> bool {
            i <= j
        }

        #[verifier(inline)]
        spec fn f2(i: int, j: int) -> bool {
            let x = i;
            let y = j;
            x < y
        }

        #[verifier(opaque)]
        spec fn f3(i: int, j: int) -> bool {
            f1(j, i)
        }

        fn test_spec_fn(a: int, b: int) {
            hide(f2);

            assume(f2(a, b));
            proof {
                reveal(f2);
            }
            assert(f1(a, b));

            proof {
                reveal(f3);
            }
            assert(f3(b, a));
            assert(f3(a, b)); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_ensures_type_inference verus_code! {
        struct Foo {
            pub b: bool,
        }

        #[verifier(inline)]
        spec fn get_b(foo: Foo) -> bool {
            foo.b
        }

        fn test1() -> (b: Foo)
            ensures get_b(b)
        {
            Foo { b: true }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] inline_poly verus_code! {
        use vstd::prelude::*;

        #[verifier::inline]
        spec fn all_contains<A>(s1: Set<A>) -> bool {
            forall|a: A| s1.contains(a)
        }

        proof fn failing_proof(s: Set<int>) {
            assert(all_contains(s)); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}
