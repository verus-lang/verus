#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] basic verus_code! {
        tracked struct Y {
            ghost y: int
        }

        tracked struct X {
            ghost g: int,
            tracked g2: Ghost<int>,
            tracked y: Y,
        }

        uninterp spec fn arbitrary<A>() -> A;

        proof fn test(tracked y: &Y) -> (tracked x: &X)
            ensures x.y == y && x.g == 0
        {
            shr_ref_struct_wrap(y, &X { g: 0, g2: Ghost(0), y: arbitrary() }, "", "y")
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] with_type_inv verus_code! {
        tracked struct Y { ghost y: int }
        tracked struct XWithInv { ghost g: int, tracked y: Y }

        #[verifier::type_invariant]
        spec fn inv(x: &XWithInv) -> bool {
            x.y.y == x.g
        }

        uninterp spec fn arbitrary<A>() -> A;

        proof fn test2(tracked y: &Y) -> (tracked x: &XWithInv)
        {
            shr_ref_struct_wrap(y, &XWithInv { g: y.y, y: arbitrary() }, "", "y")
        }

        proof fn test3(tracked y: &Y) -> (tracked x: &XWithInv)
        {
            shr_ref_struct_wrap(y, &XWithInv { g: 0, y: arbitrary() }, "", "y") // FAILS
        }
    } => Err(err) => assert_fails_type_invariant_error(err, 1)
}

test_verify_one_file! {
    #[test] malformed1 verus_code! {
        tracked struct Y { ghost y: int }
        tracked struct XWithInv { ghost g: int, tracked y: Y }

        proof fn test1() {
            let tracked t = shr_ref_struct_wrap(&0int, &1int, "", "somefield");
        }
    } => Err(err) => assert_vir_error_msg(err, "second argument to `shr_ref_struct_wrap` should be a datatype")
}

test_verify_one_file! {
    #[test] malformed2 verus_code! {
        tracked struct Y { ghost y: int }
        tracked struct XWithInv { ghost g: int, tracked y: Y }

        proof fn test1() {
            let tracked t = shr_ref_struct_wrap(&0int, &(1int, 2int), "", "0");
        }
    } => Err(err) => assert_vir_error_msg(err, "shr_ref_struct_wrap not supported for tuples")
}

test_verify_one_file! {
    #[test] malformed3 verus_code! {
        mod m {
            use super::*;
            pub tracked struct Y {
                pub ghost y: int
            }

            pub tracked struct X {
                ghost g: int,
                tracked g2: Ghost<int>,
                tracked y: Y,
            }
        }
        use m::Y;
        use m::X;

        uninterp spec fn arbitrary<A>() -> A;

        proof fn test(tracked y: &Y) -> (tracked x: &X) {
            shr_ref_struct_wrap(y, arbitrary(), "", "y")
        }
    } => Err(err) => assert_vir_error_msg(err, "disallowed: `shr_ref_struct_wrap` operator for an opaque datatype")
}

test_verify_one_file! {
    #[test] malformed4 verus_code! {
        mod m {
            use super::*;
            pub tracked struct Y { pub ghost y: int }
            pub(crate) tracked struct XWithInv { pub(crate) ghost g: int, pub(crate) tracked y: Y }

            #[verifier::type_invariant]
            spec fn inv(x: &XWithInv) -> bool {
                x.y.y == x.g
            }
        }
        use m::Y;
        use m::XWithInv;

        uninterp spec fn arbitrary<A>() -> A;

        proof fn test2(tracked y: &Y) -> (tracked x: &XWithInv)
        {
            shr_ref_struct_wrap(y, &XWithInv { g: y.y, y: arbitrary() }, "", "y")
        }
    } => Err(err) => assert_vir_error_msg(err, "type invariant function is not visible to this program point, which requires us to prove the invariant is preserved")
}

test_verify_one_file! {
    #[test] malformed5 verus_code! {
        tracked struct Y {
            ghost y: int
        }

        tracked struct X {
            ghost g: int,
            tracked g2: Ghost<int>,
            tracked y: Y,
        }

        uninterp spec fn arbitrary<A>() -> A;

        proof fn test(tracked y: &Y) -> (tracked x: &X) {
            shr_ref_struct_wrap(&0int, &arbitrary(), "", "g")
        }
    } => Err(err) => assert_vir_error_msg(err, "shr_ref_struct_wrap cannot target ghost-mode field")
}

test_verify_one_file! {
    #[test] malformed6 verus_code! {
        tracked struct Y {
            ghost y: int
        }

        ghost struct X {
            ghost g: int,
            ghost g2: Ghost<int>,
            ghost y: Y,
        }

        uninterp spec fn arbitrary<A>() -> A;

        proof fn test(tracked y: &Y) -> (tracked x: &X) {
            shr_ref_struct_wrap(&0int, &arbitrary(), "", "g")
        }
    } => Err(err) => assert_vir_error_msg(err, "shr_ref_struct_wrap cannot target ghost-mode datatype")
}

test_verify_one_file! {
    #[test] malformed7 verus_code! {
        tracked struct Y {
            ghost y: int
        }

        tracked struct X {
            ghost g: int,
            tracked g2: Tracked<int>,
            tracked y: Y,
        }

        uninterp spec fn arbitrary<A>() -> A;

        proof fn test(tracked y: &Y) -> (tracked x: &X) {
            shr_ref_struct_wrap(y, &arbitrary(), "", "y")
        }
    } => Err(err) => assert_vir_error_msg(err, "shr_ref_struct_wrap can only be applied when all other fields of the relevant variant are ghost-mode or of type Ghost (field `g2` does not meet this requirement)")
}

test_verify_one_file! {
    #[test] malformed8 verus_code! {
        tracked struct Y {
            ghost y: int
        }

        tracked enum X {
            Foo {
                ghost g: int,
                tracked g2: Tracked<int>,
                tracked y: Y,
            },
            Bar {
                ghost g3: int,
            }
        }

        uninterp spec fn arbitrary<A>() -> A;

        proof fn test(tracked y: &Y) -> (tracked x: &X) {
            shr_ref_struct_wrap(y, &arbitrary(), "Foo", "y")
        }
    } => Err(err) => assert_vir_error_msg(err, "shr_ref_struct_wrap can only be applied when all other fields of the relevant variant are ghost-mode or of type Ghost (field `g2` does not meet this requirement)")
}

test_verify_one_file! {
    #[test] malformed9 verus_code! {
        tracked struct Y {
            ghost y: int
        }

        tracked enum X {
            Foo {
                ghost g: int,
                tracked g2: Tracked<int>,
                tracked y: Y,
            },
            Bar {
                ghost g3: int,
            }
        }

        uninterp spec fn arbitrary<A>() -> A;

        proof fn test(tracked y: &Y) -> (tracked x: &X) {
            shr_ref_struct_wrap(y, &arbitrary(), "", "y")
        }
    } => Err(err) => assert_vir_error_msg(err, "no variant named ``")
}

test_verify_one_file! {
    #[test] lifetime_error verus_code! {
        tracked struct Y {
            ghost y: int
        }

        tracked struct X {
            ghost g: int,
            tracked g2: Ghost<int>,
            tracked y: Y,
        }

        uninterp spec fn arbitrary<A>() -> A;

        proof fn consume<A>(tracked a: A) { }

        proof fn test() {
            let tracked mut y = Y { y: 0 };
            let tracked k = shr_ref_struct_wrap(&y, &X { g: 0, g2: Ghost(0), y: arbitrary() }, "", "y");
            y = Y { y: 1 };
            consume(k);
        }
    } => Err(err) => assert_rust_error_msg(err, "cannot assign to `y` because it is borrowed")
}

test_verify_one_file! {
    #[test] with_enum verus_code! {
        tracked struct Y {
            ghost y: int
        }

        tracked enum X {
            Foo {
                ghost g: int,
                tracked g2: Ghost<int>,
                tracked y: Y,
            },
            Bar {
                tracked a: Y,
                tracked b: Y,
                tracked c: Y,
            }
        }

        uninterp spec fn arbitrary<A>() -> A;

        proof fn test(tracked y: &Y) -> (tracked x: &X)
            ensures x is Foo && x->Foo_y == y && x->Foo_g == 0 && x->Foo_g2 === Ghost(0),
        {
            shr_ref_struct_wrap(y, &X::Foo { g: 0, g2: Ghost(0), y: arbitrary() }, "Foo", "y")
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] with_enum2 verus_code! {
        tracked struct Y {
            ghost y: int
        }

        tracked enum X {
            Foo {
                ghost g: int,
                tracked g2: Ghost<int>,
                tracked y: Y,
            },
            Bar {
                tracked a: Y,
                tracked b: Y,
                tracked c: Y,
            }
        }

        uninterp spec fn arbitrary<A>() -> A;

        proof fn test(tracked y: &Y) {
            // should probably be a recommends error
            let tracked r: &X = shr_ref_struct_wrap(y, &arbitrary(), "Foo", "y");
            assert(r is Foo);
            let arbx = arbitrary::<X>();
            assert(r->Foo_g === arbx->Foo_g);
            assert(r->Foo_g2 === arbx->Foo_g2);
            assert(r->Foo_y == y);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] mode_error verus_code! {
        tracked struct Y {
            ghost y: int
        }

        tracked struct X {
            ghost g: int,
            tracked g2: Ghost<int>,
            tracked y: Y,
        }

        uninterp spec fn arbitrary<A>() -> A;

        proof fn test(y: &Y) -> (tracked x: &X)
            ensures x.y == y && x.g == 0
        {
            shr_ref_struct_wrap(y, &X { g: 0, g2: Ghost(0), y: arbitrary() }, "", "y")
        }
    } => Err(err) => assert_vir_error_msg(err, "expression has mode spec, expected mode proof")
}

test_verify_one_file! {
    #[test] mode_error2 verus_code! {
        struct X {
            g: u64,
        }

        fn test(y: &u64) {
            shr_ref_struct_wrap(y, &X { g: 0 }, "", "g");
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot use `shr_ref_struct_wrap` in executable context")
}

test_verify_one_file! {
    #[test] mode_error3 verus_code! {
        struct X {
            g: u64,
        }

        uninterp spec fn arbitrary<A>() -> A;

        spec fn test(y: &u64) -> &X {
            shr_ref_struct_wrap(y, &arbitrary(), "", "g")
        }
    } => Err(err) => assert_vir_error_msg(err, "cannot use `shr_ref_struct_wrap` which has mode proof here")
}

test_verify_one_file! {
    #[test] mode_error4_proph verus_code! {
        struct X {
            g: u64,
        }

        #[verifier::prophetic]
        uninterp spec fn arbitrary<A>() -> A;

        proof fn test(tracked y: &u64) -> (tracked x: &X) {
            shr_ref_struct_wrap(y, &arbitrary(), "", "g")
        }
    } => Err(err) => assert_vir_error_msg(err, "prophetic value not allowed for `shr_ref_struct_wrap`")
}
