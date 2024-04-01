#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test1 verus_code! {
        enum E1 {
            N(),
            E(Box<E1>),
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test2 verus_code! {
        enum E1 {
            N(),
            E(Box<E2>),
        }

        enum E2 {
            N(),
            E(Box<E1>),
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test3 verus_code! {
        struct List<A> {
            a: A,
        }

        enum E1 {
            N(),
        }

        enum E2 {
            N(),
            E(Box<E1>),
            F(List<Box<E1>>),
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test4 verus_code! {
        struct List<A> {
            a: A,
        }

        enum E2 {
            N(),
            E(Box<E1>),
            F(List<Box<E1>>),
        }

        enum E1 {
            N(),
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test1_ok verus_code! {
        struct List<A> {
            a: A,
        }

        enum E1 {
            N(),
            E(Box<E1>),
            F(List<Box<E1>>),
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test1_fails verus_code! {
        #[verifier::reject_recursive_types(A)]
        struct List<A> {
            a: A,
        }

        enum E1 {
            N(),
            E(Box<E1>),
            F(List<Box<E1>>),
        }
    } => Err(err) => assert_vir_error_msg(err, "in a non-positive position")
}

test_verify_one_file! {
    #[test] test2_ok verus_code! {
        struct List<A> {
            a: A,
        }

        enum E1 {
            N(),
            E(Box<E2>),
            F(List<Box<E2>>),
        }

        enum E2 {
            N(),
            E(Box<E1>),
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test2_fails verus_code! {
        #[verifier::reject_recursive_types(A)]
        struct List<A> {
            a: A,
        }

        enum E1 {
            N(),
            E(Box<E2>),
            F(List<Box<E2>>),
        }

        enum E2 {
            N(),
            E(Box<E1>),
        }
    } => Err(err) => assert_vir_error_msg(err, "in a non-positive position")
}

test_verify_one_file! {
    #[test] test3_ok verus_code! {
        struct List<A> {
            a: A,
        }

        enum E1 {
            N(),
            E(Box<E2>),
        }

        enum E2 {
            N(),
            E(Box<E1>),
            F(List<Box<E1>>),
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test3_fails verus_code! {
        #[verifier::reject_recursive_types(A)]
        struct List<A> {
            a: A,
        }

        enum E1 {
            N(),
            E(Box<E2>),
        }

        enum E2 {
            N(),
            E(Box<E1>),
            F(List<Box<E1>>),
        }
    } => Err(err) => assert_vir_error_msg(err, "in a non-positive position")
}

test_verify_one_file! {
    #[test] test5_ok verus_code! {
        #[verifier(external_body)] /* vattr */
        #[verifier::reject_recursive_types(K)]
        #[verifier::accept_recursive_types(V)]
        struct Map<K, V> {
            dummy: std::marker::PhantomData<(K, V)>,
        }

        #[verifier::reject_recursive_types(A)]
        struct D<A, B> {
            d: Map<int, D<A, B>>,
            a: Map<A, int>,
            b: Map<int, B>,
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test5_fails1 verus_code! {
        #[verifier(external_body)] /* vattr */
        #[verifier::reject_recursive_types(K)]
        struct Map<K, V> {
            dummy: std::marker::PhantomData<(K, V)>,
        }
    } => Err(err) => assert_vir_error_msg(err, "in external_body datatype, each type parameter must be one of: #[verifier::reject_recursive_types], #[verifier::reject_recursive_types_in_ground_variants], #[verifier::accept_recursive_types]")
}

test_verify_one_file! {
    #[test] test5_fails2 verus_code! {
        #[verifier(external_body)] /* vattr */
        #[verifier::reject_recursive_types(K)]
        #[verifier::accept_recursive_types(V)]
        struct Map<K, V> {
            dummy: std::marker::PhantomData<(K, V)>,
        }

        struct D<A, B> {
            d: Map<int, D<A, B>>,
            a: Map<A, int>,
            b: Map<int, B>,
        }
    } => Err(err) => assert_vir_error_msg(err, "Type parameter A of crate::D must be declared #[verifier::reject_recursive_types] to be used in a non-positive position")
}

test_verify_one_file! {
    #[test] test5_fails3 verus_code! {
        #[verifier(external_body)] /* vattr */
        #[verifier::reject_recursive_types(K)]
        #[verifier::accept_recursive_types(V)]
        struct Map<K, V> {
            dummy: std::marker::PhantomData<(K, V)>,
        }

        #[verifier::reject_recursive_types(A)]
        struct D<A, B> {
            d: Map<D<A, B>, int>,
            a: Map<A, int>,
            b: Map<int, B>,
        }
    } => Err(err) => assert_vir_error_msg(err, "in a non-positive position")
}

test_verify_one_file! {
    #[test] lifetimes_no_positivity verus_code! {
        #[verifier(external_body)] /* vattr */
        struct Str<'a> {
            inner: &'a str,
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] fnspec_positivity verus_code! {
        struct S {
            f: spec_fn(S) -> int,
        }
    } => Err(err) => assert_vir_error_msg(err, "in a non-positive position")
}

test_verify_one_file! {
    #[test] type_argument_in_nested_negative_position verus_code! {
        #[verifier(external_body)]
        #[verifier::reject_recursive_types(A)]
        pub struct Set<A> {
            dummy: std::marker::PhantomData<A>,
        }
        struct X<A>(A);
        struct Y<A>(Set<X<A>>);
        struct Z(Y<Z>);
    } => Err(err) => assert_vir_error_msg(err, "Type parameter A of crate::Y must be declared #[verifier::reject_recursive_types] to be used in a non-positive position")
}

test_verify_one_file! {
    #[test] no_ground_variant1 verus_code! {
        #[verifier::accept_recursive_types(A)]
        struct DataWrapper<A> { a: A } // error: no ground variant without A
    } => Err(err) => assert_vir_error_msg(err, "datatype must have at least one non-recursive variant")
}

test_verify_one_file! {
    #[test] no_ground_variant2 verus_code! {
        enum UngroundedList<A> {
            // error: no ground variant; the only variant is Cons, which recursively uses UngroundedList
            Cons(A, Box<UngroundedList<A>>),
        }
    } => Err(err) => assert_vir_error_msg(err, "datatype must have at least one non-recursive variant")
}

test_verify_one_file! {
    #[test] no_ground_variant_via_generics1 verus_code! {
        // from https://github.com/verus-lang/verus/issues/538
        struct I<A>(A);
        struct R(Box<I<R>>);

        proof fn bad(r: R)
            ensures false
            decreases r
        {
            bad(r.0.0);
        }

        spec fn make_r() -> R;

        proof fn test()
            ensures false
        {
            bad(make_r())
        }
    } => Err(err) => assert_vir_error_msg(err, "datatype must have at least one non-recursive variant")
}

test_verify_one_file! {
    #[test] no_ground_variant_via_generics2 verus_code! {
        // from https://github.com/verus-lang/verus/issues/538
        #[verifier::accept_recursive_types(A)]
        struct I<A>(A);
        struct R(Box<I<R>>);

        proof fn bad(r: R)
            ensures false
            decreases r
        {
            bad(r.0.0);
        }

        spec fn make_r() -> R;

        proof fn test()
            ensures false
        {
            bad(make_r())
        }
    } => Err(err) => assert_vir_error_msg(err, "datatype must have at least one non-recursive variant")
}

test_verify_one_file! {
    #[test] reject_recursive_types_ill_formed1 verus_code! {
        #[verifier::reject_recursive_types(D)]
        struct X<A, B, C> { a: A, b: B, c: C, d: bool }
    } => Err(err) => assert_vir_error_msg(err, "unused parameter attribute D")
}

test_verify_one_file! {
    #[test] reject_recursive_types_ill_formed2 verus_code! {
        #[verifier::reject_recursive_types(A)]
        #[verifier::reject_recursive_types(A)]
        struct X<A, B, C> { a: A, b: B, c: C, d: bool }
    } => Err(err) => assert_vir_error_msg(err, "duplicate parameter attribute A")
}
