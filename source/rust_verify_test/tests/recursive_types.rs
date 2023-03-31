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
        struct List<#[verifier(maybe_negative)] /* vattr */ A> {
            a: A,
        }

        enum E1 {
            N(),
            E(Box<E1>),
            F(List<Box<E1>>),
        }
    } => Err(err) => assert_vir_error_msg(err, "in a non-positive polarity")
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
        struct List<#[verifier(maybe_negative)] /* vattr */ A> {
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
    } => Err(err) => assert_vir_error_msg(err, "in a non-positive polarity")
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
        struct List<#[verifier(maybe_negative)] /* vattr */ A> {
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
    } => Err(err) => assert_vir_error_msg(err, "in a non-positive polarity")
}

test_verify_one_file! {
    #[test] test5_ok verus_code! {
        #[verifier(external_body)] /* vattr */
        struct Map<#[verifier(maybe_negative)] /* vattr */ K, #[verifier(strictly_positive)] /* vattr */ V> {
            dummy: std::marker::PhantomData<(K, V)>,
        }

        struct D<#[verifier(maybe_negative)] /* vattr */ A, B> {
            d: Map<int, D<A, B>>,
            a: Map<A, int>,
            b: Map<int, B>,
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test5_fails1 verus_code! {
        #[verifier(external_body)] /* vattr */
        struct Map<#[verifier(maybe_negative)] /* vattr */ K, V> {
            dummy: std::marker::PhantomData<(K, V)>,
        }
    } => Err(err) => assert_vir_error_msg(err, "in external_body datatype, each type parameter must be either #[verifier(maybe_negative)] or #[verifier(strictly_positive)]")
}

test_verify_one_file! {
    #[test] test5_fails2 verus_code! {
        #[verifier(external_body)] /* vattr */
        struct Map<#[verifier(maybe_negative)] /* vattr */ K, #[verifier(strictly_positive)] /* vattr */ V> {
            dummy: std::marker::PhantomData<(K, V)>,
        }

        struct D<A, B> {
            d: Map<int, D<A, B>>,
            a: Map<A, int>,
            b: Map<int, B>,
        }
    } => Err(err) => assert_vir_error_msg(err, "Type parameter A must be declared #[verifier(maybe_negative)] to be used in a non-positive position")
}

test_verify_one_file! {
    #[test] test5_fails3 verus_code! {
        #[verifier(external_body)] /* vattr */
        struct Map<#[verifier(maybe_negative)] /* vattr */ K, #[verifier(strictly_positive)] /* vattr */ V> {
            dummy: std::marker::PhantomData<(K, V)>,
        }

        struct D<#[verifier(maybe_negative)] /* vattr */ A, B> {
            d: Map<D<A, B>, int>,
            a: Map<A, int>,
            b: Map<int, B>,
        }
    } => Err(err) => assert_vir_error_msg(err, "in a non-positive polarity")
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
            f: FnSpec(S) -> int,
        }
    } => Err(err) => assert_vir_error_msg(err, "in a non-positive polarity")
}
