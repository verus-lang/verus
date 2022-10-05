#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test1 code! {
        enum E1 {
            N(),
            E(Box<E1>),
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test2 code! {
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
    #[test] test3 code! {
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
    #[test] test4 code! {
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
    #[test] test1_ok code! {
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
    #[test] test1_fails code! {
        struct List<#[verifier(maybe_negative)] A> {
            a: A,
        }

        enum E1 {
            N(),
            E(Box<E1>),
            F(List<Box<E1>>),
        }
    } => Err(_)
}

test_verify_one_file! {
    #[test] test2_ok code! {
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
    #[test] test2_fails code! {
        struct List<#[verifier(maybe_negative)] A> {
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
    } => Err(_)
}

test_verify_one_file! {
    #[test] test3_ok code! {
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
    #[test] test3_fails code! {
        struct List<#[verifier(maybe_negative)] A> {
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
    } => Err(_)
}

test_verify_one_file! {
    #[test] test5_ok code! {
        #[verifier(external_body)]
        struct Map<#[verifier(maybe_negative)] K, #[verifier(strictly_positive)] V> {
            dummy: std::marker::PhantomData<(K, V)>,
        }

        struct D<#[verifier(maybe_negative)] A, B> {
            d: Map<int, D<A, B>>,
            a: Map<A, int>,
            b: Map<int, B>,
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test5_fails1 code! {
        #[verifier(external_body)]
        struct Map<#[verifier(maybe_negative)] K, V> {
            dummy: std::marker::PhantomData<(K, V)>,
        }
    } => Err(_)
}

test_verify_one_file! {
    #[test] test5_fails2 code! {
        #[verifier(external_body)]
        struct Map<#[verifier(maybe_negative)] K, #[verifier(strictly_positive)] V> {
            dummy: std::marker::PhantomData<(K, V)>,
        }

        struct D<A, B> {
            d: Map<int, D<A, B>>,
            a: Map<A, int>,
            b: Map<int, B>,
        }
    } => Err(_)
}

test_verify_one_file! {
    #[test] test5_fails3 code! {
        #[verifier(external_body)]
        struct Map<#[verifier(maybe_negative)] K, #[verifier(strictly_positive)] V> {
            dummy: std::marker::PhantomData<(K, V)>,
        }

        struct D<#[verifier(maybe_negative)] A, B> {
            d: Map<D<A, B>, int>,
            a: Map<A, int>,
            b: Map<int, B>,
        }
    } => Err(_)
}

test_verify_one_file! {
    #[test] lifetimes_no_positivity code! {
        #[verifier(external_body)]
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
    } => Err(_)
}
