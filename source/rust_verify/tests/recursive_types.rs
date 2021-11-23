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
    #[test] test1_fails code! {
        struct List<A> {
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
    #[test] test2_fails code! {
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
    } => Err(_)
}

test_verify_one_file! {
    #[test] test3_fails code! {
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
    } => Err(_)
}
