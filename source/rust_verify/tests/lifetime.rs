#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test1 code! {
        #[proof]
        fn consume<A>(#[proof] a: A) {
        }

        #[proof]
        fn test1<A>(#[proof] a: A) {
            consume(a);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test1_fail code! {
        #[proof]
        fn consume<A>(#[proof] a: A) {
        }

        #[proof]
        fn test1<A>(#[proof] a: A) {
            consume(a);
            consume(a);
        }
    } => Err(_) => ()
}

test_verify_one_file! {
    #[test] lifetime_bounds code! {
        #[verifier(external_body)]
        #[verifier(returns(proof))]
        #[proof]
        pub fn proof_to_ref<'a, T: 'a>(#[proof] t: T) -> &'a T {
            ensures(|t2: &'a T| equal(t, *t2));
            unimplemented!();
        }

        struct Foo<'a, T: 'a> {
            #[proof] pub t: &'a T,
        }

        pub fn mk_foo<'a, T: 'a>(t: T) -> Foo<'a, T> {
            Foo { t: proof_to_ref(t) }
        }

        impl<'a, T> Foo<'a, T> {
            fn mk_foo2(t: T) -> Self {
                mk_foo(t)
            }
        }

        impl<T> Foo<'_, T> {
            fn mk_foo3(t: T) -> Self {
                Foo::mk_foo2(t)
            }
        }

        impl<'a, T> Foo<'a, T> {
            fn mk_foo4(t: T) -> Self {
                Foo::<'a, T>::mk_foo3(t)
            }
        }

        pub fn mk_foo5<'a, 'b: 'a, T: 'a, U: 'b>(t: T, u: U) -> (Foo<'a, T>, Foo<'b, U>) {
            (
                Foo { t: proof_to_ref(t) },
                Foo { t: proof_to_ref(u) },
            )
        }

        #[verifier(returns(spec))]
        fn bar<'a, F: Fn(u32) -> bool>(#[spec] f: F, #[spec] v: u32, foo: Foo<'a, u32>) -> bool {
            f(v)
        }
    } => Ok(())
}
