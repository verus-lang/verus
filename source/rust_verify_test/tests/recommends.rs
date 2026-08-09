#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] ensures_forall_recommends_failure verus_code! {
        spec fn foo(i: int) -> bool
          recommends 0 <= i < 5,
        {
          i + 3 == 20
        }

        proof fn some_proof()
            ensures forall |i: int| 0 <= i < 20 ==> foo(i),  // FAILS
        {
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] ensures_type_substitutes_issue1566 verus_code! {
        use vstd::*;
        use vstd::seq::*;

        struct W { }

        spec fn bar(w: W) -> bool
            recommends false
        { true }

        struct X { }

        trait Tr<Key> {
            spec fn trait_fn(s: Seq<u8>) -> Option<Key>;
        }

        struct Implementor<T> { t: T }

        impl<S> Tr<S> for Implementor<S> {
            uninterp spec fn trait_fn(s: Seq<u8>) -> Option<S>;
        }

        trait SecondTrait<R, Kv: Tr<R>> {
            proof fn proof_trait_fn()
                ensures
                    forall|s: Seq<u8>|
                        #![trigger Kv::trait_fn(s)]
                    {
                        &&& Kv::trait_fn(s) matches Some(x)
                        &&& {
                            exists |w| bar(w)
                        }
                    };
        }

        struct Y<Z> { z: Z }

        impl<K> SecondTrait<K, Implementor<K>> for Y<K> {
            proof fn proof_trait_fn() {
                return; // FAILS
            }
        }
    } => Err(e) => {
        assert_one_fails(e);
    }
}

test_verify_one_file! {
    #[test] no_orphaned_tmp_vars_issue2435 verus_code! {
        use vstd::prelude::*;
        mod opaque_mod {
            use vstd::prelude::*;
            pub tracked struct Opaque<T> {
                t: T,
            }
            impl<T> Opaque<T> {
                pub closed spec fn view(self) -> T { self.t }
            }
        }
        use opaque_mod::Opaque;

        pub trait Tr<T> : Sized {
            proof fn f(s: Seq<Opaque<T>>, v: T)
                requires s[0]@ == v;
        }

        pub struct S<T>(core::marker::PhantomData<T>);

        impl<T> Tr<T> for S<T> {
            proof fn f(s: Seq<Opaque<T>>, v: T) {
                assert(false);  // FAILS
            }
        }

    } => Err(e) => {
        assert_one_fails(e);
    }
}

// https://github.com/verus-lang/verus/issues/408
// A `get_variant` accessor (here via `->`) is a total function, so it's not unsound to
// call it on a value that might not be the given variant, but it's a recommends-worthy
// mistake, so it should be flagged just like an explicit `recommends` clause would be.
test_verify_one_file! {
    #[test] get_variant_field_recommends_issue408 verus_code! {
        pub enum Foo {
            A(u32),
            B(bool),
        }

        proof fn test_ens(f: Foo)
            ensures f->A_0 == 10  // FAILS: nothing establishes f is the A variant
        {
        }
    } => Err(e) => assert_has_recommends_failure(e)
}

// Same as above, but via the named `get_A_0()` accessor rather than `->` - these compile
// to different call shapes (a synthesized #[verifier::inline] fn with its own
// `recommends` clause, vs. a raw field access), so both need their own coverage.
test_verify_one_file! {
    #[test] get_variant_field_method_call_recommends_issue408 verus_code! {
        #[is_variant]
        pub enum Foo {
            A(u32),
            B(bool),
        }

        proof fn test_ens(f: Foo)
            ensures f.get_A_0() == 10  // FAILS: nothing establishes f is the A variant
        {
        }
    } => Err(e) => assert_has_recommends_failure(e)
}
