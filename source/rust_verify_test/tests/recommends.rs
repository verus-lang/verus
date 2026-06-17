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
