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

// Same as above, but via the named `get_A_0()` accessor rather than `->`.
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

// https://github.com/verus-lang/verus/issues/912
// `h`'s recommends (m == 41) is genuinely met here (f(42) == 41), so recommends checking
// shouldn't complain about it, regardless of whether f(n) is passed to h directly or via
// a `let` binding first.
test_verify_one_file! {
    #[test] let_bound_call_recommends_completeness_issue912 verus_code! {
        spec fn f(n: int) -> int
            recommends n > 0,
        {
            n - 1
        }

        spec fn h(m: int) -> int
            recommends m == 41,
        {
            m + 1
        }

        proof fn test_let(n: int)
            requires n == 42,
            ensures ({
                let x = f(n);
                h(x) == 999  // FAILS: genuinely false, but h's recommends is met
            }),
        {
        }
    } => Err(e) => {
        assert_eq!(e.errors.len(), 1);
        assert!(e.notes.iter().all(|n| !n.message.contains("recommendation not met")));
    }
}

// https://github.com/verus-lang/verus/issues/1060 - same root cause as #912.
// `spec_affirm`'s equality trivially follows from the `let`, but recommends-checking
// lost the link and spuriously warned about `discard_old`'s own recommends instead.
test_verify_one_file! {
    #[test] let_bound_spec_call_recommends_issue1060 verus_code! {
        use vstd::prelude::*;

        spec(checked) fn discard_old(x: int, y: int) -> int
            recommends y <= x,
        {
            x - y
        }

        spec(checked) fn foo(x: int, y: int) -> int
            recommends y <= x,
        {
            let remaining = discard_old(x, y);
            let _ = spec_affirm(remaining == discard_old(x, y));
            remaining
        }
    } => Ok(())
}

// https://github.com/verus-lang/verus/issues/692 - same root cause as #912.
// A fact established by a `recommends_by` lemma about a `let`-bound call's result
// couldn't reach a later recommends check that used the bound variable.
test_verify_one_file! {
    #[test] recommends_by_fact_flows_through_let_bound_call_issue692 verus_code! {
        pub uninterp spec fn route(len: nat) -> nat
            recommends len > 0,
        ;

        proof fn route_lemma(len: nat)
            requires len > 0,
            ensures route(len) < len,
        {
            admit();
        }

        pub closed spec fn get(len: nat, i: nat) -> nat
            recommends i < len,
        {
            i
        }

        pub struct Node { pub len: nat }

        impl Node {
            #[verifier(recommends_by)]
            proof fn flushed_ofs_inline_lemma(&self)
            {
                route_lemma(self.len);
                assert(0 <= route(self.len) < self.len);
            }

            pub open spec(checked) fn flushed_ofs(&self) -> nat
                recommends
                    self.len > 0,
            {
                recommends_by(Self::flushed_ofs_inline_lemma);
                let r = route(self.len);
                get(self.len, r)
            }
        }
    } => Ok(())
}
