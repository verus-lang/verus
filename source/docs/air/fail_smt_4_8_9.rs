// rust_verify --extern builtin=../rust/install/bin/libbuiltin.rlib --edition=2018 fail_smt_4_8_9.rs --verify-root
// succeeds with Z3 4.8.5
// fails with Z3 4.8.9, 4.8.14

#[allow(unused_imports)]
use builtin::*;

mod seq {
    #[allow(unused_imports)]
    use builtin::*;

    #[verifier(external_body)]
    pub struct Seq<A> {
        dummy: std::marker::PhantomData<A>,
    }

    #[spec]
    #[verifier(external_body)]
    pub fn seq_empty<A>() -> Seq<A> {
        unimplemented!()
    }

    impl<A> Seq<A> {
        #[spec]
        #[verifier(external_body)]
        pub fn len(self) -> nat {
            unimplemented!()
        }

        #[spec]
        #[verifier(external_body)]
        pub fn index(self, i: int) -> A {
            unimplemented!()
        }

        #[spec]
        #[verifier(external_body)]
        pub fn push(self, a: A) -> Seq<A> {
            unimplemented!()
        }
    }

    #[proof]
    #[verifier(external_body)]
    #[verifier(broadcast_forall)]
    pub fn axiom_seq_empty<A>() {
        ensures(#[trigger] seq_empty::<A>().len() == 0);
    }

    #[proof]
    #[verifier(external_body)]
    #[verifier(broadcast_forall)]
    pub fn axiom_seq_push_len<A>(s: Seq<A>, a: A) {
        ensures(#[trigger] s.push(a).len() == s.len() + 1);
    }

    #[proof]
    #[verifier(external_body)]
    #[verifier(broadcast_forall)]
    pub fn axiom_seq_push_index_same<A>(s: Seq<A>, a: A) {
        ensures(equal(#[trigger] s.push(a).index(s.len()), a));
    }

    #[proof]
    #[verifier(external_body)]
    #[verifier(broadcast_forall)]
    pub fn axiom_seq_push_index_different<A>(s: Seq<A>, a: A, i: int) {
        requires([
            0 <= i,
            i < s.len(),
        ]);
        ensures(equal(s.push(a).index(i), s.index(i)));
    }
}

#[allow(unused)]
use crate::seq::*;

#[proof]
fn sl(s: Seq<int>) {
    requires(equal(s, seq_empty().push(7)));
    ensures(s.index(0) == 7);
}

#[verifier(external)]
fn main() {
}
