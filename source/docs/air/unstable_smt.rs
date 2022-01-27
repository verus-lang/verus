// rust_verify --extern builtin=../rust/install/bin/libbuiltin.rlib --edition=2018 unstable_smt.rs --verify-root --smt-option smt.random_seed=7

extern crate builtin;
#[allow(unused_imports)]
use builtin::*;

mod pervasive {
    #[allow(unused_imports)]
    use builtin::*;
    #[proof]
    pub fn assume(b: bool) {
        ensures(b);

        admit();
    }

    #[proof]
    #[verifier(custom_req_err("assertion failure"))]
    pub fn assert(b: bool) {
        requires(b);
        ensures(b);
    }

    /// In spec, all types are inhabited
    #[spec]
    #[verifier(external_body)]
    #[allow(dead_code)]
    pub fn arbitrary<A>() -> A {
        unimplemented!()
    }
}

#[allow(unused_imports)]
use pervasive::*;

mod seq {
    #[allow(unused_imports)]
    use builtin::*;
    #[allow(unused_imports)]
    use crate::pervasive::*;

    /// sequence type for specifications
    #[verifier(external_body)]
    pub struct Seq<A> {
        dummy: std::marker::PhantomData<A>,
    }

    #[spec]
    #[verifier(pub_abstract)]
    pub fn seq_empty<A>() -> Seq<A> {
        arbitrary()
    }

    impl<A> Seq<A> {
        #[spec]
        #[verifier(pub_abstract)]
        pub fn len(self) -> nat {
            arbitrary()
        }

        #[spec]
        #[verifier(pub_abstract)]
        pub fn index(self, i: int) -> A {
            arbitrary()
        }

        #[spec]
        #[verifier(pub_abstract)]
        pub fn push(self, a: A) -> Seq<A> {
            arbitrary()
        }

        #[spec]
        #[verifier(pub_abstract)]
        pub fn add(self, rhs: Seq<A>) -> Seq<A> {
            arbitrary()
        }
    }

    // Trusted axioms

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
        ensures(0 <= i && i < s.len() >>= equal(s.push(a).index(i), s.index(i)));
    }

    #[proof]
    #[verifier(external_body)]
    #[verifier(broadcast_forall)]
    pub fn axiom_seq_add_len<A>(s1: Seq<A>, s2: Seq<A>) {
        ensures(#[trigger] s1.add(s2).len() == s1.len() + s2.len());
    }

    #[proof]
    #[verifier(external_body)]
    #[verifier(broadcast_forall)]
    pub fn axiom_seq_add_index1<A>(s1: Seq<A>, s2: Seq<A>, i: int) {
        ensures(0 <= i && i < s1.len() >>= equal(s1.add(s2).index(i), s1.index(i)));
    }

    #[proof]
    #[verifier(external_body)]
    #[verifier(broadcast_forall)]
    pub fn axiom_seq_add_index2<A>(s1: Seq<A>, s2: Seq<A>, i: int) {
        ensures(0 <= s1.len() && i < s1.len() as int + s2.len() >>= equal(s1.add(s2).index(i), s2.index(i - s1.len())));
    }
}

#[allow(unused_imports)]
use crate::seq::*;

mod M {
    extern crate builtin;
    #[allow(unused_imports)]
    use builtin::*;
    #[allow(unused_imports)]
    use crate::pervasive::*;
    #[allow(unused_imports)]
    use crate::seq::*;

    pub enum Tree {
        Nil,
        Node { value: u64, left: Box<Tree>, right: Box<Tree> }
    }

    #[spec]
    pub fn sequence_is_sorted(s: Seq<u64>) -> bool
    {
        forall(|i: nat, j: nat| i <= j && j < s.len() >>= s.index(i) <= s.index(j))
    }

    #[spec]
    pub fn tree_as_sequence(tree: Tree) -> Seq<u64>
    {
        decreases(tree);
        match tree {
            Tree::Nil => seq_empty(),
            Tree::Node { value, left, right } =>
                tree_as_sequence(*left).add(seq_empty().push(value)).add(tree_as_sequence(*right))
        }
    }
}

use M::*;

fn unstable(min: u64, tree: Tree, max: u64) {
    decreases(tree);
    ensures({
        #[spec] let s = tree_as_sequence(tree);
        forall(|i: nat| i < s.len() >>= min <= s.index(i) && s.index(i) <= max) &&
        sequence_is_sorted(tree_as_sequence(tree))
    });

    match tree {
        Tree::Nil => {},
        Tree::Node { value, left, right } => {
            #[spec] let s = tree_as_sequence(tree);
            unstable(min, *left, value);
            unstable(value, *right, max);
            assume(min <= value);
            assume(value <= max);
            assert(forall(|i: nat| i < s.len() >>= min <= s.index(i) && s.index(i) <= max));
            assume(false);
        }
    }
}

#[verifier(external)]
fn main() {
}
