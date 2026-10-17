//! Borrowed parts of a `multiset` field on the generic interface.
//!
//! A borrowed token collection (`have f >= (e)`) is observed token by token
//! through `MultisetToken::borrow`. Shared references to two tokens of one
//! element do not show that the tokens are distinct resources, so the joined
//! observation shows each element of `e` at least once, not its multiplicity.
//! The borrowed part `e` must therefore not contain an element twice. A
//! machine states this with a `require` (`spread` below); without one, the
//! generated operation reports the diagnostic
//! "the borrowed part of multiset field `..` must not contain an element twice"
//! at the `have` statement (see
//! `negative/generic_tokens_multiset_repeated_borrow.rs`).
//!
//! Separate singleton borrows (`have f >= {x}; have f >= {y}`) require each
//! element once (the model reads `count(x) >= 1` and `count(y) >= 1`), so
//! they need no such condition, also for `x == y`.
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::multiset::Multiset;
use vstd::prelude::*;
use vstd::tokens::*;

verified_tokenized_state_machine! {
    Bag {
        fields {
            #[sharding(variable)]
            pub bound: int,

            #[sharding(multiset)]
            pub items: Multiset<int>,
        }

        #[invariant]
        pub fn inv(&self) -> bool {
            forall|x: int| #[trigger] self.items.count(x) > 0 ==> x < self.bound
        }

        init!{
            initialize(bound: int) {
                init bound = bound;
                init items = Multiset::empty();
            }
        }

        transition!{
            put(x: int) {
                require(x < pre.bound);
                add items += { x };
            }
        }

        // A borrowed part without repeated elements: every element is below
        // the bound.
        property!{
            spread(e: Multiset<int>) {
                require(forall|x: int| #[trigger] e.count(x) <= 1);
                have items >= (e);
                assert(forall|x: int| #[trigger] e.count(x) > 0 ==> x < pre.bound) by {
                    broadcast use vstd::multiset::group_multiset_axioms;
                };
            }
        }

        // Two singleton borrows, possibly of one element.
        property!{
            pair(x: int, y: int) {
                have items >= { x };
                have items >= { y };
                assert(x < pre.bound && y < pre.bound) by {
                    broadcast use vstd::multiset::group_multiset_axioms;
                };
            }
        }

        #[inductive(initialize)]
        fn initialize_inductive(post: Self, bound: int) {
            broadcast use vstd::multiset::group_multiset_axioms;
        }

        #[inductive(put)]
        fn put_inductive(pre: Self, post: Self, x: int) {
            broadcast use vstd::multiset::group_multiset_axioms;
            assert forall|y: int| #[trigger] post.items.count(y) > 0 implies y < post.bound by {
                if y != x { assert(pre.items.count(y) > 0); }
            }
        }
    }
}

verus! {

proof fn client() {
    broadcast use vstd::multiset::group_multiset_axioms;
    let tracked (Tracked(inst), Tracked(bound), Tracked(items)) = Bag::Instance::initialize(10);
    let tracked a1 = inst.put(3, &bound);
    let tracked a2 = inst.put(3, &bound);
    let tracked b = inst.put(5, &bound);
    // Two tokens of the element 3.
    inst.pair(3, 3, &bound, &a1, &a2);
    let tracked mut all = items;
    all.insert(a1);
    all.insert(a2);
    all.insert(b);
    assert(all.multiset() =~= Multiset::empty().insert(3).insert(3).insert(5));
    let e = Multiset::empty().insert(3).insert(5);
    assert(e.subset_of(all.multiset()));
    assert(e.count(3) == 1 && e.count(5) == 1);
    assert forall|x: int| #[trigger] e.count(x) <= 1 by {
        if x != 3 && x != 5 { assert(e.count(x) == 0); }
    }
    inst.spread(e, &bound, &all);
    assert(e.count(5) > 0);
    assert(5 < bound.value());
}

}

fn main() {}
