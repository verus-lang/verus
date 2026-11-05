// Regression (de92adf43): a read-only operation that reads a constant and whose only
// borrowed inputs are imap/iset collections was rejected (the collections' observation
// did not join the constants' fragment).
//! Read-only operations that read a constant and whose only borrowed inputs
//! are `imap`/`iset` token collections.
//!
//! An operation reading a constant observes the constants' agreement
//! fragment `κ`. The observation of a borrowed `imap`/`iset` collection joins
//! the copies of `κ` held by its bulk token and its individual tokens, so a
//! non-empty observation includes `κ`; an empty one (nothing borrowed) reasons
//! about the instance's reachable state, which has the instance's constants.
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
use vstd::tokens::*;

verified_tokenized_state_machine! {
    Bounded {
        fields {
            #[sharding(constant)]
            pub bound: int,

            #[sharding(imap)]
            pub values: IMap<int, int>,

            #[sharding(iset)]
            pub marks: ISet<int>,
        }

        #[invariant]
        pub fn inv(&self) -> bool {
            &&& forall|k: int| #[trigger] self.values.contains_key(k) ==> self.values[k] < self.bound
            &&& forall|k: int| #[trigger] self.marks.contains(k) ==> k < self.bound
        }

        init!{
            initialize(bound: int) {
                init bound = bound;
                // Every key below the bound holds `bound - 1`.
                init values = IMap::new(|k: int| k < bound, |k: int| bound - 1);
                init marks = ISet::new(|k: int| k < bound);
            }
        }

        // Reads the constant; borrows only an `imap` collection.
        property!{
            below(m: IMap<int, int>) {
                have values >= (m);
                assert(forall|k: int| m.contains_key(k) ==> #[trigger] m[k] < pre.bound) by {
                    assert forall|k: int| m.contains_key(k) implies #[trigger] m[k] < pre.bound by {
                        assert(pre.values.contains_key(k));
                    }
                };
            }
        }

        // Reads the constant; borrows only an `iset` collection.
        property!{
            marked_below(s: ISet<int>) {
                have marks >= (s);
                assert(forall|k: int| #[trigger] s.contains(k) ==> k < pre.bound);
            }
        }

        #[inductive(initialize)]
        fn initialize_inductive(post: Self, bound: int) { }
    }
}

verus! {

proof fn client() {
    let tracked (Tracked(inst), Tracked(values), Tracked(marks)) = Bounded::Instance::initialize(10);
    assert(inst.bound() == 10);
    // An infinite borrowed part.
    let all = IMap::new(|k: int| k < 10, |k: int| 9int);
    assert(all =~= values.map());
    inst.below(all, &values);
    // A finite one, split off as an individual token.
    let tracked mut values = values;
    let tracked v3 = values.remove(3);
    assert(v3.key() == 3 && v3.value() == 9);
    let tracked mut part = Bounded::values_map::empty(inst.id());
    part.insert(v3);
    let one = IMap::<int, int>::empty().insert(3, 9);
    assert(part.map() =~= one);
    inst.below(one, &part);
    // An empty one.
    inst.below(IMap::empty(), &part);
    let s = ISet::new(|k: int| k < 10);
    assert(s =~= marks.set());
    inst.marked_below(s, &marks);
    assert(s.contains(-5));
}

}

fn main() {}
