//! Bulk multiset changes retain the untouched owner's overlapping counts.
use vstd::multiset::Multiset;
use vstd::prelude::*;
use vstd::resource::algebra::ResourceAlgebra;
use vstd::resource::tsm::*;
use vstd::resource::tsm_finite_multiset::*;

verus! {

broadcast use vstd::multiset::group_multiset_axioms;

pub struct Bag;

impl Machine for Bag {
    type State = Multiset<int>;

    type Fragment = FiniteMultisetRA<int>;

    open spec fn invariant(state: Self::State) -> bool {
        true
    }

    open spec fn embed(state: Self::State) -> Self::Fragment {
        finite_multiset_frag(state)
    }
}

proof fn bulk_changes_preserve_overlapping_owner() {
    let local = Multiset::empty().insert(4int).insert(4int).insert(5int);
    let rest = Multiset::empty().insert(4int).insert(6int);
    let tracked all = Token::<Bag>::alloc_state(local.add(rest));
    finite_multiset_join(local, rest);
    let tracked (owner, untouched) = all.split(
        finite_multiset_frag(local),
        finite_multiset_frag(rest),
    );
    let before = owner.fragment();
    let removed = Multiset::empty().insert(4int).insert(5int);
    let after = finite_multiset_frag(before.values.sub(removed));
    assert(frame_update::<Bag>(before, after)) by {
        assert forall|frame: FiniteMultisetRA<int>, state: Multiset<int>|
            Bag::invariant(state) && FiniteMultisetRA::op(before, frame) == Bag::embed(
                state,
            ) implies exists|post: Multiset<int>|
            Bag::invariant(post) && FiniteMultisetRA::op(after, frame) == Bag::embed(post) by {
            finite_multiset_remove_many_frame(before, frame, state, removed);
            assert(FiniteMultisetRA::op(after, frame) == Bag::embed(state.sub(removed)));
        };
    };
    let tracked owner = owner.update(after);
    assert(owner.fragment().at(4).count == 1);
    assert(owner.fragment().at(5).count == 0);
    assert(untouched.fragment().at(4).count == 1);
    let before = owner.fragment();
    let added = Multiset::empty().insert(5int).insert(5int);
    let after = finite_multiset_frag(before.values.add(added));
    assert(frame_update::<Bag>(before, after)) by {
        assert forall|frame: FiniteMultisetRA<int>, state: Multiset<int>|
            Bag::invariant(state) && FiniteMultisetRA::op(before, frame) == Bag::embed(
                state,
            ) implies exists|post: Multiset<int>|
            Bag::invariant(post) && FiniteMultisetRA::op(after, frame) == Bag::embed(post) by {
            finite_multiset_add_many_frame(before, frame, state, added);
            assert(FiniteMultisetRA::op(after, frame) == Bag::embed(state.add(added)));
        };
    };
    let tracked owner = owner.update(after);
    assert(owner.fragment().at(5).count == 2);
    assert(untouched.fragment().at(6).count == 1);
    let tracked combined = owner.join(untouched);
    combined.validate();
    assert(combined.fragment().at(4).count == 2);
    assert(combined.fragment().at(5).count == 2);
}

fn main() {
}

} // verus!
