//! Read-only compatibility handles both aliased and distinct references.
use vstd::prelude::*;
use vstd::resource::algebra::ResourceAlgebra;
use vstd::resource::exclusive::ExclusiveRA;
use vstd::resource::product::ProductRA;
use vstd::resource::tsm::*;
use vstd::resource::tsm_bool::bool_frag;
use vstd::resource::tsm_storage::*;

verus! {

pub struct Boolean;

impl Machine for Boolean {
    type Fragment = CountRA;

    type State = bool;

    open spec fn invariant(state: bool) -> bool {
        true
    }

    open spec fn embed(state: bool) -> CountRA {
        bool_frag(state)
    }
}

impl StorageMachine for Boolean {
    type Key = int;

    type Value = bool;

    open spec fn storage(state: bool) -> IMap<int, bool> {
        IMap::empty()
    }
}

proof fn same_reference_pcm() {
    let tracked token = Token::<Boolean>::alloc_state(true);
    let (state, left_frame, right_frame) = token.compatible_with(&token);
    assert(state);
    assert(left_frame.count == 0 && right_frame.count == 0);
    // The overlapping references have a common completion, although their
    // separating composition would contain two exclusive boolean owners.
    assert(!completes::<Boolean>(CountRA::op(token.fragment(), token.fragment()))) by {
        assert forall|frame: CountRA, full: bool|
            !(Boolean::invariant(full) && CountRA::op(
                CountRA::op(token.fragment(), token.fragment()),
                frame,
            ) == Boolean::embed(full)) by {};
    }
}

proof fn same_reference_storage() {
    let tracked token = StorageToken::<Boolean>::alloc_state(true, IMap::tracked_empty());
    let (state, left_frame, right_frame) = token.compatible_with(&token);
    assert(state);
    assert(left_frame.count == 0 && right_frame.count == 0);
    assert(!completes::<Boolean>(CountRA::op(token.fragment(), token.fragment()))) by {
        assert forall|frame: CountRA, full: bool|
            !(Boolean::invariant(full) && CountRA::op(
                CountRA::op(token.fragment(), token.fragment()),
                frame,
            ) == Boolean::embed(full)) by {};
    }
}

pub type PairFragment = ProductRA<Option<ExclusiveRA<bool>>, Option<ExclusiveRA<bool>>>;

pub struct Pair;

impl Machine for Pair {
    type Fragment = PairFragment;

    type State = (bool, bool);

    open spec fn invariant(state: Self::State) -> bool {
        state.0 == state.1
    }

    open spec fn embed(state: Self::State) -> PairFragment {
        ProductRA {
            left: Some(ExclusiveRA::Exclusive(state.0)),
            right: Some(ExclusiveRA::Exclusive(state.1)),
        }
    }
}

impl StorageMachine for Pair {
    type Key = int;

    type Value = bool;

    open spec fn storage(state: Self::State) -> IMap<int, bool> {
        IMap::empty()
    }
}

pub open spec fn left_fragment(value: bool) -> PairFragment {
    ProductRA { left: Some(ExclusiveRA::Exclusive(value)), right: None }
}

pub open spec fn right_fragment(value: bool) -> PairFragment {
    ProductRA { left: None, right: Some(ExclusiveRA::Exclusive(value)) }
}

proof fn compare_pcm(tracked left: &Token<Pair>, tracked right: &Token<Pair>)
    requires
        left.loc() == right.loc(),
        left.fragment().left is Some && left.fragment().left->Some_0 is Exclusive,
        right.fragment().right is Some && right.fragment().right->Some_0 is Exclusive,
    ensures
        left.fragment().left->Some_0->Exclusive_0 == right.fragment().right->Some_0->Exclusive_0,
{
    let (state, left_frame, right_frame) = left.compatible_with(right);
    assert(left.fragment().left->Some_0->Exclusive_0 == state.0);
    assert(right.fragment().right->Some_0->Exclusive_0 == state.1);
}

proof fn compare_storage(tracked left: &StorageToken<Pair>, tracked right: &StorageToken<Pair>)
    requires
        left.loc() == right.loc(),
        left.fragment().left is Some && left.fragment().left->Some_0 is Exclusive,
        right.fragment().right is Some && right.fragment().right->Some_0 is Exclusive,
    ensures
        left.fragment().left->Some_0->Exclusive_0 == right.fragment().right->Some_0->Exclusive_0,
{
    let fact = left.fragment().left->Some_0->Exclusive_0
        == right.fragment().right->Some_0->Exclusive_0;
    assert forall|left_frame: PairFragment, right_frame: PairFragment, state: (bool, bool)|
        Pair::invariant(state) && PairFragment::op(left.fragment(), left_frame) == Pair::embed(
            state,
        ) && PairFragment::op(right.fragment(), right_frame) == Pair::embed(state) implies fact by {
        assert(left.fragment().left->Some_0->Exclusive_0 == state.0);
        assert(right.fragment().right->Some_0->Exclusive_0 == state.1);
    };
    left.facts_2(right, fact);
}

proof fn distinct_reference_pcm() {
    let tracked all = Token::<Pair>::alloc_state((true, true));
    let tracked (left, right) = all.split(left_fragment(true), right_fragment(true));
    compare_pcm(&left, &right);
}

proof fn distinct_reference_storage() {
    let tracked all = StorageToken::<Pair>::alloc_state((false, false), IMap::tracked_empty());
    let tracked (left, right) = all.split(left_fragment(false), right_fragment(false));
    compare_storage(&left, &right);
}

fn main() {
}

} // verus!
