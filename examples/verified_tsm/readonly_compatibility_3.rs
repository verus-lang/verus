//! Three shared references have one common completion, even when they alias.
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
    let (state, first_frame, second_frame, third_frame) = token.compatible_3(&token, &token);
    assert(state);
    assert(first_frame.count == 0 && second_frame.count == 0 && third_frame.count == 0);
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
    let (state, first_frame, second_frame, third_frame) = token.compatible_3(&token, &token);
    assert(state);
    assert(first_frame.count == 0 && second_frame.count == 0 && third_frame.count == 0);
}

pub type TripleFragment = ProductRA<
    Option<ExclusiveRA<bool>>,
    ProductRA<Option<ExclusiveRA<bool>>, Option<ExclusiveRA<bool>>>,
>;

pub struct Triple;

impl Machine for Triple {
    type Fragment = TripleFragment;

    type State = (bool, bool, bool);

    // Any two false observations admit a completion; all three false ones do not.
    open spec fn invariant(state: Self::State) -> bool {
        state.0 || state.1 || state.2
    }

    open spec fn embed(state: Self::State) -> TripleFragment {
        ProductRA {
            left: Some(ExclusiveRA::Exclusive(state.0)),
            right: ProductRA {
                left: Some(ExclusiveRA::Exclusive(state.1)),
                right: Some(ExclusiveRA::Exclusive(state.2)),
            },
        }
    }
}

impl StorageMachine for Triple {
    type Key = int;

    type Value = bool;

    open spec fn storage(state: Self::State) -> IMap<int, bool> {
        IMap::empty()
    }
}

pub open spec fn first(value: bool) -> TripleFragment {
    ProductRA {
        left: Some(ExclusiveRA::Exclusive(value)),
        right: ProductRA { left: None, right: None },
    }
}

pub open spec fn second(value: bool) -> TripleFragment {
    ProductRA {
        left: None,
        right: ProductRA { left: Some(ExclusiveRA::Exclusive(value)), right: None },
    }
}

pub open spec fn third(value: bool) -> TripleFragment {
    ProductRA {
        left: None,
        right: ProductRA { left: None, right: Some(ExclusiveRA::Exclusive(value)) },
    }
}

proof fn observe_pcm(
    tracked a: &Token<Triple>,
    tracked b: &Token<Triple>,
    tracked c: &Token<Triple>,
)
    requires
        a.loc() == b.loc(),
        a.loc() == c.loc(),
        a.fragment() == first(a.fragment().left->Some_0->Exclusive_0),
        b.fragment() == second(b.fragment().right.left->Some_0->Exclusive_0),
        c.fragment() == third(c.fragment().right.right->Some_0->Exclusive_0),
    ensures
        a.fragment().left->Some_0->Exclusive_0 || b.fragment().right.left->Some_0->Exclusive_0
            || c.fragment().right.right->Some_0->Exclusive_0,
{
    let fact = a.fragment().left->Some_0->Exclusive_0
        || b.fragment().right.left->Some_0->Exclusive_0
        || c.fragment().right.right->Some_0->Exclusive_0;
    assert forall|
        af: TripleFragment,
        bf: TripleFragment,
        cf: TripleFragment,
        state: (bool, bool, bool),
    |
        Triple::invariant(state) && TripleFragment::op(a.fragment(), af) == Triple::embed(state)
            && TripleFragment::op(b.fragment(), bf) == Triple::embed(state) && TripleFragment::op(
            c.fragment(),
            cf,
        ) == Triple::embed(state) implies fact by {
        assert(a.fragment().left->Some_0->Exclusive_0 == state.0);
        assert(b.fragment().right.left->Some_0->Exclusive_0 == state.1);
        assert(c.fragment().right.right->Some_0->Exclusive_0 == state.2);
    };
    a.facts_3(b, c, fact);
}

proof fn observe_storage(
    tracked a: &StorageToken<Triple>,
    tracked b: &StorageToken<Triple>,
    tracked c: &StorageToken<Triple>,
)
    requires
        a.loc() == b.loc(),
        a.loc() == c.loc(),
        a.fragment() == first(a.fragment().left->Some_0->Exclusive_0),
        b.fragment() == second(b.fragment().right.left->Some_0->Exclusive_0),
        c.fragment() == third(c.fragment().right.right->Some_0->Exclusive_0),
    ensures
        a.fragment().left->Some_0->Exclusive_0 || b.fragment().right.left->Some_0->Exclusive_0
            || c.fragment().right.right->Some_0->Exclusive_0,
{
    let fact = a.fragment().left->Some_0->Exclusive_0
        || b.fragment().right.left->Some_0->Exclusive_0
        || c.fragment().right.right->Some_0->Exclusive_0;
    assert forall|
        af: TripleFragment,
        bf: TripleFragment,
        cf: TripleFragment,
        state: (bool, bool, bool),
    |
        Triple::invariant(state) && TripleFragment::op(a.fragment(), af) == Triple::embed(state)
            && TripleFragment::op(b.fragment(), bf) == Triple::embed(state) && TripleFragment::op(
            c.fragment(),
            cf,
        ) == Triple::embed(state) implies fact by {
        assert(a.fragment().left->Some_0->Exclusive_0 == state.0);
        assert(b.fragment().right.left->Some_0->Exclusive_0 == state.1);
        assert(c.fragment().right.right->Some_0->Exclusive_0 == state.2);
    };
    a.facts_3(b, c, fact);
}

proof fn distinct_references() {
    let tracked all = Token::<Triple>::alloc_state((true, false, false));
    let tracked (a, bc) = all.split(first(true), TripleFragment::op(second(false), third(false)));
    let tracked (b, c) = bc.split(second(false), third(false));
    observe_pcm(&a, &b, &c);
    let tracked all = StorageToken::<Triple>::alloc_state(
        (false, true, false),
        IMap::tracked_empty(),
    );
    let tracked (a, bc) = all.split(first(false), TripleFragment::op(second(true), third(false)));
    let tracked (b, c) = bc.split(second(true), third(false));
    observe_storage(&a, &b, &c);
}

fn main() {
    proof {
        same_reference_pcm();
        same_reference_storage();
        distinct_references();
    }
}

} // verus!
