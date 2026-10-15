//! Checked optional ownership, with the guide's remove/add sequence.
//! Generated option strategy coverage is a separate integration milestone.
use vstd::prelude::*;
use vstd::resource::agree::AgreementRA;
use vstd::resource::algebra::ResourceAlgebra;
use vstd::resource::exclusive::ExclusiveRA;
use vstd::resource::product::ProductRA;
use vstd::resource::tsm::*;
use vstd::resource::tsm_collections::*;

verus! {

type Fragment = ProductRA<Option<ExclusiveRA<bool>>, OptionFragment<int>>;

pub struct Optional;

impl Machine for Optional {
    type State = (bool, Option<int>);

    type Fragment = Fragment;

    open spec fn invariant(state: Self::State) -> bool {
        state.0 == (state.1 is Some)
    }

    open spec fn embed(state: Self::State) -> Fragment {
        ProductRA { left: Some(ExclusiveRA::Exclusive(state.0)), right: option_frag(state.1) }
    }
}

proof fn exclusive_option_sequence() {
    let tracked token = Token::<Optional>::alloc_state((true, Some(5int)));
    let old = token.fragment();
    let removed = Fragment { left: Some(ExclusiveRA::Exclusive(false)), right: None };
    assert(frame_update::<Optional>(old, removed)) by {
        assert forall|frame: Fragment, state: (bool, Option<int>)|
            Optional::invariant(state) && Fragment::op(old, frame) == Optional::embed(
                state,
            ) implies exists|post: (bool, Option<int>)|
            Optional::invariant(post) && Fragment::op(removed, frame) == Optional::embed(post) by {
            option_remove_frame(old.right, frame.right, state.1, 5int);
            let post = (false, None::<int>);
            assert(Fragment::op(removed, frame) == Optional::embed(post));
        };
    };
    let tracked token = token.update(removed);
    assert(token.fragment().left == Some(ExclusiveRA::Exclusive(false)));
    assert(token.fragment().right is None);
    let old = token.fragment();
    let added = Fragment {
        left: Some(ExclusiveRA::Exclusive(true)),
        right: option_frag(Some(19int)),
    };
    assert(frame_update::<Optional>(old, added)) by {
        assert forall|frame: Fragment, state: (bool, Option<int>)|
            Optional::invariant(state) && Fragment::op(old, frame) == Optional::embed(
                state,
            ) implies exists|post: (bool, Option<int>)|
            Optional::invariant(post) && Fragment::op(added, frame) == Optional::embed(post) by {
            assert(!state.0);
            assert(state.1 is None);
            option_add_frame(old.right, frame.right, state.1, 19int);
            let post = (true, Some(19int));
            assert(Fragment::op(added, frame) == Optional::embed(post));
        };
    };
    let tracked token = token.update(added);
    assert(token.fragment().right == Some(ExclusiveRA::Exclusive(19)));
    token.validate();
}

pub struct PersistentOptional;

impl Machine for PersistentOptional {
    type State = Option<int>;

    type Fragment = PersistentOptionFragment<int>;

    open spec fn invariant(state: Option<int>) -> bool {
        true
    }

    open spec fn embed(state: Option<int>) -> Self::Fragment {
        persistent_option_frag(state)
    }
}

proof fn persistent_option_retains_copy() {
    let tracked token = Token::<PersistentOptional>::alloc_state(Some(4int));
    persistent_option_idempotent(Some(4int));
    let tracked copy = token.duplicate();
    let old = token.fragment();
    let new = Some(AgreementRA::Agree(4int));
    assert(frame_update::<PersistentOptional>(old, new)) by {
        assert forall|frame: PersistentOptionFragment<int>, state: Option<int>|
            PersistentOptional::invariant(state) && PersistentOptionFragment::op(old, frame)
                == PersistentOptional::embed(state) implies exists|post: Option<int>|
            PersistentOptional::invariant(post) && PersistentOptionFragment::op(new, frame)
                == PersistentOptional::embed(post) by {
            persistent_option_owned_frame(old, frame, state, 4int);
            persistent_option_insert_frame(old, frame, state, 4int);
            assert(PersistentOptionFragment::op(new, frame) == PersistentOptional::embed(
                Some(4int),
            ));
        };
    };
    let tracked token = token.update(new);
    assert(copy.fragment() == Some(AgreementRA::Agree(4)));
    let tracked both = token.join(copy);
    both.validate();
}

proof fn generic_optional_fragments<T>(value: T) {
    option_join(None, Some(value));
    option_owned_frame(option_frag(Some(value)), None, Some(value), value);
    option_add_frame(None, None, None, value);
    persistent_option_insert_frame(None, None, None, value);
    persistent_option_owned_frame(
        PersistentOptionFragment::op(None, persistent_option_frag(Some(value))),
        None,
        Some(value),
        value,
    );
}

fn main() {
}

} // verus!
