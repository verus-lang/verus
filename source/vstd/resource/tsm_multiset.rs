//! Checked frame lemmas for multiset fragments used by generated protocols.
use super::super::prelude::*;
use super::super::multiset::Multiset;
use super::algebra::ResourceAlgebra;
use super::tsm::CountRA;
use super::tsm_collections::*;

verus! {

broadcast use {
    super::super::multiset::group_multiset_axioms,
    super::tsm_collections::group_tsm_fragment_lemmas,
};

pub proof fn multiset_join<V>(left: Multiset<V>, right: Multiset<V>)
    ensures
        MultisetFragment::op(multiset_frag(left), multiset_frag(right))
            == multiset_frag(left.add(right)),
{
    let combined = MultisetFragment::op(multiset_frag(left), multiset_frag(right));
    let whole = multiset_frag(left.add(right));
    assert forall|value: V| #[trigger] combined.at(value) == whole.at(value) by {};
    Pointwise::extensionality(combined, whole);
}

pub proof fn multiset_owned_frame<V>(
    owned: MultisetFragment<V>,
    frame: MultisetFragment<V>,
    whole: Multiset<V>,
    value: V,
)
    requires
        MultisetFragment::op(owned, frame) == multiset_frag(whole),
    ensures
        whole.count(value) == owned.at(value).count + frame.at(value).count,
{
    assert(MultisetFragment::op(owned, frame).at(value) == multiset_frag(whole).at(value));
}

pub proof fn multiset_add_frame<V>(
    owned: MultisetFragment<V>,
    frame: MultisetFragment<V>,
    whole: Multiset<V>,
    value: V,
)
    requires
        MultisetFragment::op(owned, frame) == multiset_frag(whole),
    ensures
        MultisetFragment::op(
            replace_at(owned, value, CountRA { count: owned.at(value).count + 1 }),
            frame,
        ) == multiset_frag(whole.insert(value)),
{
    let new_owned = replace_at(owned, value, CountRA { count: owned.at(value).count + 1 });
    let combined = MultisetFragment::op(new_owned, frame);
    let updated_whole = multiset_frag(whole.insert(value));
    assert forall|other: V| #[trigger] combined.at(other) == updated_whole.at(other) by {
        multiset_owned_frame(owned, frame, whole, other);
    };
    Pointwise::extensionality(combined, updated_whole);
}

/// Subtraction must be justified by ownership, not merely by the full state's
/// count: a reader in another owner's frame cannot be consumed.
pub proof fn multiset_remove_frame<V>(
    owned: MultisetFragment<V>,
    frame: MultisetFragment<V>,
    whole: Multiset<V>,
    value: V,
)
    requires
        MultisetFragment::op(owned, frame) == multiset_frag(whole),
        owned.at(value).count >= 1,
    ensures
        MultisetFragment::op(
            replace_at(owned, value, CountRA { count: (owned.at(value).count - 1) as nat }),
            frame,
        ) == multiset_frag(whole.remove(value)),
{
    let new_owned = replace_at(owned, value, CountRA { count: (owned.at(value).count - 1) as nat });
    let combined = MultisetFragment::op(new_owned, frame);
    let updated_whole = multiset_frag(whole.remove(value));
    assert forall|other: V| #[trigger] combined.at(other) == updated_whole.at(other) by {
        multiset_owned_frame(owned, frame, whole, other);
    };
    Pointwise::extensionality(combined, updated_whole);
}

}
