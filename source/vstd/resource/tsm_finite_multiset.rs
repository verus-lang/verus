//! Finite multiset PCM, permitting recursive permission values.
//!
//! Unlike a function from values to counts, a finite multiset contains its
//! value type only positively. This matters for recursive Rc clients.
use super::super::prelude::*;
use super::super::multiset::Multiset;
use super::algebra::ResourceAlgebra;
use super::pcm::PCM;
use super::tsm::CountRA;

verus! {
broadcast use super::super::multiset::group_multiset_axioms;

#[verifier::accept_recursive_types(V)]
pub struct FiniteMultisetRA<V> {
    pub values: Multiset<V>,
}

impl<V> FiniteMultisetRA<V> {
    pub open spec fn at(self, value: V) -> CountRA {
        CountRA { count: self.values.count(value) }
    }

    pub open spec fn insert(self, value: V) -> Self {
        Self { values: self.values.insert(value) }
    }

    pub open spec fn remove(self, value: V) -> Self {
        Self { values: self.values.remove(value) }
    }

    pub proof fn extensionality(left: Self, right: Self)
        requires
            forall|value: V| #[trigger] left.at(value) == right.at(value),
        ensures
            left == right,
    {
        assert forall|value: V|
            #[trigger] left.values.count(value) == right.values.count(value) by {
            assert(left.at(value) == right.at(value));
        };
        assert(left.values =~= right.values);
    }
}

impl<V> ResourceAlgebra for FiniteMultisetRA<V> {
    open spec fn valid(self) -> bool { true }

    open spec fn op(left: Self, right: Self) -> Self {
        Self { values: left.values.add(right.values) }
    }

    proof fn associative(a: Self, b: Self, c: Self) {
        let left = Self::op(a, Self::op(b, c));
        let right = Self::op(Self::op(a, b), c);
        assert forall|value: V| #[trigger] left.at(value) == right.at(value) by {};
        Self::extensionality(left, right);
    }

    proof fn commutative(a: Self, b: Self) {
        let left = Self::op(a, b);
        let right = Self::op(b, a);
        assert forall|value: V| #[trigger] left.at(value) == right.at(value) by {};
        Self::extensionality(left, right);
    }

    proof fn valid_op(a: Self, b: Self) {}
}

impl<V> PCM for FiniteMultisetRA<V> {
    open spec fn unit() -> Self { Self { values: Multiset::empty() } }

    proof fn op_unit(self) {
        let combined = Self::op(self, Self::unit());
        assert forall|value: V| #[trigger] combined.at(value) == self.at(value) by {};
        Self::extensionality(combined, self);
    }

    proof fn unit_valid() {}
}

pub open spec fn finite_multiset_frag<V>(values: Multiset<V>) -> FiniteMultisetRA<V> {
    FiniteMultisetRA { values }
}

pub proof fn finite_multiset_join<V>(left: Multiset<V>, right: Multiset<V>)
    ensures
        FiniteMultisetRA::op(finite_multiset_frag(left), finite_multiset_frag(right))
            == finite_multiset_frag(left.add(right)),
{
}

pub proof fn finite_multiset_owned_frame<V>(
    owned: FiniteMultisetRA<V>,
    frame: FiniteMultisetRA<V>,
    whole: Multiset<V>,
    value: V,
)
    requires
        FiniteMultisetRA::op(owned, frame) == finite_multiset_frag(whole),
    ensures
        whole.count(value) == owned.at(value).count + frame.at(value).count,
{
}

/// A completed fragment owns no more than the full state's multiplicities.
pub proof fn finite_multiset_owned_subset<V>(
    owned: FiniteMultisetRA<V>,
    frame: FiniteMultisetRA<V>,
    whole: Multiset<V>,
)
    requires
        FiniteMultisetRA::op(owned, frame) == finite_multiset_frag(whole),
    ensures
        owned.values.subset_of(whole),
{
    assert forall|value: V| #[trigger] whole.count(value) >= owned.values.count(value) by {
        finite_multiset_owned_frame(owned, frame, whole, value);
    };
}

pub proof fn finite_multiset_add_frame<V>(
    owned: FiniteMultisetRA<V>,
    frame: FiniteMultisetRA<V>,
    whole: Multiset<V>,
    value: V,
)
    requires
        FiniteMultisetRA::op(owned, frame) == finite_multiset_frag(whole),
    ensures
        FiniteMultisetRA::op(owned.insert(value), frame)
            == finite_multiset_frag(whole.insert(value)),
{
    let combined = FiniteMultisetRA::op(owned.insert(value), frame);
    let updated = finite_multiset_frag(whole.insert(value));
    assert forall|other: V| #[trigger] combined.at(other) == updated.at(other) by {
        finite_multiset_owned_frame(owned, frame, whole, other);
    };
    FiniteMultisetRA::extensionality(combined, updated);
}

pub proof fn finite_multiset_remove_frame<V>(
    owned: FiniteMultisetRA<V>,
    frame: FiniteMultisetRA<V>,
    whole: Multiset<V>,
    value: V,
)
    requires
        FiniteMultisetRA::op(owned, frame) == finite_multiset_frag(whole),
        owned.at(value).count >= 1,
    ensures
        FiniteMultisetRA::op(owned.remove(value), frame)
            == finite_multiset_frag(whole.remove(value)),
{
    let combined = FiniteMultisetRA::op(owned.remove(value), frame);
    let updated = finite_multiset_frag(whole.remove(value));
    assert forall|other: V| #[trigger] combined.at(other) == updated.at(other) by {
        finite_multiset_owned_frame(owned, frame, whole, other);
    };
    FiniteMultisetRA::extensionality(combined, updated);
}

pub proof fn finite_multiset_add_many_frame<V>(
    owned: FiniteMultisetRA<V>,
    frame: FiniteMultisetRA<V>,
    whole: Multiset<V>,
    added: Multiset<V>,
)
    requires
        FiniteMultisetRA::op(owned, frame) == finite_multiset_frag(whole),
    ensures
        FiniteMultisetRA::op(finite_multiset_frag(owned.values.add(added)), frame)
            == finite_multiset_frag(whole.add(added)),
{
    let combined = FiniteMultisetRA::op(finite_multiset_frag(owned.values.add(added)), frame);
    let updated = finite_multiset_frag(whole.add(added));
    assert forall|value: V| #[trigger] combined.at(value) == updated.at(value) by {
        finite_multiset_owned_frame(owned, frame, whole, value);
    };
    FiniteMultisetRA::extensionality(combined, updated);
}

/// Subtraction never consumes multiplicity owned by the untouched frame.
pub proof fn finite_multiset_remove_many_frame<V>(
    owned: FiniteMultisetRA<V>,
    frame: FiniteMultisetRA<V>,
    whole: Multiset<V>,
    removed: Multiset<V>,
)
    requires
        FiniteMultisetRA::op(owned, frame) == finite_multiset_frag(whole),
        removed.subset_of(owned.values),
    ensures
        removed.subset_of(whole),
        FiniteMultisetRA::op(finite_multiset_frag(owned.values.sub(removed)), frame)
            == finite_multiset_frag(whole.sub(removed)),
{
    let combined = FiniteMultisetRA::op(finite_multiset_frag(owned.values.sub(removed)), frame);
    let updated = finite_multiset_frag(whole.sub(removed));
    assert forall|value: V| #[trigger] combined.at(value) == updated.at(value) by {
        finite_multiset_owned_frame(owned, frame, whole, value);
        assert(removed.count(value) <= owned.values.count(value));
    };
    assert forall|value: V| #[trigger] removed.count(value) <= whole.count(value) by {
        finite_multiset_owned_frame(owned, frame, whole, value);
    };
    FiniteMultisetRA::extensionality(combined, updated);
}
}
