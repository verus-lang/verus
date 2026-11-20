//! Provides specifications for spec closures as relations.
#[allow(unused_imports)]
use super::pervasive::*;
#[allow(unused_imports)]
use super::prelude::*;
#[allow(unused_imports)]
use super::seq::*;

verus! {

pub open spec fn injective<X, Y>(r: spec_fn(X) -> Y) -> bool {
    forall|x1: X, x2: X| #[trigger] r(x1) == #[trigger] r(x2) ==> x1 == x2
}

pub open spec fn commutative<T, U>(r: spec_fn(T, T) -> U) -> bool {
    forall|x: T, y: T| #[trigger] r(x, y) == #[trigger] r(y, x)
}

pub open spec fn associative<T>(r: spec_fn(T, T) -> T) -> bool {
    forall|x: T, y: T, z: T| #[trigger] r(x, r(y, z)) == #[trigger] r(r(x, y), z)
}

pub open spec fn reflexive<T>(r: spec_fn(T, T) -> bool) -> bool {
    forall|x: T| #[trigger] r(x, x)
}

pub open spec fn irreflexive<T>(r: spec_fn(T, T) -> bool) -> bool {
    forall|x: T| #[trigger] r(x, x) == false
}

pub open spec fn antisymmetric<T>(r: spec_fn(T, T) -> bool) -> bool {
    forall|x: T, y: T| #[trigger] r(x, y) && #[trigger] r(y, x) ==> x == y
}

pub open spec fn asymmetric<T>(r: spec_fn(T, T) -> bool) -> bool {
    forall|x: T, y: T| #[trigger] r(x, y) ==> #[trigger] r(y, x) == false
}

pub open spec fn symmetric<T>(r: spec_fn(T, T) -> bool) -> bool {
    forall|x: T, y: T| #[trigger] r(x, y) <==> #[trigger] r(y, x)
}

pub open spec fn connected<T>(r: spec_fn(T, T) -> bool) -> bool {
    forall|x: T, y: T| x != y ==> #[trigger] r(x, y) || #[trigger] r(y, x)
}

pub open spec fn strongly_connected<T>(r: spec_fn(T, T) -> bool) -> bool {
    forall|x: T, y: T| #[trigger] r(x, y) || #[trigger] r(y, x)
}

pub open spec fn transitive<T>(r: spec_fn(T, T) -> bool) -> bool {
    forall|x: T, y: T, z: T| #[trigger] r(x, y) && #[trigger] r(y, z) ==> r(x, z)
}

pub open spec fn total_ordering<T>(r: spec_fn(T, T) -> bool) -> bool {
    &&& reflexive(r)
    &&& antisymmetric(r)
    &&& transitive(r)
    &&& strongly_connected(r)
}

pub open spec fn strict_total_ordering<T>(r: spec_fn(T, T) -> bool) -> bool {
    &&& irreflexive(r)
    &&& antisymmetric(r)
    &&& transitive(r)
    &&& connected(r)
}

pub open spec fn pre_ordering<T>(r: spec_fn(T, T) -> bool) -> bool {
    &&& reflexive(r)
    &&& transitive(r)
}

pub open spec fn partial_ordering<T>(r: spec_fn(T, T) -> bool) -> bool {
    &&& reflexive(r)
    &&& transitive(r)
    &&& antisymmetric(r)
}

pub open spec fn equivalence_relation<T>(r: spec_fn(T, T) -> bool) -> bool {
    &&& reflexive(r)
    &&& symmetric(r)
    &&& transitive(r)
}

/// This function returns true if the input sequence a is sorted, using the input function
/// less_than to sort the elements
pub open spec fn sorted_by<T>(a: Seq<T>, less_than: spec_fn(T, T) -> bool) -> bool {
    forall|i: int, j: int| 0 <= i < j < a.len() ==> #[trigger] less_than(a[i], a[j])
}

pub proof fn lemma_new_first_element_still_sorted_by<T>(
    x: T,
    s: Seq<T>,
    less_than: spec_fn(T, T) -> bool,
)
    requires
        sorted_by(s, less_than),
        s.len() == 0 || less_than(x, s[0]),
        total_ordering(less_than),
    ensures
        sorted_by(seq![x].add(s), less_than),
{
    broadcast use group_seq_lemmas;

    if s.len() > 1 {
        assert forall|index: int| 0 < index < s.len() implies #[trigger] less_than(x, s[index]) by {
            assert(less_than(s[0], s[index]));
        };
    }
}

} // verus!
