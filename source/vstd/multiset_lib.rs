#[allow(unused_imports)]
use super::multiset::Multiset;
#[allow(unused_imports)]
use super::prelude::*;

verus! {

broadcast use super::multiset::group_multiset_axioms;

impl<A> Multiset<A> {
    /// Is `true` if called by an "empty" multiset, i.e., a set containing no elements and has length 0
    pub open spec fn is_empty(self) -> (b: bool) {
        self.len() == 0
    }

    /// A singleton multiset has at least one element with multiplicity 1 and any two elements are equal.
    pub open spec fn is_singleton(self) -> bool {
        &&& self.len() > 0
        &&& (forall|x: A| self.contains(x) ==> self.count(x) == 1)
        &&& (forall|x: A, y: A| self.contains(x) && self.contains(y) ==> x == y)
    }

    /// A singleton multiset that contains an alement is equivalent to the singleton multiset with that element.
    pub proof fn lemma_is_singleton_contains_elem_equal_singleton(self, x: A)
        requires
            self.is_singleton(),
            self.contains(x),
        ensures
            self =~= Multiset::singleton(x),
    {
        assert forall|y: A| #[trigger] Multiset::singleton(x).count(y) == self.count(y) by {
            if self.contains(y) {
            } else {
            }
        };
    }

    /// A singleton multiset has length 1.
    pub proof fn lemma_singleton_size(self)
        requires
            self.is_singleton(),
        ensures
            self.len() == 1,
    {
        self.lemma_is_singleton_contains_elem_equal_singleton(self.choose());
    }

    /// A multiset has exactly one element, if and only if, it has at least one element with multiplicity 1 and any two elements are equal.
    pub proof fn lemma_is_singleton(s: Multiset<A>)
        ensures
            s.is_singleton() <==> (s.len() == 1),
    {
        if s.is_singleton() {
            s.lemma_singleton_size();
        }
        if s.len() == 1 {
            assert forall|x: A, y: A| s.contains(x) && s.contains(y) implies x == y by {
                assert(s.remove(x).len() == 0);
                if x != y {
                    assert(s.remove(x).count(y) == 0);
                    assert(s.remove(x).insert(x) =~= s);
                }
            }
        }
    }
}

} // verus!
