//! Specifications for `std::collections::BTreeSet`
//!
//! BTreeSet is viewed as a `Set<K>` since it maintains unique ordered elements.
//! Unlike HashSet, BTreeSet requires Ord on elements and iteration is ordered.
use super::super::prelude::*;

use alloc::collections::btree_set::{IntoIter, Iter};
use alloc::collections::BTreeSet;
use core::alloc::Allocator;
use core::clone::Clone;
use core::cmp::Ord;
use core::marker::PhantomData;
use core::option::Option;
use core::option::Option::None;
use core::option::Option::Some;

use verus as verus_;
verus_! {

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::accept_recursive_types(K)]
#[verifier::reject_recursive_types(A)]
pub struct ExBTreeSet<K, A: Allocator + Clone>(BTreeSet<K, A>);

/// BTreeSet views as a `Set<K>`
impl<K, A: Allocator + Clone> View for BTreeSet<K, A> {
    type V = Set<K>;

    uninterp spec fn view(&self) -> Set<K>;
}

// Len (with autospec pattern)

pub uninterp spec fn spec_btree_set_len<K, A: Allocator + Clone>(s: &BTreeSet<K, A>) -> usize;

pub broadcast proof fn axiom_spec_len<K, A: Allocator + Clone>(s: &BTreeSet<K, A>)
    ensures
        #[trigger] spec_btree_set_len(s) == s@.len(),
{
    admit();
}

#[verifier::when_used_as_spec(spec_btree_set_len)]
pub assume_specification<K, A: Allocator + Clone>[ BTreeSet::<K, A>::len ](s: &BTreeSet<K, A>) -> (len: usize)
    ensures
        len == spec_btree_set_len(s),
    no_unwind
;

pub assume_specification<K, A: Allocator + Clone>[ BTreeSet::<K, A>::is_empty ](s: &BTreeSet<K, A>) -> (res: bool)
    ensures
        res == (s@.len() == 0),
;

pub assume_specification<K>[ BTreeSet::<K>::new ]() -> (s: BTreeSet<K>)
    ensures
        s@ == Set::<K>::empty(),
;

pub assume_specification<K: Ord, A: Allocator + Clone>[ BTreeSet::<K, A>::insert ](
    s: &mut BTreeSet<K, A>,
    value: K,
) -> (replaced: bool)
    ensures
        s@ == old(s)@.insert(value),
        replaced == old(s)@.contains(value),
;

use core::borrow::Borrow;

// For remove/contains, Rust uses Borrow<Q> pattern for flexible lookups.
// We provide uninterp specs and axioms similar to BTreeMap.

// For element types that impl Borrow<Q>, we can query/remove by &Q
pub uninterp spec fn btree_set_contains_borrowed<K, Q: ?Sized>(s: Set<K>, q: &Q) -> bool;

pub broadcast proof fn axiom_btree_set_contains_borrowed<Q>(s: Set<Q>, q: &Q)
    ensures
        #[trigger] btree_set_contains_borrowed::<Q, Q>(s, q) <==> s.contains(*q),
{
    admit();
}

pub uninterp spec fn btree_set_borrowed_removed<K, Q: ?Sized>(old_s: Set<K>, new_s: Set<K>, q: &Q) -> bool;

pub broadcast proof fn axiom_btree_set_borrowed_removed<Q>(old_s: Set<Q>, new_s: Set<Q>, q: &Q)
    ensures
        #[trigger] btree_set_borrowed_removed::<Q, Q>(old_s, new_s, q) <==> new_s == old_s.remove(*q),
{
    admit();
}

pub assume_specification<K: Ord + Borrow<Q>, A: Allocator + Clone, Q: Ord + ?Sized>[ BTreeSet::<K, A>::remove::<Q> ](
    s: &mut BTreeSet<K, A>,
    value: &Q,
) -> (was_present: bool)
    ensures
        btree_set_borrowed_removed(old(s)@, s@, value),
        was_present == btree_set_contains_borrowed(old(s)@, value),
;

pub assume_specification<K: Ord + Borrow<Q>, A: Allocator + Clone, Q: Ord + ?Sized>[ BTreeSet::<K, A>::contains::<Q> ](
    s: &BTreeSet<K, A>,
    value: &Q,
) -> (res: bool)
    ensures
        res == btree_set_contains_borrowed(s@, value),
;

pub assume_specification<K, A: Allocator + Clone + Clone>[ BTreeSet::<K, A>::clear ](s: &mut BTreeSet<K, A>)
    ensures
        s@ == Set::<K>::empty(),
;

pub assume_specification<K: Clone, A: Allocator + Clone>[ <BTreeSet<K, A> as Clone>::clone ](
    s: &BTreeSet<K, A>,
) -> (res: BTreeSet<K, A>)
    ensures
        res@ == s@,
;

// retain - NOT WRAPPABLE
//
// BTreeSet::retain takes FnMut(&K) -> bool, but due to Verus limitations with
// closures, this cannot be easily specified. Unlike BTreeMap::retain which has
// &mut V (truly problematic), BTreeSet's retain uses immutable &K, but Verus
// still needs closure support improvements to handle this properly.

/// A `Set` constructed from a `BTreeSet` is always finite.
pub broadcast proof fn axiom_btree_set_view_finite<K, A: Allocator + Clone>(s: BTreeSet<K, A>)
    ensures
        #[trigger] s@.finite(),
{
    admit();
}

// Iter (borrowing iterator)

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::accept_recursive_types(K)]
pub struct ExBTreeSetIter<'a, K: 'a>(Iter<'a, K>);

impl<'a, K> View for Iter<'a, K> {
    type V = (int, Seq<K>);

    uninterp spec fn view(&self) -> (int, Seq<K>);
}

pub assume_specification<'a, K>[ Iter::<'a, K>::next ](
    iter: &mut Iter<'a, K>,
) -> (r: Option<&'a K>)
    ensures
        ({
            let (old_index, old_seq) = old(iter)@;
            match r {
                None => {
                    &&& iter@ == old(iter)@
                    &&& old_index >= old_seq.len()
                },
                Some(val) => {
                    let (new_index, new_seq) = iter@;
                    &&& 0 <= old_index < old_seq.len()
                    &&& new_seq == old_seq
                    &&& new_index == old_index + 1
                    &&& *val == old_seq[old_index]
                },
            }
        }),
;

pub struct BTreeSetIterGhostIterator<'a, K> {
    pub pos: int,
    pub elements: Seq<K>,
    pub _marker: PhantomData<&'a K>,
}

impl<'a, K> super::super::pervasive::ForLoopGhostIteratorNew for Iter<'a, K> {
    type GhostIter = BTreeSetIterGhostIterator<'a, K>;

    open spec fn ghost_iter(&self) -> BTreeSetIterGhostIterator<'a, K> {
        BTreeSetIterGhostIterator { pos: self@.0, elements: self@.1, _marker: PhantomData }
    }
}

impl<'a, K: 'a> super::super::pervasive::ForLoopGhostIterator for BTreeSetIterGhostIterator<'a, K> {
    type ExecIter = Iter<'a, K>;
    type Item = K;
    type Decrease = int;

    open spec fn exec_invariant(&self, exec_iter: &Iter<'a, K>) -> bool {
        &&& self.pos == exec_iter@.0
        &&& self.elements == exec_iter@.1
    }

    open spec fn ghost_invariant(&self, init: Option<&Self>) -> bool {
        init matches Some(init) ==> {
            &&& init.pos == 0
            &&& init.elements == self.elements
            &&& 0 <= self.pos <= self.elements.len()
        }
    }

    open spec fn ghost_ensures(&self) -> bool {
        self.pos == self.elements.len()
    }

    open spec fn ghost_decrease(&self) -> Option<int> {
        Some(self.elements.len() - self.pos)
    }

    open spec fn ghost_peek_next(&self) -> Option<K> {
        if 0 <= self.pos < self.elements.len() {
            Some(self.elements[self.pos])
        } else {
            None
        }
    }

    open spec fn ghost_advance(&self, _exec_iter: &Iter<'a, K>) -> BTreeSetIterGhostIterator<'a, K> {
        Self { pos: self.pos + 1, ..*self }
    }
}

impl<'a, K> View for BTreeSetIterGhostIterator<'a, K> {
    type V = Seq<K>;

    open spec fn view(&self) -> Seq<K> {
        self.elements.take(self.pos)
    }
}

pub uninterp spec fn spec_btree_set_iter<'a, K, A: Allocator + Clone>(s: &'a BTreeSet<K, A>) -> Iter<'a, K>;

pub broadcast proof fn axiom_spec_iter<'a, K, A: Allocator + Clone>(s: &'a BTreeSet<K, A>)
    ensures
        ({
            let (pos, seq) = #[trigger] spec_btree_set_iter(s)@;
            &&& pos == 0int
            &&& forall|i: int| 0 <= i < seq.len() ==> s@.contains(#[trigger] seq[i])
        }),
{
    admit();
}

#[verifier::when_used_as_spec(spec_btree_set_iter)]
pub assume_specification<'a, K, A: Allocator + Clone>[ BTreeSet::<K, A>::iter ](s: &'a BTreeSet<K, A>) -> (iter: Iter<'a, K>)
    ensures
        ({
            let (index, seq) = iter@;
            &&& index == 0
            &&& seq.to_set() == s@
            &&& seq.no_duplicates()
            &&& seq.len() == s@.len()
        }),
    no_unwind
;

// IntoIter (consuming iterator)

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::accept_recursive_types(K)]
#[verifier::reject_recursive_types(A)]
pub struct ExBTreeSetIntoIter<K, A: Allocator + Clone>(IntoIter<K, A>);

impl<K, A: Allocator + Clone> View for IntoIter<K, A> {
    type V = (int, Seq<K>);

    uninterp spec fn view(&self) -> (int, Seq<K>);
}

pub assume_specification<K, A: Allocator + Clone>[ IntoIter::<K, A>::next ](
    iter: &mut IntoIter<K, A>,
) -> (r: Option<K>)
    ensures
        ({
            let (old_index, old_seq) = old(iter)@;
            match r {
                None => {
                    &&& iter@ == old(iter)@
                    &&& old_index >= old_seq.len()
                },
                Some(val) => {
                    let (new_index, new_seq) = iter@;
                    &&& 0 <= old_index < old_seq.len()
                    &&& new_seq == old_seq
                    &&& new_index == old_index + 1
                    &&& val == old_seq[old_index]
                },
            }
        }),
;

pub struct BTreeSetIntoIterGhostIterator<K, A: Allocator + Clone> {
    pub pos: int,
    pub elements: Seq<K>,
    pub _marker: PhantomData<A>,
}

impl<K, A: Allocator + Clone> super::super::pervasive::ForLoopGhostIteratorNew for IntoIter<K, A> {
    type GhostIter = BTreeSetIntoIterGhostIterator<K, A>;

    open spec fn ghost_iter(&self) -> BTreeSetIntoIterGhostIterator<K, A> {
        BTreeSetIntoIterGhostIterator { pos: self@.0, elements: self@.1, _marker: PhantomData }
    }
}

impl<K, A: Allocator + Clone> super::super::pervasive::ForLoopGhostIterator for BTreeSetIntoIterGhostIterator<K, A> {
    type ExecIter = IntoIter<K, A>;
    type Item = K;
    type Decrease = int;

    open spec fn exec_invariant(&self, exec_iter: &IntoIter<K, A>) -> bool {
        &&& self.pos == exec_iter@.0
        &&& self.elements == exec_iter@.1
    }

    open spec fn ghost_invariant(&self, init: Option<&Self>) -> bool {
        init matches Some(init) ==> {
            &&& init.pos == 0
            &&& init.elements == self.elements
            &&& 0 <= self.pos <= self.elements.len()
        }
    }

    open spec fn ghost_ensures(&self) -> bool {
        self.pos == self.elements.len()
    }

    open spec fn ghost_decrease(&self) -> Option<int> {
        Some(self.elements.len() - self.pos)
    }

    open spec fn ghost_peek_next(&self) -> Option<K> {
        if 0 <= self.pos < self.elements.len() {
            Some(self.elements[self.pos])
        } else {
            None
        }
    }

    open spec fn ghost_advance(&self, _exec_iter: &IntoIter<K, A>) -> BTreeSetIntoIterGhostIterator<K, A> {
        Self { pos: self.pos + 1, ..*self }
    }
}

impl<K, A: Allocator + Clone> View for BTreeSetIntoIterGhostIterator<K, A> {
    type V = Seq<K>;

    open spec fn view(&self) -> Seq<K> {
        self.elements.take(self.pos)
    }
}

pub uninterp spec fn spec_btree_set_into_iter<K, A: Allocator + Clone>(s: BTreeSet<K, A>) -> IntoIter<K, A>;

pub broadcast proof fn axiom_spec_into_iter<K, A: Allocator + Clone>(s: BTreeSet<K, A>)
    ensures
        (#[trigger] spec_btree_set_into_iter(s))@.0 == 0,
        (#[trigger] spec_btree_set_into_iter(s))@.1.to_set() == s@,
{
    admit();
}

#[verifier::when_used_as_spec(spec_btree_set_into_iter)]
pub assume_specification<K, A: Allocator + Clone>[ BTreeSet::<K, A>::into_iter ](s: BTreeSet<K, A>) -> (iter: IntoIter<K, A>)
    ensures
        iter@.0 == 0,
        iter@.1.to_set() == s@,
        iter@.1.no_duplicates(),
        iter@.1.len() == s@.len(),
;

// DeepView implementation for BTreeSet

impl<K: DeepView, A: Allocator + Clone> DeepView for BTreeSet<K, A> {
    type V = Set<K::V>;

    open spec fn deep_view(&self) -> Set<K::V> {
        self@.map(|x: K| x.deep_view())
    }
}

// Broadcast group

pub broadcast group group_btree_set_axioms {
    axiom_spec_len,
    axiom_btree_set_view_finite,
    axiom_btree_set_contains_borrowed,
    axiom_btree_set_borrowed_removed,
    axiom_spec_iter,
    axiom_spec_into_iter,
}

} // verus!
