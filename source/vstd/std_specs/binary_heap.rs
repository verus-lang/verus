//! Specifications for `std::collections::BinaryHeap`
//!
//! BinaryHeap is viewed as a `Multiset<T>` since it's a max-heap where
//! element order doesn't matter for the abstract view, only membership.
//!
//! The `pop` and `peek` methods are specified to return the **maximum** element
//! via the `is_heap_max` predicate.
use super::super::multiset::Multiset;
use super::super::prelude::*;
use verus_builtin::*;

use alloc::collections::binary_heap::IntoIter;
use alloc::collections::binary_heap::Iter;
use alloc::collections::BinaryHeap;
use core::alloc::Allocator;
use core::clone::Clone;
use core::cmp::Ord;
use core::cmp::Ordering;
use core::marker::PhantomData;
use core::option::Option;
use core::option::Option::None;
use core::option::Option::Some;

use verus as verus_;
verus_! {

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::accept_recursive_types(T)]
#[verifier::reject_recursive_types(A)]
pub struct ExBinaryHeap<T, A: Allocator>(BinaryHeap<T, A>);

/// BinaryHeap views as a Multiset - order doesn't matter, just membership
impl<T, A: Allocator> View for BinaryHeap<T, A> {
    type V = Multiset<T>;

    uninterp spec fn view(&self) -> Multiset<T>;
}

pub trait BinaryHeapAdditionalSpecFns<T>: View<V = Multiset<T>> {
    /// Returns true if the heap contains the given element
    spec fn spec_contains(&self, value: T) -> bool;
}

impl<T, A: Allocator> BinaryHeapAdditionalSpecFns<T> for BinaryHeap<T, A> {
    #[verifier::inline]
    open spec fn spec_contains(&self, value: T) -> bool {
        self.view().contains(value)
    }
}

// Len (with autospec pattern)

pub uninterp spec fn spec_binary_heap_len<T, A: Allocator>(h: &BinaryHeap<T, A>) -> usize;

pub broadcast proof fn axiom_spec_len<T, A: Allocator>(h: &BinaryHeap<T, A>)
    ensures
        #[trigger] spec_binary_heap_len(h) == h@.len(),
{
    admit();
}

#[verifier::when_used_as_spec(spec_binary_heap_len)]
pub assume_specification<T, A: Allocator>[ BinaryHeap::<T, A>::len ](heap: &BinaryHeap<T, A>) -> (len: usize)
    ensures
        len == spec_binary_heap_len(heap),
    no_unwind
;

// Maximality predicate for heap elements
//
// `is_heap_max(v, heap)` means v is greater than or equal to all elements in the multiset.
// This is an uninterpreted predicate that captures the max-heap invariant.
// For types with `obeys_partial_cmp_spec()`, axioms connect this to `partial_cmp_spec`.
pub uninterp spec fn is_heap_max<T>(v: T, heap: Multiset<T>) -> bool;

pub assume_specification<T: Ord>[ BinaryHeap::<T>::new ]() -> (heap: BinaryHeap<T>)
    ensures
        heap@ == Multiset::<T>::empty(),
;

pub assume_specification<T: Ord>[ BinaryHeap::<T>::with_capacity ](capacity: usize) -> (heap: BinaryHeap<T>)
    ensures
        heap@ == Multiset::<T>::empty(),
;

pub assume_specification<T: Ord, A: Allocator>[ BinaryHeap::<T, A>::push ](heap: &mut BinaryHeap<T, A>, item: T)
    ensures
        heap@ == old(heap)@.insert(item),
;

// Pop - removes and returns the maximum element
//
// The returned value is guaranteed to be the maximum element according to the
// Ord ordering. The `is_heap_max` predicate captures this.

pub assume_specification<T: Ord, A: Allocator>[ BinaryHeap::<T, A>::pop ](heap: &mut BinaryHeap<T, A>) -> (value: Option<T>)
    ensures
        old(heap)@.len() == 0 ==> value.is_none() && heap@ == old(heap)@,
        old(heap)@.len() > 0 ==> value.is_some()
            && old(heap)@.contains(value.unwrap())
            && heap@ == old(heap)@.remove(value.unwrap())
            && is_heap_max(value.unwrap(), old(heap)@),
;

// Peek - returns reference to maximum element without removing
//
// The returned value is guaranteed to be the maximum element according to the
// Ord ordering. The `is_heap_max` predicate captures this.
// Note: peek doesn't require T: Ord in Rust (only in the heap's construction).

pub assume_specification<T, A: Allocator>[ BinaryHeap::<T, A>::peek ](heap: &BinaryHeap<T, A>) -> (value: Option<&T>)
    ensures
        heap@.len() == 0 ==> value.is_none(),
        heap@.len() > 0 ==> value.is_some()
            && heap@.contains(*value.unwrap())
            && is_heap_max(*value.unwrap(), heap@),
    no_unwind
;

pub assume_specification<T, A: Allocator>[ BinaryHeap::<T, A>::is_empty ](heap: &BinaryHeap<T, A>) -> (res: bool)
    ensures
        res <==> heap@.len() == 0,
    no_unwind
;

pub assume_specification<T, A: Allocator>[ BinaryHeap::<T, A>::clear ](heap: &mut BinaryHeap<T, A>)
    ensures
        heap@ == Multiset::<T>::empty(),
;


pub open spec fn binary_heap_clone_trigger<T, A: Allocator>(h1: BinaryHeap<T, A>, h2: BinaryHeap<T, A>) -> bool {
    true
}

pub assume_specification<T: Clone, A: Allocator + Clone>[ <BinaryHeap<T, A> as Clone>::clone ](
    heap: &BinaryHeap<T, A>,
) -> (res: BinaryHeap<T, A>)
    ensures
        res@ == heap@,
        binary_heap_clone_trigger(*heap, res),
;

// Note: BinaryHeap does not implement PartialEq in std, so no eq specs here.

// Axioms for is_heap_max
//
// These axioms connect is_heap_max to the ordering relation for primitive types.

/// For any element x in the multiset, x <= max (using integer comparison)
pub broadcast proof fn axiom_is_heap_max_u32(v: u32, heap: Multiset<u32>)
    ensures
        #[trigger] is_heap_max(v, heap) ==> forall|x: u32| heap.contains(x) ==> x <= v,
{
    admit();
}

pub broadcast proof fn axiom_is_heap_max_u64(v: u64, heap: Multiset<u64>)
    ensures
        #[trigger] is_heap_max(v, heap) ==> forall|x: u64| heap.contains(x) ==> x <= v,
{
    admit();
}

pub broadcast proof fn axiom_is_heap_max_i32(v: i32, heap: Multiset<i32>)
    ensures
        #[trigger] is_heap_max(v, heap) ==> forall|x: i32| heap.contains(x) ==> x <= v,
{
    admit();
}

pub broadcast proof fn axiom_is_heap_max_i64(v: i64, heap: Multiset<i64>)
    ensures
        #[trigger] is_heap_max(v, heap) ==> forall|x: i64| heap.contains(x) ==> x <= v,
{
    admit();
}

// IntoIter - consuming iterator

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::accept_recursive_types(T)]
#[verifier::reject_recursive_types(A)]
pub struct ExBinaryHeapIntoIter<T, A: Allocator>(IntoIter<T, A>);

/// IntoIter views as (position, remaining elements as Seq)
/// Note: iteration order is unspecified for BinaryHeap
impl<T, A: Allocator> View for IntoIter<T, A> {
    type V = (int, Seq<T>);

    uninterp spec fn view(&self) -> (int, Seq<T>);
}

pub assume_specification<T, A: Allocator>[ IntoIter::<T, A>::next ](
    iter: &mut IntoIter<T, A>,
) -> (r: Option<T>)
    ensures
        ({
            let (old_index, old_seq) = old(iter)@;
            match r {
                None => {
                    &&& iter@ == old(iter)@
                    &&& old_index >= old_seq.len()
                },
                Some(element) => {
                    let (new_index, new_seq) = iter@;
                    &&& 0 <= old_index < old_seq.len()
                    &&& new_seq == old_seq
                    &&& new_index == old_index + 1
                    &&& element == old_seq[old_index]
                },
            }
        }),
;

pub struct IntoIterGhostIterator<T, A: Allocator> {
    pub pos: int,
    pub elements: Seq<T>,
    pub _marker: PhantomData<A>,
}

impl<T, A: Allocator> super::super::pervasive::ForLoopGhostIteratorNew for IntoIter<T, A> {
    type GhostIter = IntoIterGhostIterator<T, A>;

    open spec fn ghost_iter(&self) -> IntoIterGhostIterator<T, A> {
        IntoIterGhostIterator { pos: self@.0, elements: self@.1, _marker: PhantomData }
    }
}

impl<T, A: Allocator> super::super::pervasive::ForLoopGhostIterator for IntoIterGhostIterator<T, A> {
    type ExecIter = IntoIter<T, A>;
    type Item = T;
    type Decrease = int;

    open spec fn exec_invariant(&self, exec_iter: &IntoIter<T, A>) -> bool {
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

    open spec fn ghost_peek_next(&self) -> Option<T> {
        if 0 <= self.pos < self.elements.len() {
            Some(self.elements[self.pos])
        } else {
            None
        }
    }

    open spec fn ghost_advance(&self, _exec_iter: &IntoIter<T, A>) -> IntoIterGhostIterator<T, A> {
        Self { pos: self.pos + 1, ..*self }
    }
}

impl<T, A: Allocator> View for IntoIterGhostIterator<T, A> {
    type V = Seq<T>;

    open spec fn view(&self) -> Seq<T> {
        self.elements.take(self.pos)
    }
}

pub uninterp spec fn spec_binary_heap_into_iter<T, A: Allocator>(h: BinaryHeap<T, A>) -> IntoIter<T, A>;

pub broadcast proof fn axiom_spec_into_iter<T, A: Allocator>(h: BinaryHeap<T, A>)
    ensures
        (#[trigger] spec_binary_heap_into_iter(h))@.0 == 0,
        // The elements in the iterator correspond to the multiset
        (#[trigger] spec_binary_heap_into_iter(h))@.1.to_multiset() == h@,
{
    admit();
}

#[verifier::when_used_as_spec(spec_binary_heap_into_iter)]
pub assume_specification<T, A: Allocator>[ BinaryHeap::<T, A>::into_iter ](heap: BinaryHeap<T, A>) -> (iter: IntoIter<T, A>)
    ensures
        iter@.0 == 0,
        iter@.1.to_multiset() == heap@,
;

// Iter - borrowing iterator

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::accept_recursive_types(T)]
pub struct ExBinaryHeapIter<'a, T: 'a>(Iter<'a, T>);

// Iter views as (position, elements as Seq of references)
impl<'a, T> View for Iter<'a, T> {
    type V = (int, Seq<T>);

    uninterp spec fn view(&self) -> (int, Seq<T>);
}

pub assume_specification<'a, T>[ Iter::<'a, T>::next ](
    iter: &mut Iter<'a, T>,
) -> (r: Option<&'a T>)
    ensures
        ({
            let (old_index, old_seq) = old(iter)@;
            match r {
                None => {
                    &&& iter@ == old(iter)@
                    &&& old_index >= old_seq.len()
                },
                Some(element) => {
                    let (new_index, new_seq) = iter@;
                    &&& 0 <= old_index < old_seq.len()
                    &&& new_seq == old_seq
                    &&& new_index == old_index + 1
                    &&& *element == old_seq[old_index]
                },
            }
        }),
;

pub struct IterGhostIterator<'a, T> {
    pub pos: int,
    pub elements: Seq<T>,
    pub _marker: PhantomData<&'a T>,
}

impl<'a, T> super::super::pervasive::ForLoopGhostIteratorNew for Iter<'a, T> {
    type GhostIter = IterGhostIterator<'a, T>;

    open spec fn ghost_iter(&self) -> IterGhostIterator<'a, T> {
        IterGhostIterator { pos: self@.0, elements: self@.1, _marker: PhantomData }
    }
}

impl<'a, T: 'a> super::super::pervasive::ForLoopGhostIterator for IterGhostIterator<'a, T> {
    type ExecIter = Iter<'a, T>;
    type Item = &'a T;
    type Decrease = int;

    open spec fn exec_invariant(&self, exec_iter: &Iter<'a, T>) -> bool {
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

    open spec fn ghost_peek_next(&self) -> Option<&'a T> {
        if 0 <= self.pos < self.elements.len() {
            Some(&self.elements[self.pos])
        } else {
            None
        }
    }

    open spec fn ghost_advance(&self, _exec_iter: &Iter<'a, T>) -> IterGhostIterator<'a, T> {
        Self { pos: self.pos + 1, ..*self }
    }
}

impl<'a, T> View for IterGhostIterator<'a, T> {
    type V = Seq<T>;

    open spec fn view(&self) -> Seq<T> {
        self.elements.take(self.pos)
    }
}

pub uninterp spec fn spec_binary_heap_iter<'a, T, A: Allocator>(h: &'a BinaryHeap<T, A>) -> Iter<'a, T>;

pub broadcast proof fn axiom_spec_iter<'a, T, A: Allocator>(h: &'a BinaryHeap<T, A>)
    ensures
        (#[trigger] spec_binary_heap_iter(h))@.0 == 0,
        (#[trigger] spec_binary_heap_iter(h))@.1.to_multiset() == h@,
{
    admit();
}

#[verifier::when_used_as_spec(spec_binary_heap_iter)]
pub assume_specification<'a, T, A: Allocator>[ BinaryHeap::<T, A>::iter ](heap: &'a BinaryHeap<T, A>) -> (iter: Iter<'a, T>)
    ensures
        iter@.0 == 0,
        iter@.1.to_multiset() == heap@,
;

// DeepView implementation for BinaryHeap

impl<T: DeepView, A: Allocator> DeepView for BinaryHeap<T, A> {
    type V = Multiset<T::V>;

    open spec fn deep_view(&self) -> Multiset<T::V> {
        binary_heap_deep_view_impl(*self)
    }
}

/// The actual definition of `BinaryHeap::deep_view`.
///
/// Maps each element through its deep_view, preserving multiplicities.
/// Uses from_map to construct a new multiset where each deep-viewed element
/// has the same count as the sum of counts of all original elements that map to it.
#[verifier::opaque]
pub open spec fn binary_heap_deep_view_impl<T: DeepView, A: Allocator>(
    h: BinaryHeap<T, A>,
) -> Multiset<T::V> {
    Multiset::from_map(
        Map::new(
            |dv: T::V| exists|t: T| h@.contains(t) && #[trigger] t.deep_view() == dv,
            |dv: T::V| {
                // Sum counts of all elements that deep_view to dv
                // For injective deep_view, this is just the count of the unique preimage
                let t = choose|t: T| h@.contains(t) && #[trigger] t.deep_view() == dv;
                h@.count(t)
            },
        )
    )
}

// Broadcast group

pub broadcast group group_binary_heap_axioms {
    axiom_spec_len,
    axiom_spec_into_iter,
    axiom_spec_iter,
    axiom_is_heap_max_u32,
    axiom_is_heap_max_u64,
    axiom_is_heap_max_i32,
    axiom_is_heap_max_i64,
}

} // verus!
