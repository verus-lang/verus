/// This code adds specifications for the standard-library type
/// `std::collections::VecDeque`.
use super::super::prelude::*;

use alloc::collections::vec_deque::Iter;
use alloc::collections::vec_deque::VecDeque;
use core::alloc::Allocator;
use core::clone::Clone;
use core::ops::Index;
use core::option::Option;
use core::option::Option::None;

verus! {

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::accept_recursive_types(T)]
#[verifier::reject_recursive_types(A)]
pub struct ExVecDeque<T, A: Allocator>(VecDeque<T, A>);

impl<T, A: Allocator> View for VecDeque<T, A> {
    type V = Seq<T>;

    uninterp spec fn view(&self) -> Seq<T>;
}

pub trait VecDequeAdditionalSpecFns<T>: View<V = Seq<T>> {
    spec fn spec_index(&self, i: int) -> T
        recommends
            0 <= i < self.view().len(),
    ;
}

impl<T, A: Allocator> VecDequeAdditionalSpecFns<T> for VecDeque<T, A> {
    #[verifier::inline]
    open spec fn spec_index(&self, i: int) -> T {
        self.view().index(i)
    }
}

////// Len (with autospec)
pub uninterp spec fn spec_vec_dequeue_len<T, A: Allocator>(v: &VecDeque<T, A>) -> usize;

// This axiom is slightly better than defining spec_vec_dequeue_len to just be `v@.len() as usize`
// (the axiom also shows that v@.len() is in-bounds for usize)
pub broadcast proof fn axiom_spec_len<T, A: Allocator>(v: &VecDeque<T, A>)
    ensures
        #[trigger] spec_vec_dequeue_len(v) == v@.len(),
{
    admit();
}

pub assume_specification<T, A: Allocator>[ VecDeque::<T, A>::index ](
    v: &VecDeque<T, A>,
    i: usize,
) -> (result: &T)
    requires
        i < v.len(),
    ensures
        result == v.spec_index(i as int),
;

#[verifier::when_used_as_spec(spec_vec_dequeue_len)]
pub assume_specification<T, A: Allocator>[ VecDeque::<T, A>::len ](v: &VecDeque<T, A>) -> (len:
    usize)
    ensures
        len == spec_vec_dequeue_len(v),
;

pub assume_specification<T>[ VecDeque::<T>::new ]() -> (v: VecDeque<T>)
    ensures
        v@ == Seq::<T>::empty(),
;

pub assume_specification<T>[ VecDeque::<T>::with_capacity ](capacity: usize) -> (v: VecDeque<T>)
    ensures
        v@ == Seq::<T>::empty(),
;

pub assume_specification<T, A: Allocator>[ VecDeque::<T, A>::reserve ](
    v: &mut VecDeque<T, A>,
    additional: usize,
)
    ensures
        v@ == old(v)@,
;

pub assume_specification<T, A: Allocator>[ VecDeque::<T, A>::push_back ](
    v: &mut VecDeque<T, A>,
    value: T,
)
    ensures
        v@ == old(v)@.push(value),
;

pub assume_specification<T, A: Allocator>[ VecDeque::<T, A>::push_front ](
    v: &mut VecDeque<T, A>,
    value: T,
)
    ensures
        v@ == seq![value] + old(v)@,
;

pub assume_specification<T, A: Allocator>[ VecDeque::<T, A>::pop_back ](
    v: &mut VecDeque<T, A>,
) -> (value: Option<T>)
    ensures
        match value {
            Some(x) => {
                &&& old(v)@.len() > 0
                &&& x == old(v)@[old(v)@.len() - 1]
                &&& v@ == old(v)@.subrange(0, old(v)@.len() as int - 1)
            },
            None => {
                &&& old(v)@.len() == 0
                &&& v@ == old(v)@
            },
        },
;

pub assume_specification<T, A: Allocator>[ VecDeque::<T, A>::pop_front ](
    v: &mut VecDeque<T, A>,
) -> (value: Option<T>)
    ensures
        match value {
            Some(x) => {
                &&& old(v)@.len() > 0
                &&& x == old(v)@[0]
                &&& v@ == old(v)@.subrange(1, old(v)@.len() as int)
            },
            None => {
                &&& old(v)@.len() == 0
                &&& v@ == old(v)@
            },
        },
;

pub assume_specification<T, A: Allocator>[ VecDeque::<T, A>::append ](
    v: &mut VecDeque<T, A>,
    other: &mut VecDeque<T, A>,
)
    ensures
        v@ == old(v)@ + old(other)@,
        other@ == Seq::<T>::empty(),
;

pub assume_specification<T, A: Allocator>[ VecDeque::<T, A>::insert ](
    v: &mut VecDeque<T, A>,
    i: usize,
    element: T,
)
    requires
        i <= old(v).len(),
    ensures
        v@ == old(v)@.insert(i as int, element),
;

pub assume_specification<T, A: Allocator>[ VecDeque::<T, A>::remove ](
    v: &mut VecDeque<T, A>,
    i: usize,
) -> (element: Option<T>)
    ensures
        match element {
            Some(x) => {
                &&& i < old(v)@.len()
                &&& x == old(v)@[i as int]
                &&& v@ == old(v)@.remove(i as int)
            },
            None => {
                &&& old(v)@.len() <= i
                &&& v@ == old(v)@
            },
        },
;

pub assume_specification<T, A: Allocator>[ VecDeque::<T, A>::clear ](v: &mut VecDeque<T, A>)
    ensures
        v.view() == Seq::<T>::empty(),
;

pub assume_specification<T, A: Allocator + core::clone::Clone>[ VecDeque::<T, A>::split_off ](
    v: &mut VecDeque<T, A>,
    at: usize,
) -> (return_value: VecDeque<T, A>)
    requires
        at <= old(v)@.len(),
    ensures
        v@ == old(v)@.subrange(0, at as int),
        return_value@ == old(v)@.subrange(at as int, old(v)@.len() as int),
;

pub open spec fn vec_dequeue_clone_trigger<T, A: Allocator>(
    v1: VecDeque<T, A>,
    v2: VecDeque<T, A>,
) -> bool {
    true
}

pub assume_specification<T: Clone, A: Allocator + Clone>[ <VecDeque<T, A> as Clone>::clone ](
    v: &VecDeque<T, A>,
) -> (res: VecDeque<T, A>)
    ensures
        res.len() == v.len(),
        forall|i| #![all_triggers] 0 <= i < v.len() ==> cloned::<T>(v[i], res[i]),
        vec_dequeue_clone_trigger(*v, res),
        v@ =~= res@ ==> v@ == res@,
;

pub assume_specification<T, A: Allocator>[ VecDeque::<T, A>::truncate ](
    v: &mut VecDeque<T, A>,
    len: usize,
)
    ensures
        len <= old(v).len() ==> v@ == old(v)@.subrange(0, len as int),
        len > old(v).len() ==> v@ == old(v)@,
;

pub assume_specification<T: Clone, A: Allocator>[ VecDeque::<T, A>::resize ](
    v: &mut VecDeque<T, A>,
    len: usize,
    value: T,
)
    ensures
        len <= old(v).len() ==> v@ == old(v)@.subrange(0, len as int),
        len > old(v).len() ==> {
            &&& v@.len() == len
            &&& v@.subrange(0, old(v).len() as int) == old(v)@
            &&& forall|i| #![all_triggers] old(v).len() <= i < len ==> cloned::<T>(value, v@[i])
        },
;

pub broadcast proof fn axiom_vec_dequeue_index_decreases<A>(v: VecDeque<A>, i: int)
    requires
        0 <= i < v.len(),
    ensures
        #[trigger] (decreases_to!(v => v[i])),
{
    admit();
}

// The `iter` method of a `VecDeque` returns an iterator of type `Iter`,
// so we specify that type here.
#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::accept_recursive_types(T)]
pub struct ExIter<'a, T: 'a>(Iter<'a, T>);

pub trait IterAdditionalSpecFns<'a, T: 'a> {
    spec fn view(self: &Self) -> (int, Seq<T>);
}

impl<'a, T: 'a> IterAdditionalSpecFns<'a, T> for Iter<'a, T> {
    uninterp spec fn view(self: &Iter<'a, T>) -> (int, Seq<T>);
}

pub assume_specification<'a, T>[ Iter::<'a, T>::next ](elements: &mut Iter<'a, T>) -> (r: Option<
    &'a T,
>)
    ensures
        ({
            let (old_index, old_seq) = old(elements)@;
            match r {
                None => {
                    &&& elements@ == old(elements)@
                    &&& old_index >= old_seq.len()
                },
                Some(element) => {
                    let (new_index, new_seq) = elements@;
                    &&& 0 <= old_index < old_seq.len()
                    &&& new_seq == old_seq
                    &&& new_index == old_index + 1
                    &&& element == old_seq[old_index]
                },
            }
        }),
;

pub struct IterGhostIterator<'a, T> {
    pub pos: int,
    pub elements: Seq<T>,
    pub phantom: Option<&'a T>,
}

impl<'a, T> super::super::pervasive::ForLoopGhostIteratorNew for Iter<'a, T> {
    type GhostIter = IterGhostIterator<'a, T>;

    open spec fn ghost_iter(&self) -> IterGhostIterator<'a, T> {
        IterGhostIterator { pos: self@.0, elements: self@.1, phantom: None }
    }
}

impl<'a, T: 'a> super::super::pervasive::ForLoopGhostIterator for IterGhostIterator<'a, T> {
    type ExecIter = Iter<'a, T>;

    type Item = T;

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

    open spec fn ghost_peek_next(&self) -> Option<T> {
        if 0 <= self.pos < self.elements.len() {
            Some(self.elements[self.pos])
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

// To allow reasoning about the ghost iterator when the executable
// function `iter()` is invoked in a `for` loop header (e.g., in
// `for x in it: v.iter() { ... }`), we need to specify the behavior of
// the iterator in spec mode. To do that, we add
// `#[verifier::when_used_as_spec(spec_iter)` to the specification for
// the executable `iter` method and define that spec function here.
pub uninterp spec fn spec_iter<'a, T, A: Allocator>(v: &'a VecDeque<T, A>) -> (r: Iter<'a, T>);

pub broadcast proof fn axiom_spec_iter<'a, T, A: Allocator>(v: &'a VecDeque<T, A>)
    ensures
        (#[trigger] spec_iter(v))@ == (0int, v@),
{
    admit();
}

#[verifier::when_used_as_spec(spec_iter)]
pub assume_specification<'a, T, A: Allocator>[ VecDeque::<T, A>::iter ](
    v: &'a VecDeque<T, A>,
) -> (r: Iter<'a, T>)
    ensures
        r@ == (0int, v@),
;

pub broadcast group group_vec_dequeue_axioms {
    axiom_spec_len,
    axiom_vec_dequeue_index_decreases,
    axiom_spec_iter,
}

} // verus!
