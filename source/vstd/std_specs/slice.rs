use super::super::prelude::*;
use super::core::IndexSetTrustedSpec;
use super::core::TrustedSpecSealed;
use super::super::utf8::{is_char_boundary};

#[cfg(not(verus_verify_core))]
use super::super::string::StringSliceAdditionalSpecFns;

use core::slice::Iter;
use core::ops::{Range, RangeFrom, RangeFull, RangeInclusive, RangeTo, RangeToInclusive};

use verus as verus_;

verus_! {

impl<T, const N: usize> TrustedSpecSealed for [T; N] {}

impl<T, const N: usize> IndexSetTrustedSpec<usize> for [T; N] {
    open spec fn spec_index_set_requires(&self, index: usize) -> bool {
        0 <= index < N
    }

    open spec fn spec_index_set_ensures(&self, new_container: &Self, index: usize, val: T) -> bool {
        new_container@ === self@.update(index as int, val)
    }
}

impl<T> TrustedSpecSealed for [T] {}

impl<T> IndexSetTrustedSpec<usize> for [T] {
    open spec fn spec_index_set_requires(&self, index: usize) -> bool {
        0 <= index < self@.len()
    }

    open spec fn spec_index_set_ensures(&self, new_container: &Self, index: usize, val: T) -> bool {
        new_container@ == self@.update(index as int, val)
    }
}

pub assume_specification[ core::hint::unreachable_unchecked ]() -> !
    requires
        false,
;

/* SliceIndex */

/// Precondition on the "sliced" data for `SliceIndex` functions.
// Currently, this is only used for asserting the valid UTF-8 invariant on `str` within the Rust standard library.
// In vstd, this property is assumed to hold for `str`, so this is trivial.
pub uninterp spec fn valid_slice<T: ?Sized>(slice: &T) -> bool;

pub broadcast axiom fn valid_slice_slice<T>(slice: &[T])
    ensures
        #[trigger] valid_slice(slice);

#[cfg(not(verus_verify_core))]
pub broadcast axiom fn valid_slice_str(slice: &str)
    ensures
        #[trigger] valid_slice(slice);

/// True when the indices `start` and `end` (exclusive) are considered valid indices for `slice`.
pub uninterp spec fn in_bounds<T: ?Sized>(start: int, end: int, slice: &T) -> bool;

pub broadcast axiom fn in_bounds_slice<T>(start: int, end: int, slice: &[T])
    ensures
        start <= slice@.len() <= end ==> #[trigger] in_bounds(start, end, slice);

#[cfg(not(verus_verify_core))]
pub broadcast axiom fn in_bounds_str(start: int, end: int, slice: &str)
    ensures
        start <= slice.spec_bytes().len() <= end && is_char_boundary(slice.spec_bytes(), start) && is_char_boundary(slice.spec_bytes(), end) ==> #[trigger] in_bounds(start, end, slice);

/// True when `output` matches the result of the slicing `slice` from `start` to `end` (exclusive) indices.
// This is written as a relation because `Output` is an exec type (e.g. [T]), and so we cannot necessarily return it from a spec function.
pub uninterp spec fn index_result<T: ?Sized, Output: ?Sized>(start: int, end: int, slice: &T, output: &Output) -> bool;

pub broadcast axiom fn index_result_slice<T>(start: int, end: int, slice: &[T], output: &[T])
    ensures
        #[trigger] index_result::<[T], [T]>(start, end, slice, output) <==> output@ =~= slice@.subrange(start, end);

#[cfg(not(verus_verify_core))]
pub broadcast axiom fn index_result_str(start: int, end: int, slice: &str, output: &str)
    ensures
        #[trigger] index_result::<str, str>(start, end, slice, output) <==> output@ == slice@.subrange(start, end);

#[verifier::external_trait_specification]
#[verifier::external_trait_extension(SliceIndexSpec via SliceIndexSpecImpl)]
pub trait ExSliceIndex<T> where T: ?Sized {
    type ExternalTraitSpecificationFor: core::slice::SliceIndex<T>;

    type Output: ?Sized;

    /// Start index of this slice index on the given slice.
    spec fn spec_start(&self, slice: &T) -> int;

    /// End index (exclusive) of this slice index on the given slice.
    spec fn spec_end(&self, slice: &T) -> int;

    fn get(self, slice: &T) -> (out: Option<&Self::Output>)
        requires
            valid_slice::<T>(slice),
        ensures
            out.is_some() <==> in_bounds(self.spec_start(slice), self.spec_end(slice), slice),
            out.is_some() ==> index_result(self.spec_start(slice), self.spec_end(slice), slice, out.unwrap())
    ;

    #[verifier::ignore_outside_new_mut_ref_experiment]
    fn get_mut(self, slice: &mut T) -> (out: Option<&mut Self::Output>)
        requires
            valid_slice::<T>(old(slice)),
        ensures
            &*old(slice) == &*final(slice),
            out.is_some() <==> in_bounds(self.spec_start(final(slice)), self.spec_end(final(slice)), final(slice)),
            out.is_some() ==> index_result(self.spec_start(final(slice)), self.spec_end(final(slice)), final(slice), out.unwrap())
    ;

    fn index(self, slice: &T) -> (out: &Self::Output)
        requires
            valid_slice::<T>(slice),
            in_bounds(self.spec_start(slice), self.spec_end(slice), slice)
        ensures
            index_result(self.spec_start(slice), self.spec_end(slice), slice, out)
        ;

    #[verifier::ignore_outside_new_mut_ref_experiment]
    fn index_mut(self, slice: &mut T) -> (out: &mut Self::Output)
        requires
            valid_slice::<T>(old(slice)),
            in_bounds(self.spec_start(old(slice)), self.spec_end(old(slice)), old(slice))
        ensures
            &*old(slice) == &*final(slice),
            index_result(self.spec_start(final(slice)), self.spec_end(final(slice)), final(slice), out)
        ;
}

impl<T> SliceIndexSpecImpl<[T]> for usize {
    open spec fn spec_start(&self, slice: &[T]) -> int {
        self as int
    }
    open spec fn spec_end(&self, slice: &[T]) -> int {
        self as int
    }
}
// describes range: start..end
impl<T> SliceIndexSpecImpl<[T]> for Range<usize> {
    open spec fn spec_start(&self, slice: &[T]) -> int {
        self.start as int
    }

    open spec fn spec_end(&self, slice: &[T]) -> int {
        self.end as int
    }
}
// describes range: start..
impl<T> SliceIndexSpecImpl<[T]> for RangeFrom<usize> {
    open spec fn spec_start(&self, slice: &[T]) -> int {
        self.start as int
    }

    open spec fn spec_end(&self, slice: &[T]) -> int {
        slice@.len() as int
    }
}
// describes full range: ..
impl<T> SliceIndexSpecImpl<[T]> for RangeFull {
    open spec fn spec_start(&self, slice: &[T]) -> int {
        0
    }

    open spec fn spec_end(&self, slice: &[T]) -> int {
        slice@.len() as int
    }
}
// describes range: start..=end
impl<T> SliceIndexSpecImpl<[T]> for RangeInclusive<usize> {
    open spec fn spec_start(&self, slice: &[T]) -> int {
        self@.start as int
    }

    open spec fn spec_end(&self, slice: &[T]) -> int {
        self@.end as int + 1
    }
}
// describes range: ..end
impl<T> SliceIndexSpecImpl<[T]> for RangeTo<usize> {
    open spec fn spec_start(&self, slice: &[T]) -> int {
        0
    }

    open spec fn spec_end(&self, slice: &[T]) -> int {
        self.end as int
    }
}
// describes range: ..=end
impl<T> SliceIndexSpecImpl<[T]> for RangeToInclusive<usize> {
    open spec fn spec_start(&self, slice: &[T]) -> int {
        0
    }

    open spec fn spec_end(&self, slice: &[T]) -> int {
        self.end as int + 1
    }
}
// describes range: start..end
impl SliceIndexSpecImpl<str> for Range<usize> {
    open spec fn spec_start(&self, slice: &str) -> int {
        self.start as int
    }

    open spec fn spec_end(&self, slice: &str) -> int {
        self.end as int
    }
}
// describes range: start..
impl SliceIndexSpecImpl<str> for RangeFrom<usize> {
    open spec fn spec_start(&self, slice: &str) -> int {
        self.start as int
    }

    open spec fn spec_end(&self, slice: &str) -> int {
        slice@.len() as int
    }
}
// describes full range: ..
impl SliceIndexSpecImpl<str> for RangeFull {
    open spec fn spec_start(&self, slice: &str) -> int {
        0
    }

    open spec fn spec_end(&self, slice: &str) -> int {
        slice@.len() as int
    }
}
// describes range: start..=end
impl SliceIndexSpecImpl<str> for RangeInclusive<usize> {
    open spec fn spec_start(&self, slice: &str) -> int {
        self@.start as int
    }

    open spec fn spec_end(&self, slice: &str) -> int {
        self@.end as int + 1
    }
}
// describes range: ..end
impl SliceIndexSpecImpl<str> for RangeTo<usize> {
    open spec fn spec_start(&self, slice: &str) -> int {
        0
    }

    open spec fn spec_end(&self, slice: &str) -> int {
        self.end as int
    }
}
// describes range: ..=end
impl SliceIndexSpecImpl<str> for RangeToInclusive<usize> {
    open spec fn spec_start(&self, slice: &str) -> int {
        0
    }

    open spec fn spec_end(&self, slice: &str) -> int {
        self.end as int + 1
    }
}

#[cfg(not(verus_verify_core))]
pub broadcast group group_slice_index_specs {
    valid_slice_slice,
    valid_slice_str,
    in_bounds_slice,
    in_bounds_str,
    index_result_slice,
    index_result_str
}

#[cfg(verus_verify_core)]
pub broadcast group group_slice_index_specs {
    valid_slice_slice,
    in_bounds_slice,
    index_result_slice,
}

// The `iter` method of a `<T>` returns an iterator of type `Iter<'_, T>`,
// so we specify that type here.
#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::accept_recursive_types(T)]
pub struct ExIter<'a, T: 'a>(Iter<'a, T>);

impl<T> View for Iter<'_, T> {
    type V = (int, Seq<T>);

    uninterp spec fn view(&self) -> (int, Seq<T>);
}

impl<T: DeepView> DeepView for Iter<'_, T> {
    type V = (int, Seq<T::V>);

    open spec fn deep_view(&self) -> Self::V {
        let (i, v) = self@;
        (i, Seq::new(v.len(), |i: int| v[i].deep_view()))
    }
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
// `for x in it: s.iter() { ... }`), we need to specify the behavior of
// the iterator in spec mode. To do that, we add
// `#[verifier::when_used_as_spec(spec_slice_iter)` to the specification for
// the executable `into_iter` method and define that spec function here.
pub uninterp spec fn spec_slice_iter<'a, T>(s: &'a [T]) -> (iter: Iter<'a, T>);

pub broadcast proof fn axiom_spec_slice_iter<'a, T>(s: &'a [T])
    ensures
        (#[trigger] spec_slice_iter(s))@ == (0int, s@),
{
    admit();
}

#[verifier::when_used_as_spec(spec_slice_iter)]
pub assume_specification<'a, T>[ <[T]>::iter ](s: &'a [T]) -> (iter: Iter<'a, T>)
    ensures
        ({
            let (index, seq) = iter@;
            &&& index == 0
            &&& seq == s@
        }),
;

pub assume_specification<T> [ <[T]>::first ](slice: &[T]) -> (res: Option<&T>)
    ensures
        slice.len() == 0 ==> res.is_none(),
        slice.len() != 0 ==> res.is_some() && res.unwrap() == slice[0]
;

pub assume_specification<T> [ <[T]>::last ](slice: &[T]) -> (res: Option<&T>)
    ensures
        slice.len() == 0 ==> res.is_none(),
        slice.len() != 0 ==> res.is_some() && res.unwrap() == slice@.last()
;

#[doc(hidden)]
#[verifier::ignore_outside_new_mut_ref_experiment]
pub assume_specification<T> [ <[T]>::first_mut ](slice: &mut [T]) -> (res: Option<&mut T>)
    ensures
        old(slice).len() == 0 ==> res.is_none() && final(slice)@ === seq![],
        old(slice).len() != 0 ==> res.is_some() && *res.unwrap() == old(slice)[0]
            && final(slice)@ === old(slice)@.update(0, *final(res.unwrap()))
;

#[doc(hidden)]
#[verifier::ignore_outside_new_mut_ref_experiment]
pub assume_specification<T> [ <[T]>::last_mut ](slice: &mut [T]) -> (res: Option<&mut T>)
    ensures
        old(slice).len() == 0 ==> res.is_none() && final(slice)@ === seq![],
        old(slice).len() != 0 ==> res.is_some() && *res.unwrap() == old(slice)@.last()
            && final(slice)@ === old(slice)@.update(old(slice).len() - 1, *final(res.unwrap()))
;

pub assume_specification<T> [ <[T]>::split_at ](slice: &[T], mid: usize) -> (ret: (&[T], &[T]))
    requires
        0 <= mid <= slice.len(),
    ensures
        ret.0@ == slice@.subrange(0, mid as int),
        ret.1@ == slice@.subrange(mid as int, slice@.len() as int),
;

#[doc(hidden)]
#[verifier::ignore_outside_new_mut_ref_experiment]
pub assume_specification<T> [ <[T]>::split_at_mut ](slice: &mut [T], mid: usize) -> (ret: (&mut [T], &mut [T]))
    requires
        0 <= mid <= slice.len(),
    ensures
        ret.0@ == old(slice)@.subrange(0, mid as int),
        ret.1@ == old(slice)@.subrange(mid as int, old(slice)@.len() as int),
        final(slice)@ == final(ret.0)@ + final(ret.1)@,
;

pub broadcast group group_slice_axioms {
    axiom_spec_slice_iter,
}

} // verus!
