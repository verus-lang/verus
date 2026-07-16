use super::super::prelude::*;
use super::super::slice::SliceIndexSpec;
use super::core::IndexSpec;
use super::iter::IteratorSpec;
use super::range::{slice_range_end, slice_range_start, slice_range_valid};

use core::ops::{Index, IndexMut, Range};
use core::slice::{Iter, SliceIndex};

use verus as verus_;

verus_! {

impl<T> super::super::slice::SliceIndexSpecImpl<[T]> for usize {
    open spec fn index_requires(&self, slice: &[T]) -> bool {
        *self < slice@.len()
    }
}

pub assume_specification<T>[ <usize as SliceIndex<[T]>>::index ](i: usize, slice: &[T]) -> &T
    returns
        slice@[i as int],
;

pub assume_specification<T>[ <usize as SliceIndex<[T]>>::index_mut ](i: usize, slice: &mut [T]) -> (output: &mut T)
    ensures
        *output == old(slice)@[i as int],
        final(slice)@ == old(slice)@.update(i as int, *final(output))
;

impl<T> super::super::slice::SliceIndexSpecImpl<[T]> for Range<usize> {
    open spec fn index_requires(&self, slice: &[T]) -> bool {
        &&& self.start <= self.end
        &&& self.end <= slice@.len()
    }
}

pub assume_specification<T>[ <Range<usize> as SliceIndex<[T]>>::index ](i: Range<usize>, slice: &[T]) -> (r: &[T])
    ensures
        r@ == slice@.subrange(i.start as int, i.end as int),
;

pub assume_specification<T>[ <Range<usize> as SliceIndex<[T]>>::index_mut ](i: Range<usize>, slice: &mut [T]) -> (r: &mut [T])
    ensures
        r@ == old(slice)@.subrange(i.start as int, i.end as int),
        final(r)@ == final(slice)@.subrange(i.start as int, i.end as int),
        forall|j: int| !(i.start <= j < i.end) ==> final(slice)@[j] == old(slice)@[j],
;

impl<T, I: SliceIndex<[T]>> super::core::IndexSpecImpl<I> for [T] {
    open spec fn index_requires(&self, index: &I) -> bool {
        index.index_requires(self)
    }
}

pub assume_specification<T, I: SliceIndex<[T]>>[ <[T] as Index<I>>::index ](
    slice: &[T],
    index: I,
) -> (output: &<I as SliceIndex<[T]>>::Output)
    ensures
        call_ensures(<I as SliceIndex<[T]>>::index, (index, slice), output),
;

pub assume_specification<T, I: SliceIndex<[T]>>[ <[T] as IndexMut<I>>::index_mut ](
    slice: &mut [T],
    index: I,
) -> (output: &mut <I as SliceIndex<[T]>>::Output)
    ensures
        call_ensures(<I as SliceIndex<[T]>>::index_mut, (index, slice), output),
;

impl<T, I, const N: usize> super::core::IndexSpecImpl<I> for [T; N]
where
    [T]: Index<I>,
{
    open spec fn index_requires(&self, index: &I) -> bool {
        <[T] as IndexSpec<I>>::index_requires(self, index)
    }
}

pub assume_specification<T, I, const N: usize>[ <[T; N]>::index ](array: &[T; N], index: I) -> (output: &<[T; N] as Index<I>>::Output)
    where
        [T]: Index<I>,
    ensures
        call_ensures(<[T]>::index, (array, index), output),
;

pub assume_specification<T, I, const N: usize>[ <[T; N]>::index_mut ](array: &mut [T; N], index: I) -> (output: &mut <[T; N] as Index<I>>::Output)
    where
        [T]: IndexMut<I>,
    ensures
        forall|slice: &mut [T]| #![trigger slice@] {
            &&& slice@ == old(array)@
            &&& final(slice)@ == final(array)@
        } ==> call_ensures(<[T]>::index_mut, (slice, index), output),
;

pub assume_specification[ core::hint::unreachable_unchecked ]() -> !
    requires
        false,
;

// The `iter` method of a `<T>` returns an iterator of type `Iter<'_, T>`,
// so we specify that type here.
#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::accept_recursive_types(T)]
pub struct ExIter<'a, T: 'a>(Iter<'a, T>);

// To allow reasoning about the "contents" of the slice iterator, without using
// a prophecy, we need a function that gives us the underlying sequence of the original slice.
pub uninterp spec fn into_iter_elts<'a, T: 'a>(i: Iter<'a, T>) -> Seq<T>;

impl <'a, T: 'a> super::iter::IteratorSpecImpl for Iter<'a, T> {
    open spec fn obeys_prophetic_iter_laws(&self) -> bool {
        true
    }

    uninterp spec fn remaining(&self) -> Seq<Self::Item>;
    uninterp spec fn will_return_none(&self) -> bool;

    #[verifier::prophetic]
    open spec fn initial_value_relation(&self, init: &Self) -> bool {
        &&& IteratorSpec::remaining(init) == IteratorSpec::remaining(self)
        &&& into_iter_elts(*self) == IteratorSpec::remaining(self).unref()
    }

    uninterp spec fn decrease(&self) -> Option<nat>;

    open spec fn peek(&self, index: int) -> Option<Self::Item> {
        if 0 <= index < into_iter_elts(*self).len() {
            Some(&into_iter_elts(*self)[index])
        } else {
            None
        }
    }
}


// To allow reasoning about the returned iterator when the executable
// function `iter()` is invoked in a `for` loop header (e.g., in
// `for x in it: s.iter() { ... }`), we need to specify the behavior of
// the iterator in spec mode. To do that, we add
// `#[verifier::when_used_as_spec(spec_slice_iter)` to the specification for
// the executable `into_iter` method and define that spec function here.
pub uninterp spec fn spec_slice_iter<'a, T>(s: &'a [T]) -> (iter: Iter<'a, T>);

pub broadcast proof fn axiom_spec_slice_iter<'a, T>(s: &'a [T])
    ensures
        #[trigger] spec_slice_iter(s).remaining() == s@.as_ref(),
{
    admit();
}

#[verifier::when_used_as_spec(spec_slice_iter)]
pub assume_specification<'a, T>[ <[T]>::iter ](s: &'a [T]) -> (iter: Iter<'a, T>)
    ensures
        iter == spec_slice_iter(s),
        IteratorSpec::decrease(&iter) is Some,
        IteratorSpec::initial_value_relation(&iter, &iter),
;

#[verifier::when_used_as_spec(spec_slice_iter)]
pub assume_specification<'a, T> [<&'a [T] as core::iter::IntoIterator>::into_iter] (s: &'a [T]) ->
    (iter: Iter<'a, T>)
    ensures
        iter == spec_slice_iter(s),
        IteratorSpec::decrease(&iter) is Some,
        IteratorSpec::initial_value_relation(&iter, &iter),
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
pub assume_specification<T> [ <[T]>::first_mut ](slice: &mut [T]) -> (res: Option<&mut T>)
    ensures
        old(slice).len() == 0 ==> res.is_none() && final(slice)@ == seq![],
        old(slice).len() != 0 ==> res.is_some() && *res.unwrap() == old(slice)[0]
            && final(slice)@ == old(slice)@.update(0, *final(res.unwrap()))
;

#[doc(hidden)]
pub assume_specification<T> [ <[T]>::last_mut ](slice: &mut [T]) -> (res: Option<&mut T>)
    ensures
        old(slice).len() == 0 ==> res.is_none() && final(slice)@ == seq![],
        old(slice).len() != 0 ==> res.is_some() && *res.unwrap() == old(slice)@.last()
            && final(slice)@ == old(slice)@.update(old(slice).len() - 1, *final(res.unwrap()))
;

pub assume_specification<T> [ <[T]>::split_at ](slice: &[T], mid: usize) -> (ret: (&[T], &[T]))
    requires
        0 <= mid <= slice.len(),
    ensures
        ret.0@ == slice@.subrange(0, mid as int),
        ret.1@ == slice@.subrange(mid as int, slice@.len() as int),
;

#[doc(hidden)]
pub assume_specification<T> [ <[T]>::split_at_mut ](slice: &mut [T], mid: usize) -> (ret: (&mut [T], &mut [T]))
    requires
        0 <= mid <= slice.len(),
    ensures
        ret.0@ == old(slice)@.subrange(0, mid as int),
        ret.1@ == old(slice)@.subrange(mid as int, old(slice)@.len() as int),
        final(slice)@ == final(ret.0)@ + final(ret.1)@,
;

/// Copy the contents of `src` into `dst`, which must have the same length.
pub assume_specification<T: Copy>[ <[T]>::copy_from_slice ](dst: &mut [T], src: &[T])
    requires
        old(dst)@.len() == src@.len(),
    ensures
        final(dst)@ == src@,
;

/// The sequence resulting from copying `old_slice[src_start..src_end]` to start
/// at index `dest`, leaving all other positions unchanged. Reads are taken from
/// `old_slice`, so overlapping source and destination ranges are handled like
/// std's `<[T]>::copy_within` (which uses `ptr::copy`).
pub open spec fn copy_within_result<T>(
    old_slice: Seq<T>,
    src_start: int,
    src_end: int,
    dest: int,
) -> Seq<T> {
    let count = src_end - src_start;
    Seq::new(
        old_slice.len(),
        |i: int|
            if dest <= i && i < dest + count {
                old_slice[src_start + (i - dest)]
            } else {
                old_slice[i]
            },
    )
}

/// Copy the elements in range `src` within the slice to start at index `dest`.
pub assume_specification<T: Copy, R: core::ops::RangeBounds<usize>>[ <[T]>::copy_within::<R> ](
    slice: &mut [T],
    src: R,
    dest: usize,
)
    requires
        slice_range_valid(&src, old(slice)@.len()),
        (dest as int) + (slice_range_end(&src, old(slice)@.len()) - slice_range_start(&src))
            <= old(slice)@.len(),
    ensures
        final(slice)@ == copy_within_result(
            old(slice)@,
            slice_range_start(&src),
            slice_range_end(&src, old(slice)@.len()),
            dest as int,
        ),
;

pub broadcast group group_slice_axioms {
    axiom_spec_slice_iter,
}

} // verus!
