use super::super::prelude::*;
use super::super::slice::SliceIndexSpec;
use super::core::IndexSpec;
use super::iter::IteratorSpec;
use super::range::{
    ExRange, RangeBoundsSpec, slice_range_end, slice_range_start, slice_range_valid,
};

use core::ops::{
    Index, IndexMut, Range, RangeFrom, RangeFull, RangeInclusive, RangeTo, RangeToInclusive,
};
use core::slice::{Iter, SliceIndex};

use verus as verus_;

verus_! {

impl<T> super::super::slice::SliceIndexSpecImpl<[T]> for usize {
    open spec fn in_bounds(&self, slice: &[T]) -> bool {
        *self < slice@.len()
    }

    open spec fn index_postcondition(&self, slice: &[T], r: &T) -> bool {
        r == slice@[self as int]
    }

    open spec fn index_mut_postcondition(
        &self,
        old_slice: &[T],
        final_slice: &[T],
        immediate_output: &T,
        final_output: &T,
    ) -> bool {
        &&& *immediate_output == old_slice@[*self as int]
        &&& final_slice@ == old_slice@.update(*self as int, *final_output)
    }
}

pub assume_specification<T>[ <usize as SliceIndex<[T]>>::get ](i: usize, slice: &[T]) -> Option<&T>;

pub assume_specification<T>[ <usize as SliceIndex<[T]>>::index ](i: usize, slice: &[T]) -> &T
;

pub assume_specification<T>[ <usize as SliceIndex<[T]>>::get_mut ](i: usize, slice: &mut [T]) -> Option<&mut T>;

pub assume_specification<T>[ <usize as SliceIndex<[T]>>::index_mut ](i: usize, slice: &mut [T]) -> (output: &mut T)
;

pub open spec fn generic_slice_in_bounds<R: RangeBoundsSpec<usize>, T>(
    range: &R,
    s: Seq<T>
) -> bool {
    slice_range_valid(range, s.len())
}

pub open spec fn generic_slice_index_postcondition<R: RangeBoundsSpec<usize>, T>(
    range: &R,
    slice: Seq<T>,
    r: Seq<T>,
) -> bool {
    r == slice.subrange(slice_range_start(range), slice_range_end(range, slice.len()))
}

pub open spec fn generic_slice_index_mut_postcondition<R: RangeBoundsSpec<usize>, T>(
    range: &R,
    old_slice: Seq<T>,
    final_slice: Seq<T>,
    immediate_output: Seq<T>,
    final_output: Seq<T>,
) -> bool {
    &&& immediate_output == old_slice.subrange(slice_range_start(range), slice_range_end(range, old_slice.len()))
    &&& final_slice.len() == old_slice.len()
    &&& final_slice.subrange(0, slice_range_start(range)) == old_slice.subrange(0, slice_range_start(range))
    &&& final_slice.subrange(slice_range_start(range), slice_range_end(range, old_slice.len())) == final_output
    &&& final_slice.subrange(slice_range_end(range, old_slice.len()), old_slice.len() as int) ==
        old_slice.subrange(slice_range_end(range, old_slice.len()), old_slice.len() as int)
    // The following conjunct can be derived from the above four, but
    // it's useful to include anyway.
    &&& final_slice == old_slice.subrange(0, slice_range_start(range)) + final_output + old_slice.subrange(
           slice_range_end(range, old_slice.len()),
           old_slice.len() as int,
       )
}

impl<T> super::super::slice::SliceIndexSpecImpl<[T]> for Range<usize> {
    open spec fn in_bounds(&self, slice: &[T]) -> bool {
        generic_slice_in_bounds(self, slice@)
    }

    open spec fn index_postcondition(&self, slice: &[T], r: &[T]) -> bool {
        generic_slice_index_postcondition(self, slice@, r@)
    }

    open spec fn index_mut_postcondition(
        &self,
        old_slice: &[T],
        final_slice: &[T],
        immediate_output: &[T],
        final_output: &[T]
    ) -> bool {
        generic_slice_index_mut_postcondition(self, old_slice@, final_slice@, immediate_output@, final_output@)
    }
}

pub assume_specification<T>[ <Range<usize> as SliceIndex<[T]>>::get ](i: Range<usize>, slice: &[T]) -> Option<&[T]>;

pub assume_specification<T>[ <Range<usize> as SliceIndex<[T]>>::index ](i: Range<usize>, slice: &[T]) -> (r: &[T])
;

pub assume_specification<T>[ <Range<usize> as SliceIndex<[T]>>::get_mut ](i: Range<usize>, slice: &mut [T]) -> Option<&mut [T]>;

pub assume_specification<T>[ <Range<usize> as SliceIndex<[T]>>::index_mut ](i: Range<usize>, slice: &mut [T]) -> (r: &mut [T])
;

impl<T> super::super::slice::SliceIndexSpecImpl<[T]> for RangeTo<usize> {
    open spec fn in_bounds(&self, slice: &[T]) -> bool {
        generic_slice_in_bounds(self, slice@)
    }

    open spec fn index_postcondition(&self, slice: &[T], r: &[T]) -> bool {
        generic_slice_index_postcondition(self, slice@, r@)
    }

    open spec fn index_mut_postcondition(
        &self,
        old_slice: &[T],
        final_slice: &[T],
        immediate_output: &[T],
        final_output: &[T]
    ) -> bool {
        generic_slice_index_mut_postcondition(self, old_slice@, final_slice@, immediate_output@, final_output@)
    }
}

pub assume_specification<T>[ <RangeTo<usize> as SliceIndex<[T]>>::get ](i: RangeTo<usize>, slice: &[T]) -> Option<&[T]>;

pub assume_specification<T>[ <RangeTo<usize> as SliceIndex<[T]>>::index ](i: RangeTo<usize>, slice: &[T]) -> (r: &[T])
;

pub assume_specification<T>[ <RangeTo<usize> as SliceIndex<[T]>>::get_mut ](i: RangeTo<usize>, slice: &mut [T]) -> Option<&mut [T]>;

pub assume_specification<T>[ <RangeTo<usize> as SliceIndex<[T]>>::index_mut ](i: RangeTo<usize>, slice: &mut [T]) -> (r: &mut [T])
;

impl<T> super::super::slice::SliceIndexSpecImpl<[T]> for RangeFrom<usize> {
    open spec fn in_bounds(&self, slice: &[T]) -> bool {
        generic_slice_in_bounds(self, slice@)
    }

    open spec fn index_postcondition(&self, slice: &[T], r: &[T]) -> bool {
        generic_slice_index_postcondition(self, slice@, r@)
    }

    open spec fn index_mut_postcondition(
        &self,
        old_slice: &[T],
        final_slice: &[T],
        immediate_output: &[T],
        final_output: &[T]
    ) -> bool {
        generic_slice_index_mut_postcondition(self, old_slice@, final_slice@, immediate_output@, final_output@)
    }
}

pub assume_specification<T>[ <RangeFrom<usize> as SliceIndex<[T]>>::get ](i: RangeFrom<usize>, slice: &[T]) -> Option<&[T]>;

pub assume_specification<T>[ <RangeFrom<usize> as SliceIndex<[T]>>::index ](i: RangeFrom<usize>, slice: &[T]) -> (r: &[T])
;

pub assume_specification<T>[ <RangeFrom<usize> as SliceIndex<[T]>>::get_mut ](i: RangeFrom<usize>, slice: &mut [T]) -> Option<&mut [T]>;

pub assume_specification<T>[ <RangeFrom<usize> as SliceIndex<[T]>>::index_mut ](i: RangeFrom<usize>, slice: &mut [T]) -> (r: &mut [T])
;

impl<T> super::super::slice::SliceIndexSpecImpl<[T]> for RangeToInclusive<usize> {
    open spec fn in_bounds(&self, slice: &[T]) -> bool {
        generic_slice_in_bounds(self, slice@)
    }

    open spec fn index_postcondition(&self, slice: &[T], r: &[T]) -> bool {
        generic_slice_index_postcondition(self, slice@, r@)
    }

    open spec fn index_mut_postcondition(
        &self,
        old_slice: &[T],
        final_slice: &[T],
        immediate_output: &[T],
        final_output: &[T]
    ) -> bool {
        generic_slice_index_mut_postcondition(self, old_slice@, final_slice@, immediate_output@, final_output@)
    }
}

pub assume_specification<T>[ <RangeToInclusive<usize> as SliceIndex<[T]>>::get ](i: RangeToInclusive<usize>, slice: &[T]) -> Option<&[T]>;

pub assume_specification<T>[ <RangeToInclusive<usize> as SliceIndex<[T]>>::index ](i: RangeToInclusive<usize>, slice: &[T]) -> (r: &[T])
;

pub assume_specification<T>[ <RangeToInclusive<usize> as SliceIndex<[T]>>::get_mut ](i: RangeToInclusive<usize>, slice: &mut [T]) -> Option<&mut [T]>;

pub assume_specification<T>[ <RangeToInclusive<usize> as SliceIndex<[T]>>::index_mut ](i: RangeToInclusive<usize>, slice: &mut [T]) -> (r: &mut [T])
;

impl<T> super::super::slice::SliceIndexSpecImpl<[T]> for RangeFull {
    open spec fn in_bounds(&self, slice: &[T]) -> bool {
        generic_slice_in_bounds(self, slice@)
    }

    open spec fn index_postcondition(&self, slice: &[T], r: &[T]) -> bool {
        generic_slice_index_postcondition(self, slice@, r@)
    }

    open spec fn index_mut_postcondition(
        &self,
        old_slice: &[T],
        final_slice: &[T],
        immediate_output: &[T],
        final_output: &[T]
    ) -> bool {
        generic_slice_index_mut_postcondition(self, old_slice@, final_slice@, immediate_output@, final_output@)
    }
}

pub assume_specification<T>[ <RangeFull as SliceIndex<[T]>>::get ](i: RangeFull, slice: &[T]) -> Option<&[T]>;

pub assume_specification<T>[ <RangeFull as SliceIndex<[T]>>::index ](i: RangeFull, slice: &[T]) -> (r: &[T])
;

pub assume_specification<T>[ <RangeFull as SliceIndex<[T]>>::get_mut ](i: RangeFull, slice: &mut [T]) -> Option<&mut [T]>;

pub assume_specification<T>[ <RangeFull as SliceIndex<[T]>>::index_mut ](i: RangeFull, slice: &mut [T]) -> (r: &mut [T])
;

impl<T> super::super::slice::SliceIndexSpecImpl<[T]> for RangeInclusive<usize> {
    open spec fn in_bounds(&self, slice: &[T]) -> bool {
        generic_slice_in_bounds(self, slice@)
    }

    open spec fn index_postcondition(&self, slice: &[T], r: &[T]) -> bool {
        generic_slice_index_postcondition(self, slice@, r@)
    }

    open spec fn index_mut_postcondition(
        &self,
        old_slice: &[T],
        final_slice: &[T],
        immediate_output: &[T],
        final_output: &[T]
    ) -> bool {
        generic_slice_index_mut_postcondition(self, old_slice@, final_slice@, immediate_output@, final_output@)
    }
}

pub assume_specification<T>[ <RangeInclusive<usize> as SliceIndex<[T]>>::get ](i: RangeInclusive<usize>, slice: &[T]) -> Option<&[T]>;

pub assume_specification<T>[ <RangeInclusive<usize> as SliceIndex<[T]>>::index ](i: RangeInclusive<usize>, slice: &[T]) -> (r: &[T])
;

pub assume_specification<T>[ <RangeInclusive<usize> as SliceIndex<[T]>>::get_mut ](i: RangeInclusive<usize>, slice: &mut [T]) -> Option<&mut [T]>;

pub assume_specification<T>[ <RangeInclusive<usize> as SliceIndex<[T]>>::index_mut ](i: RangeInclusive<usize>, slice: &mut [T]) -> (r: &mut [T])
;

// starts_with
pub open spec fn spec_slice_starts_with<T: PartialEq>(slice: &[T], needle: &[T]) -> bool {
    &&& needle@.len() <= slice@.len()
    &&& forall|i: int| #![auto]
        0 <= i < needle@.len() ==>
            <T as super::cmp::PartialEqSpec<T>>::eq_spec(
                &slice@[i],
                &needle@[i],
            )
}

#[verifier::when_used_as_spec(spec_slice_starts_with)]
pub assume_specification<T: PartialEq>[ <[T]>::starts_with ](
    slice: &[T],
    needle: &[T],
) -> (result: bool)
    ensures
        needle@.len() > slice@.len() ==> !result,
        <T as super::cmp::PartialEqSpec<T>>::obeys_eq_spec() ==> (result == spec_slice_starts_with(
            slice,
            needle,
        )),
;

// ends_with
pub open spec fn spec_slice_ends_with<T: PartialEq>(slice: &[T], needle: &[T]) -> bool {
    &&& needle@.len() <= slice@.len()
    &&& forall|i: int| #![auto]
        0 <= i < needle@.len() ==>
            <T as super::cmp::PartialEqSpec<T>>::eq_spec(
                &slice@[slice@.len() - needle@.len() + i],
                &needle@[i],
            )
}

#[verifier::when_used_as_spec(spec_slice_ends_with)]
pub assume_specification<T: PartialEq>[ <[T]>::ends_with ](
    slice: &[T],
    needle: &[T],
) -> (result: bool)
    ensures
        needle@.len() > slice@.len() ==> !result,
        <T as super::cmp::PartialEqSpec<T>>::obeys_eq_spec() ==> (result == spec_slice_ends_with(
            slice,
            needle,
        )),
;

impl<T, I: SliceIndex<[T]>> super::core::IndexSpecImpl<I> for [T] {
    open spec fn index_req(&self, index: &I) -> bool {
        index.in_bounds(self)
    }
}

pub assume_specification<T, I>[ <[T]>::get::<I> ](slice: &[T], i: I) -> (b: Option<
    &<I as SliceIndex<[T]>>::Output,
>) where I: SliceIndex<[T]>
    ensures
        call_ensures(<I as SliceIndex<[T]>>::get, (i, slice), b),
;

pub assume_specification<T, I>[ <[T]>::get_mut::<I> ](slice: &mut [T], i: I) -> (b: Option<
    &mut <I as SliceIndex<[T]>>::Output,
>) where I: SliceIndex<[T]>
    ensures
        call_ensures(<I as SliceIndex<[T]>>::get_mut, (i, slice), b),
;

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
    open spec fn index_req(&self, index: &I) -> bool {
        <[T] as IndexSpec<I>>::index_req(self, index)
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
        exists|slice: &mut [T]| {
            &&& #[trigger] slice@ == old(array)@
            &&& final(slice)@ == final(array)@
            &&& call_ensures(<[T]>::index_mut, (slice, index), output)
        },
;

pub assume_specification[ core::hint::unreachable_unchecked ]() -> !
    requires
        false,
;

// slice == slice
pub assume_specification<T: PartialEq<U>, U>[ <[T] as PartialEq<[U]>>::eq ](
    left: &[T],
    right: &[U],
) -> bool
;

impl<T, U> super::cmp::PartialEqSpecImpl<[U]> for [T] where T: PartialEq<U> + super::cmp::PartialEqSpec<U> {
    open spec fn obeys_eq_spec() -> bool {
        <T as super::cmp::PartialEqSpec<U>>::obeys_eq_spec()
    }

    open spec fn eq_spec(&self, other: &[U]) -> bool {
        &&& self@.len() == other@.len()
        &&& forall|i: int|
            #![auto]
            0 <= i < self@.len() ==> <T as super::cmp::PartialEqSpec<U>>::eq_spec(&self@[i], &other@[i])
    }
}

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
    uninterp spec fn decrease(&self) -> Option<nat>;

    open spec fn peek(&self, index: int) -> Option<Self::Item> {
        if 0 <= index < into_iter_elts(*self).len() {
            Some(&into_iter_elts(*self)[index])
        } else {
            None
        }
    }
}

pub assume_specification<'a, T>[ <[T]>::iter ](s: &'a [T]) -> (iter: Iter<'a, T>)
    ensures
        IteratorSpec::remaining(&iter) == s@.as_ref(),
        into_iter_elts(iter) == IteratorSpec::remaining(&iter).unref(),
        IteratorSpec::decrease(&iter) is Some,
;

pub assume_specification<'a, T> [<&'a [T] as core::iter::IntoIterator>::into_iter] (s: &'a [T]) ->
    (iter: Iter<'a, T>)
    ensures
        IteratorSpec::remaining(&iter) == s@.as_ref(),
        into_iter_elts(iter) == IteratorSpec::remaining(&iter).unref(),
        IteratorSpec::decrease(&iter) is Some,
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

// The non-panicking (`Option`-returning) form of `split_at`: `Some((a, b))` split at `mid`
// when `mid <= len`, else `None`.
pub assume_specification<T> [ <[T]>::split_at_checked ](slice: &[T], mid: usize) -> (ret: Option<(&[T], &[T])>)
    ensures
        mid <= slice.len() ==> (ret matches Some((a, b))
            && a@ == slice@.subrange(0, mid as int)
            && b@ == slice@.subrange(mid as int, slice@.len() as int)),
        mid > slice.len() ==> ret is None,
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

} // verus!
