use super::super::prelude::*;
use super::super::slice::{SliceIndexSpec, spec_slice_get};
use super::core::IndexSpec;
use super::iter::IteratorSpec;
use super::range::{slice_range_end, slice_range_start, slice_range_valid};

use core::ops::{
    Index, IndexMut, Range, RangeFrom, RangeFull, RangeInclusive, RangeTo, RangeToInclusive,
};
use core::slice::{Iter, SliceIndex};

use verus as verus_;

verus_! {

impl<T> super::super::slice::SliceIndexSpecImpl<[T]> for usize {
    open spec fn index_req(&self, slice: &[T]) -> bool {
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
    open spec fn index_req(&self, slice: &[T]) -> bool {
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
        final(slice)@ == old(slice)@.subrange(0, i.start as int) + final(r)@ + old(slice)@.subrange(
            i.end as int,
            old(slice)@.len() as int,
        ),
;

impl<T> super::super::slice::SliceIndexSpecImpl<[T]> for RangeTo<usize> {
    open spec fn index_req(&self, slice: &[T]) -> bool {
        self.end <= slice@.len()
    }
}

pub assume_specification<T>[ <RangeTo<usize> as SliceIndex<[T]>>::index ](i: RangeTo<usize>, slice: &[T]) -> (r: &[T])
    ensures
        r@ == slice@.subrange(0, i.end as int),
;

pub assume_specification<T>[ <RangeTo<usize> as SliceIndex<[T]>>::index_mut ](i: RangeTo<usize>, slice: &mut [T]) -> (r: &mut [T])
    ensures
        r@ == old(slice)@.subrange(0, i.end as int),
        final(r)@ == final(slice)@.subrange(0, i.end as int),
        final(slice)@ == final(r)@ + old(slice)@.subrange(i.end as int, old(slice)@.len() as int),
;

impl<T> super::super::slice::SliceIndexSpecImpl<[T]> for RangeFrom<usize> {
    open spec fn index_req(&self, slice: &[T]) -> bool {
        self.start <= slice@.len()
    }
}

pub assume_specification<T>[ <RangeFrom<usize> as SliceIndex<[T]>>::index ](i: RangeFrom<usize>, slice: &[T]) -> (r: &[T])
    ensures
        r@ == slice@.subrange(i.start as int, slice@.len() as int),
;

pub assume_specification<T>[ <RangeFrom<usize> as SliceIndex<[T]>>::index_mut ](i: RangeFrom<usize>, slice: &mut [T]) -> (r: &mut [T])
    ensures
        r@ == old(slice)@.subrange(i.start as int, old(slice)@.len() as int),
        final(r)@ == final(slice)@.subrange(i.start as int, old(slice)@.len() as int),
        final(slice)@ == old(slice)@.subrange(0, i.start as int) + final(r)@,
;

impl<T> super::super::slice::SliceIndexSpecImpl<[T]> for RangeToInclusive<usize> {
    open spec fn index_req(&self, slice: &[T]) -> bool {
        self.end < slice@.len()
    }
}

pub assume_specification<T>[ <RangeToInclusive<usize> as SliceIndex<[T]>>::index ](i: RangeToInclusive<usize>, slice: &[T]) -> (r: &[T])
    ensures
        r@ == slice@.subrange(0, i.end as int + 1),
;

pub assume_specification<T>[ <RangeToInclusive<usize> as SliceIndex<[T]>>::index_mut ](i: RangeToInclusive<usize>, slice: &mut [T]) -> (r: &mut [T])
    ensures
        r@ == old(slice)@.subrange(0, i.end as int + 1),
        final(r)@ == final(slice)@.subrange(0, i.end as int + 1),
        final(slice)@ == final(r)@ + old(slice)@.subrange(i.end as int + 1, old(slice)@.len() as int),
;

impl<T> super::super::slice::SliceIndexSpecImpl<[T]> for RangeFull {
    open spec fn index_req(&self, slice: &[T]) -> bool {
        true
    }
}

pub assume_specification<T>[ <RangeFull as SliceIndex<[T]>>::index ](i: RangeFull, slice: &[T]) -> (r: &[T])
    ensures
        r@ == slice@,
;

pub assume_specification<T>[ <RangeFull as SliceIndex<[T]>>::index_mut ](i: RangeFull, slice: &mut [T]) -> (r: &mut [T])
    ensures
        r@ == old(slice)@,
        final(slice)@ == final(r)@,
;

impl<T> super::super::slice::SliceIndexSpecImpl<[T]> for RangeInclusive<usize> {
    open spec fn index_req(&self, slice: &[T]) -> bool {
        slice_range_valid(self, slice@.len())
    }
}

pub assume_specification<T>[ <RangeInclusive<usize> as SliceIndex<[T]>>::index ](i: RangeInclusive<usize>, slice: &[T]) -> (r: &[T])
    ensures
        r@ == slice@.subrange(slice_range_start(&i), slice_range_end(&i, slice@.len() as nat)),
;

pub assume_specification<T>[ <RangeInclusive<usize> as SliceIndex<[T]>>::index_mut ](i: RangeInclusive<usize>, slice: &mut [T]) -> (r: &mut [T])
    ensures
        r@ == old(slice)@.subrange(
            slice_range_start(&i),
            slice_range_end(&i, old(slice)@.len() as nat),
        ),
        final(r)@ == final(slice)@.subrange(
            slice_range_start(&i),
            slice_range_end(&i, old(slice)@.len() as nat),
        ),
        final(slice)@ == old(slice)@.subrange(0, slice_range_start(&i)) + final(r)@
            + old(slice)@.subrange(
                slice_range_end(&i, old(slice)@.len() as nat),
                old(slice)@.len() as int,
            ),
;

pub broadcast axiom fn axiom_slice_get_range<T>(v: &[T], i: Range<usize>)
    ensures
        i.start <= i.end <= v@.len() ==> {
            &&& (#[trigger] spec_slice_get(v, i)).is_some()
            &&& spec_slice_get(v, i).unwrap()@ == v@.subrange(i.start as int, i.end as int)
        },
        !(i.start <= i.end <= v@.len()) ==> spec_slice_get(v, i).is_none(),
;

pub broadcast axiom fn axiom_slice_get_range_to<T>(v: &[T], i: RangeTo<usize>)
    ensures
        i.end <= v@.len() ==> {
            &&& (#[trigger] spec_slice_get(v, i)).is_some()
            &&& spec_slice_get(v, i).unwrap()@ == v@.subrange(0, i.end as int)
        },
        !(i.end <= v@.len()) ==> spec_slice_get(v, i).is_none(),
;

pub broadcast axiom fn axiom_slice_get_range_from<T>(v: &[T], i: RangeFrom<usize>)
    ensures
        i.start <= v@.len() ==> {
            &&& (#[trigger] spec_slice_get(v, i)).is_some()
            &&& spec_slice_get(v, i).unwrap()@ == v@.subrange(i.start as int, v@.len() as int)
        },
        !(i.start <= v@.len()) ==> spec_slice_get(v, i).is_none(),
;

pub broadcast axiom fn axiom_slice_get_range_to_inclusive<T>(v: &[T], i: RangeToInclusive<usize>)
    ensures
        i.end < v@.len() ==> {
            &&& (#[trigger] spec_slice_get(v, i)).is_some()
            &&& spec_slice_get(v, i).unwrap()@ == v@.subrange(0, i.end as int + 1)
        },
        !(i.end < v@.len()) ==> spec_slice_get(v, i).is_none(),
;

pub broadcast axiom fn axiom_slice_get_range_full<T>(v: &[T], i: RangeFull)
    ensures
        (#[trigger] spec_slice_get(v, i)).is_some(),
        spec_slice_get(v, i).unwrap()@ == v@,
;

pub broadcast axiom fn axiom_slice_get_range_inclusive<T>(v: &[T], i: RangeInclusive<usize>)
    ensures
        slice_range_valid(&i, v@.len()) ==> {
            &&& (#[trigger] spec_slice_get(v, i)).is_some()
            &&& spec_slice_get(v, i).unwrap()@ == v@.subrange(
                slice_range_start(&i),
                slice_range_end(&i, v@.len()),
            )
        },
        !slice_range_valid(&i, v@.len()) ==> spec_slice_get(v, i).is_none(),
;

impl<T, I: SliceIndex<[T]>> super::core::IndexSpecImpl<I> for [T] {
    open spec fn index_req(&self, index: &I) -> bool {
        index.index_req(self)
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

pub broadcast group group_slice_axioms {
    axiom_slice_get_range,
    axiom_slice_get_range_to,
    axiom_slice_get_range_from,
    axiom_slice_get_range_to_inclusive,
    axiom_slice_get_range_full,
    axiom_slice_get_range_inclusive,
}

} // verus!
