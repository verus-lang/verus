use super::super::prelude::*;
use super::super::slice::{SliceIndexSpec, spec_slice_get};
use super::core::IndexSpec;
use super::iter::IteratorSpec;
use super::range::{slice_range_end, slice_range_start, slice_range_valid};

use core::ops::{
    FnMut, Index, IndexMut, OneSidedRange, Range, RangeFrom, RangeFull, RangeInclusive, RangeTo,
    RangeToInclusive,
};
use core::slice::{
    Iter, RSplit, RSplitMut, RSplitN, RSplitNMut, SliceIndex, Split, SplitInclusive,
    SplitInclusiveMut, SplitMut, SplitN, SplitNMut,
};

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

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(T)]
#[verifier::reject_recursive_types(P)]
pub struct ExSplit<'a, T: 'a, P: FnMut(&T) -> bool>(Split<'a, T, P>);

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(T)]
#[verifier::reject_recursive_types(P)]
pub struct ExSplitMut<'a, T: 'a, P: FnMut(&T) -> bool>(SplitMut<'a, T, P>);

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(T)]
#[verifier::reject_recursive_types(P)]
pub struct ExSplitInclusive<'a, T: 'a, P: FnMut(&T) -> bool>(SplitInclusive<'a, T, P>);

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(T)]
#[verifier::reject_recursive_types(P)]
pub struct ExSplitInclusiveMut<'a, T: 'a, P: FnMut(&T) -> bool>(
    SplitInclusiveMut<'a, T, P>,
);

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(T)]
#[verifier::reject_recursive_types(P)]
pub struct ExSplitN<'a, T: 'a, P: FnMut(&T) -> bool>(SplitN<'a, T, P>);

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(T)]
#[verifier::reject_recursive_types(P)]
pub struct ExSplitNMut<'a, T: 'a, P: FnMut(&T) -> bool>(SplitNMut<'a, T, P>);

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(T)]
#[verifier::reject_recursive_types(P)]
pub struct ExRSplit<'a, T: 'a, P: FnMut(&T) -> bool>(RSplit<'a, T, P>);

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(T)]
#[verifier::reject_recursive_types(P)]
pub struct ExRSplitMut<'a, T: 'a, P: FnMut(&T) -> bool>(RSplitMut<'a, T, P>);

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(T)]
#[verifier::reject_recursive_types(P)]
pub struct ExRSplitN<'a, T: 'a, P: FnMut(&T) -> bool>(RSplitN<'a, T, P>);

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(T)]
#[verifier::reject_recursive_types(P)]
pub struct ExRSplitNMut<'a, T: 'a, P: FnMut(&T) -> bool>(RSplitNMut<'a, T, P>);

pub ghost struct SliceIteratorView<T> {
    pub source: Seq<T>,
    pub remaining: Seq<T>,
    pub yielded_prefix: Seq<T>,
    pub remainder: Seq<T>,
    pub chunk_size: int,
    pub reverse: bool,
}

pub uninterp spec fn slice_iterator_view<I, T>(iter: I) -> SliceIteratorView<T>;

pub open spec fn slice_iterator_well_formed<T>(view: SliceIteratorView<T>) -> bool {
    0 <= view.chunk_size && view.remainder.len() <= view.source.len()
}

pub broadcast axiom fn axiom_slice_iterator_view_well_formed<I, T>(iter: I)
    ensures
        slice_iterator_well_formed(#[trigger] slice_iterator_view::<I, T>(iter)),
;

pub uninterp spec fn fnmut_predicate_observed<F, T>(pred: F, value: T) -> bool;

pub open spec fn slice_predicate_split_view<I, F, T>(
    iter: I,
    source: Seq<T>,
    pred: F,
    inclusive: bool,
    reverse: bool,
    limit: int,
) -> bool {
    let view = slice_iterator_view::<I, T>(iter);
    slice_iterator_well_formed(view)
        && view.source == source
        && view.remaining == source
        && view.yielded_prefix == Seq::empty()
        && view.remainder == Seq::empty()
        && view.reverse == reverse
        && view.chunk_size == limit
        && limit >= 0
        && (if reverse {
            view.remaining + view.yielded_prefix == source
        } else {
            view.yielded_prefix + view.remaining == source
        })
        && forall|i: int| #![trigger fnmut_predicate_observed(pred, source[i])]
            0 <= i < source.len()
            ==> (fnmut_predicate_observed(pred, source[i])
                || !fnmut_predicate_observed(pred, source[i]))
}

pub open spec fn slice_split_off_partition<T>(
    source: Seq<T>,
    remaining: Seq<T>,
    removed: Seq<T>,
) -> bool {
    removed + remaining == source || remaining + removed == source
}

pub open spec fn slice_split_off_first_result<T>(
    source: Seq<T>,
    remaining: Seq<T>,
    value: T,
) -> bool {
    source.len() != 0 && value == source[0] && remaining == source.subrange(1, source.len() as int)
}

pub open spec fn slice_split_off_last_result<T>(
    source: Seq<T>,
    remaining: Seq<T>,
    value: T,
) -> bool {
    source.len() != 0
        && value == source[(source.len() - 1) as int]
        && remaining == source.subrange(0, (source.len() - 1) as int)
}

pub assume_specification<T>[ <[T]>::split_first ](
    slice: &[T],
) -> (ret: Option<(&T, &[T])>)
    ensures
        slice@.len() == 0 ==> ret.is_none(),
        slice@.len() != 0 ==> ret.is_some()
            && *ret.unwrap().0 == slice@[0]
            && ret.unwrap().1@ == slice@.subrange(1, slice@.len() as int),
;

pub assume_specification<T>[ <[T]>::split_last ](
    slice: &[T],
) -> (ret: Option<(&T, &[T])>)
    ensures
        slice@.len() == 0 ==> ret.is_none(),
        slice@.len() != 0 ==> ret.is_some()
            && *ret.unwrap().0 == slice@[(slice@.len() - 1) as int]
            && ret.unwrap().1@ == slice@.subrange(0, (slice@.len() - 1) as int),
;

pub assume_specification<T>[ <[T]>::split_first_mut ](
    slice: &mut [T],
) -> (ret: Option<(&mut T, &mut [T])>)
    ensures
        old(slice)@.len() == 0 ==> ret.is_none() && final(slice)@ == old(slice)@,
        old(slice)@.len() != 0 ==> ret.is_some()
            && *ret.unwrap().0 == old(slice)@[0]
            && ret.unwrap().1@ == old(slice)@.subrange(1, old(slice)@.len() as int)
            && final(slice)@ == seq![*final(ret.unwrap().0)] + final(ret.unwrap().1)@,
;

pub assume_specification<T>[ <[T]>::split_last_mut ](
    slice: &mut [T],
) -> (ret: Option<(&mut T, &mut [T])>)
    ensures
        old(slice)@.len() == 0 ==> ret.is_none() && final(slice)@ == old(slice)@,
        old(slice)@.len() != 0 ==> ret.is_some()
            && *ret.unwrap().0 == old(slice)@[(old(slice)@.len() - 1) as int]
            && ret.unwrap().1@ == old(slice)@.subrange(0, (old(slice)@.len() - 1) as int)
            && final(slice)@ == final(ret.unwrap().1)@ + seq![*final(ret.unwrap().0)],
;

pub assume_specification<'a, T, F: FnMut(&T) -> bool>[ <[T]>::split::<F> ](
    slice: &'a [T],
    pred: F,
) -> (iter: Split<'a, T, F>)
    ensures
        slice_predicate_split_view::<Split<'a, T, F>, F, T>(
            iter, slice@, pred, false, false, 0,
        ),
;

pub assume_specification<'a, T, F: FnMut(&T) -> bool>[ <[T]>::split_mut::<F> ](
    slice: &'a mut [T],
    pred: F,
) -> (iter: SplitMut<'a, T, F>)
    ensures
        slice_predicate_split_view::<SplitMut<'a, T, F>, F, T>(
            iter, old(slice)@, pred, false, false, 0,
        ),
;

pub assume_specification<'a, T, F: FnMut(&T) -> bool>[ <[T]>::split_inclusive::<F> ](
    slice: &'a [T],
    pred: F,
) -> (iter: SplitInclusive<'a, T, F>)
    ensures
        slice_predicate_split_view::<SplitInclusive<'a, T, F>, F, T>(
            iter, slice@, pred, true, false, 0,
        ),
;

pub assume_specification<'a, T, F: FnMut(&T) -> bool>[
    <[T]>::split_inclusive_mut::<F>
](
    slice: &'a mut [T],
    pred: F,
) -> (iter: SplitInclusiveMut<'a, T, F>)
    ensures
        slice_predicate_split_view::<SplitInclusiveMut<'a, T, F>, F, T>(
            iter, old(slice)@, pred, true, false, 0,
        ),
;

pub assume_specification<'a, T, F: FnMut(&T) -> bool>[ <[T]>::splitn::<F> ](
    slice: &'a [T],
    n: usize,
    pred: F,
) -> (iter: SplitN<'a, T, F>)
    ensures
        slice_predicate_split_view::<SplitN<'a, T, F>, F, T>(
            iter, slice@, pred, false, false, n as int,
        ),
;

pub assume_specification<'a, T, F: FnMut(&T) -> bool>[ <[T]>::splitn_mut::<F> ](
    slice: &'a mut [T],
    n: usize,
    pred: F,
) -> (iter: SplitNMut<'a, T, F>)
    ensures
        slice_predicate_split_view::<SplitNMut<'a, T, F>, F, T>(
            iter, old(slice)@, pred, false, false, n as int,
        ),
;

pub assume_specification<'a, T, F: FnMut(&T) -> bool>[ <[T]>::rsplit::<F> ](
    slice: &'a [T],
    pred: F,
) -> (iter: RSplit<'a, T, F>)
    ensures
        slice_predicate_split_view::<RSplit<'a, T, F>, F, T>(
            iter, slice@, pred, false, true, 0,
        ),
;

pub assume_specification<'a, T, F: FnMut(&T) -> bool>[ <[T]>::rsplit_mut::<F> ](
    slice: &'a mut [T],
    pred: F,
) -> (iter: RSplitMut<'a, T, F>)
    ensures
        slice_predicate_split_view::<RSplitMut<'a, T, F>, F, T>(
            iter, old(slice)@, pred, false, true, 0,
        ),
;

pub assume_specification<'a, T, F: FnMut(&T) -> bool>[ <[T]>::rsplitn::<F> ](
    slice: &'a [T],
    n: usize,
    pred: F,
) -> (iter: RSplitN<'a, T, F>)
    ensures
        slice_predicate_split_view::<RSplitN<'a, T, F>, F, T>(
            iter, slice@, pred, false, true, n as int,
        ),
;

pub assume_specification<'a, T, F: FnMut(&T) -> bool>[ <[T]>::rsplitn_mut::<F> ](
    slice: &'a mut [T],
    n: usize,
    pred: F,
) -> (iter: RSplitNMut<'a, T, F>)
    ensures
        slice_predicate_split_view::<RSplitNMut<'a, T, F>, F, T>(
            iter, old(slice)@, pred, false, true, n as int,
        ),
;

#[verifier::allow(undeclared_external_trait)]
pub assume_specification<'a, T, R: OneSidedRange<usize>>[ <[T]>::split_off::<R> ](
    slice_ref: &mut &'a [T],
    range: R,
) -> (ret: Option<&'a [T]>)
    ensures
        ret.is_none() ==> (*final(slice_ref))@ == (*old(slice_ref))@,
        ret.is_some() ==> slice_split_off_partition::<T>(
            (*old(slice_ref))@, (*final(slice_ref))@, ret.unwrap()@,
        ),
;

#[verifier::allow(undeclared_external_trait)]
pub assume_specification<'a, T, R: OneSidedRange<usize>>[
    <[T]>::split_off_mut::<R>
](
    slice_ref: &mut &'a mut [T],
    range: R,
) -> (ret: Option<&'a mut [T]>)
    ensures
        ret.is_none() ==> (*final(slice_ref))@ == (*old(slice_ref))@,
        ret.is_some() ==> slice_split_off_partition::<T>(
            (*old(slice_ref))@, (*final(slice_ref))@, ret.unwrap()@,
        ),
        ret.is_some() ==> slice_split_off_partition::<T>(
            (*old(slice_ref))@, (*final(slice_ref))@, final(ret.unwrap())@,
        ),
;

pub assume_specification<'a, T>[ <[T]>::split_off_first ](
    slice_ref: &mut &'a [T],
) -> (ret: Option<&'a T>)
    ensures
        (*old(slice_ref))@.len() == 0 ==> ret.is_none()
            && (*final(slice_ref))@ == (*old(slice_ref))@,
        (*old(slice_ref))@.len() != 0 ==> ret.is_some()
            && slice_split_off_first_result::<T>(
                (*old(slice_ref))@, (*final(slice_ref))@, *ret.unwrap(),
            ),
;

pub assume_specification<'a, T>[ <[T]>::split_off_first_mut ](
    slice_ref: &mut &'a mut [T],
) -> (ret: Option<&'a mut T>)
    ensures
        (*old(slice_ref))@.len() == 0 ==> ret.is_none()
            && (*final(slice_ref))@ == (*old(slice_ref))@,
        (*old(slice_ref))@.len() != 0 ==> ret.is_some()
            && slice_split_off_first_result::<T>(
                (*old(slice_ref))@, (*final(slice_ref))@, *ret.unwrap(),
            )
            && (seq![*final(ret.unwrap())] + (*final(slice_ref))@).len()
                == (*old(slice_ref))@.len(),
;

pub assume_specification<'a, T>[ <[T]>::split_off_last ](
    slice_ref: &mut &'a [T],
) -> (ret: Option<&'a T>)
    ensures
        (*old(slice_ref))@.len() == 0 ==> ret.is_none()
            && (*final(slice_ref))@ == (*old(slice_ref))@,
        (*old(slice_ref))@.len() != 0 ==> ret.is_some()
            && slice_split_off_last_result::<T>(
                (*old(slice_ref))@, (*final(slice_ref))@, *ret.unwrap(),
            ),
;

pub assume_specification<'a, T>[ <[T]>::split_off_last_mut ](
    slice_ref: &mut &'a mut [T],
) -> (ret: Option<&'a mut T>)
    ensures
        (*old(slice_ref))@.len() == 0 ==> ret.is_none()
            && (*final(slice_ref))@ == (*old(slice_ref))@,
        (*old(slice_ref))@.len() != 0 ==> ret.is_some()
            && slice_split_off_last_result::<T>(
                (*old(slice_ref))@, (*final(slice_ref))@, *ret.unwrap(),
            )
            && ((*final(slice_ref))@ + seq![*final(ret.unwrap())]).len()
                == (*old(slice_ref))@.len(),
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
