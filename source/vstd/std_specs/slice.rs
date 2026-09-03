use super::super::prelude::*;
use super::super::slice::{SliceIndexSpec, spec_slice_get};
use super::core::IndexSpec;
use super::iter::IteratorSpec;
use super::range::{slice_range_end, slice_range_start, slice_range_valid};

use core::ops::{
    FnMut, Index, IndexMut, Range, RangeFrom, RangeFull, RangeInclusive, RangeTo, RangeToInclusive,
};
use core::slice::{
    ArrayWindows, ChunkBy, ChunkByMut, Chunks, ChunksExact, ChunksExactMut, ChunksMut, Iter,
    RChunks, RChunksExact, RChunksExactMut, RChunksMut, SliceIndex,
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

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(T)]
pub struct ExChunks<'a, T: 'a>(Chunks<'a, T>);

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(T)]
pub struct ExChunksExact<'a, T: 'a>(ChunksExact<'a, T>);

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(T)]
pub struct ExChunksMut<'a, T: 'a>(ChunksMut<'a, T>);

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(T)]
pub struct ExChunksExactMut<'a, T: 'a>(ChunksExactMut<'a, T>);

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(T)]
pub struct ExRChunks<'a, T: 'a>(RChunks<'a, T>);

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(T)]
pub struct ExRChunksExact<'a, T: 'a>(RChunksExact<'a, T>);

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(T)]
pub struct ExRChunksMut<'a, T: 'a>(RChunksMut<'a, T>);

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(T)]
pub struct ExRChunksExactMut<'a, T: 'a>(RChunksExactMut<'a, T>);

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(T)]
pub struct ExArrayWindows<'a, T: 'a, const N: usize>(ArrayWindows<'a, T, N>);

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(T)]
#[verifier::reject_recursive_types(P)]
pub struct ExChunkBy<'a, T: 'a, P>(ChunkBy<'a, T, P>);

#[verifier::external_type_specification]
#[verifier::external_body]
#[verifier::reject_recursive_types(T)]
#[verifier::reject_recursive_types(P)]
pub struct ExChunkByMut<'a, T: 'a, P>(ChunkByMut<'a, T, P>);

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

pub open spec fn slice_chunk_partition<T>(view: SliceIteratorView<T>) -> bool {
    slice_iterator_well_formed(view)
        && view.chunk_size > 0
        && (view.remainder.len() as int) < view.chunk_size
        && (view.remaining.len() as int) % view.chunk_size == 0
        && (view.yielded_prefix.len() as int) % view.chunk_size == 0
        && if view.reverse {
            view.remainder + view.remaining + view.yielded_prefix == view.source
        } else {
            view.yielded_prefix + view.remaining + view.remainder == view.source
        }
}

pub uninterp spec fn fnmut_adjacent_predicate_observed<F, T>(
    pred: F,
    left: T,
    right: T,
) -> bool;

pub open spec fn slice_adjacent_chunk_view<I, F, T>(
    iter: I,
    source: Seq<T>,
    pred: F,
) -> bool {
    let view = slice_iterator_view::<I, T>(iter);
    slice_iterator_well_formed(view)
        && view.source == source
        && view.remaining == source
        && view.yielded_prefix == Seq::empty()
        && view.remainder == Seq::empty()
        && view.chunk_size == 0
        && !view.reverse
        && view.yielded_prefix + view.remaining == source
        && forall|i: int| 0 <= i + 1 < source.len()
            ==> (#[trigger] fnmut_adjacent_predicate_observed(pred, source[i], source[i + 1])
                || !fnmut_adjacent_predicate_observed(pred, source[i], source[i + 1]))
}

pub uninterp spec fn slice_start_ptr<T>(seq: Seq<T>, ptr: *const T) -> bool;

pub uninterp spec fn slice_start_mut_ptr<T>(seq: Seq<T>, ptr: *mut T) -> bool;

pub uninterp spec fn slice_index_in_range<T, I: SliceIndex<[T]>>(
    seq: Seq<T>,
    index: I,
) -> bool;

pub uninterp spec fn slice_index_mut_frame<T, I: SliceIndex<[T]>>(
    old_seq: Seq<T>,
    index: I,
    final_seq: Seq<T>,
) -> bool;

pub assume_specification<'a, T>[ <[T]>::chunks ](
    slice: &'a [T],
    chunk_size: usize,
) -> (iter: Chunks<'a, T>)
    requires
        chunk_size != 0,
    ensures
        slice_iterator_view::<Chunks<'a, T>, T>(iter).source == slice@,
        slice_iterator_view::<Chunks<'a, T>, T>(iter).remaining == slice@,
        slice_iterator_view::<Chunks<'a, T>, T>(iter).yielded_prefix == Seq::empty(),
        slice_iterator_view::<Chunks<'a, T>, T>(iter).remainder == Seq::empty(),
        slice_iterator_view::<Chunks<'a, T>, T>(iter).chunk_size == chunk_size as int,
        !slice_iterator_view::<Chunks<'a, T>, T>(iter).reverse,
;

pub assume_specification<'a, T>[ <[T]>::chunks_exact ](
    slice: &'a [T],
    chunk_size: usize,
) -> (iter: ChunksExact<'a, T>)
    requires
        chunk_size != 0,
    ensures
        slice_iterator_view::<ChunksExact<'a, T>, T>(iter).source == slice@,
        slice_iterator_view::<ChunksExact<'a, T>, T>(iter).yielded_prefix == Seq::empty(),
        slice_iterator_view::<ChunksExact<'a, T>, T>(iter).chunk_size == chunk_size as int,
        !slice_iterator_view::<ChunksExact<'a, T>, T>(iter).reverse,
        slice_chunk_partition::<T>(slice_iterator_view::<ChunksExact<'a, T>, T>(iter)),
;

pub assume_specification<'a, T>[ <[T]>::rchunks ](
    slice: &'a [T],
    chunk_size: usize,
) -> (iter: RChunks<'a, T>)
    requires
        chunk_size != 0,
    ensures
        slice_iterator_view::<RChunks<'a, T>, T>(iter).source == slice@,
        slice_iterator_view::<RChunks<'a, T>, T>(iter).remaining == slice@,
        slice_iterator_view::<RChunks<'a, T>, T>(iter).yielded_prefix == Seq::empty(),
        slice_iterator_view::<RChunks<'a, T>, T>(iter).remainder == Seq::empty(),
        slice_iterator_view::<RChunks<'a, T>, T>(iter).chunk_size == chunk_size as int,
        slice_iterator_view::<RChunks<'a, T>, T>(iter).reverse,
;

pub assume_specification<'a, T>[ <[T]>::rchunks_exact ](
    slice: &'a [T],
    chunk_size: usize,
) -> (iter: RChunksExact<'a, T>)
    requires
        chunk_size != 0,
    ensures
        slice_iterator_view::<RChunksExact<'a, T>, T>(iter).source == slice@,
        slice_iterator_view::<RChunksExact<'a, T>, T>(iter).yielded_prefix == Seq::empty(),
        slice_iterator_view::<RChunksExact<'a, T>, T>(iter).chunk_size == chunk_size as int,
        slice_iterator_view::<RChunksExact<'a, T>, T>(iter).reverse,
        slice_chunk_partition::<T>(slice_iterator_view::<RChunksExact<'a, T>, T>(iter)),
;

pub assume_specification<'a, T, const N: usize>[ <[T]>::array_windows::<N> ](
    slice: &'a [T],
) -> (iter: ArrayWindows<'a, T, N>)
    requires
        N != 0,
    ensures
        slice_iterator_view::<ArrayWindows<'a, T, N>, T>(iter).source == slice@,
        slice_iterator_view::<ArrayWindows<'a, T, N>, T>(iter).remaining == slice@,
        slice_iterator_view::<ArrayWindows<'a, T, N>, T>(iter).yielded_prefix == Seq::empty(),
        slice_iterator_view::<ArrayWindows<'a, T, N>, T>(iter).remainder == Seq::empty(),
        slice_iterator_view::<ArrayWindows<'a, T, N>, T>(iter).chunk_size == N as int,
        !slice_iterator_view::<ArrayWindows<'a, T, N>, T>(iter).reverse,
;

pub assume_specification<'a, T>[ <[T]>::chunks_mut ](
    slice: &'a mut [T],
    chunk_size: usize,
) -> (iter: ChunksMut<'a, T>)
    requires
        chunk_size != 0,
    ensures
        slice_iterator_view::<ChunksMut<'a, T>, T>(iter).source == old(slice)@,
        slice_iterator_view::<ChunksMut<'a, T>, T>(iter).remaining == old(slice)@,
        slice_iterator_view::<ChunksMut<'a, T>, T>(iter).yielded_prefix == Seq::empty(),
        slice_iterator_view::<ChunksMut<'a, T>, T>(iter).remainder == Seq::empty(),
        slice_iterator_view::<ChunksMut<'a, T>, T>(iter).chunk_size == chunk_size as int,
        !slice_iterator_view::<ChunksMut<'a, T>, T>(iter).reverse,
;

pub assume_specification<'a, T>[ <[T]>::chunks_exact_mut ](
    slice: &'a mut [T],
    chunk_size: usize,
) -> (iter: ChunksExactMut<'a, T>)
    requires
        chunk_size != 0,
    ensures
        slice_iterator_view::<ChunksExactMut<'a, T>, T>(iter).source == old(slice)@,
        slice_iterator_view::<ChunksExactMut<'a, T>, T>(iter).yielded_prefix == Seq::empty(),
        slice_iterator_view::<ChunksExactMut<'a, T>, T>(iter).chunk_size == chunk_size as int,
        !slice_iterator_view::<ChunksExactMut<'a, T>, T>(iter).reverse,
        slice_chunk_partition::<T>(slice_iterator_view::<ChunksExactMut<'a, T>, T>(iter)),
;

pub assume_specification<'a, T>[ <[T]>::rchunks_mut ](
    slice: &'a mut [T],
    chunk_size: usize,
) -> (iter: RChunksMut<'a, T>)
    requires
        chunk_size != 0,
    ensures
        slice_iterator_view::<RChunksMut<'a, T>, T>(iter).source == old(slice)@,
        slice_iterator_view::<RChunksMut<'a, T>, T>(iter).remaining == old(slice)@,
        slice_iterator_view::<RChunksMut<'a, T>, T>(iter).yielded_prefix == Seq::empty(),
        slice_iterator_view::<RChunksMut<'a, T>, T>(iter).remainder == Seq::empty(),
        slice_iterator_view::<RChunksMut<'a, T>, T>(iter).chunk_size == chunk_size as int,
        slice_iterator_view::<RChunksMut<'a, T>, T>(iter).reverse,
;

pub assume_specification<'a, T>[ <[T]>::rchunks_exact_mut ](
    slice: &'a mut [T],
    chunk_size: usize,
) -> (iter: RChunksExactMut<'a, T>)
    requires
        chunk_size != 0,
    ensures
        slice_iterator_view::<RChunksExactMut<'a, T>, T>(iter).source == old(slice)@,
        slice_iterator_view::<RChunksExactMut<'a, T>, T>(iter).yielded_prefix == Seq::empty(),
        slice_iterator_view::<RChunksExactMut<'a, T>, T>(iter).chunk_size == chunk_size as int,
        slice_iterator_view::<RChunksExactMut<'a, T>, T>(iter).reverse,
        slice_chunk_partition::<T>(slice_iterator_view::<RChunksExactMut<'a, T>, T>(iter)),
;

pub assume_specification<'a, T, F: FnMut(&T, &T) -> bool>[ <[T]>::chunk_by::<F> ](
    slice: &'a [T],
    pred: F,
) -> (iter: ChunkBy<'a, T, F>)
    ensures
        slice_adjacent_chunk_view::<ChunkBy<'a, T, F>, F, T>(iter, slice@, pred),
;

pub assume_specification<'a, T, F: FnMut(&T, &T) -> bool>[ <[T]>::chunk_by_mut::<F> ](
    slice: &'a mut [T],
    pred: F,
) -> (iter: ChunkByMut<'a, T, F>)
    ensures
        slice_adjacent_chunk_view::<ChunkByMut<'a, T, F>, F, T>(
            iter, old(slice)@, pred,
        ),
;

pub assume_specification<T>[ <[T]>::as_mut_ptr ](
    slice: &mut [T],
) -> (ptr: *mut T)
    ensures
        slice_start_mut_ptr(old(slice)@, ptr),
        final(slice)@ == old(slice)@,
;

pub assume_specification<T>[ <[T]>::as_ptr ](
    slice: &[T],
) -> (ptr: *const T)
    ensures
        slice_start_ptr(slice@, ptr),
;

#[verifier::allow(undeclared_external_trait)]
pub assume_specification<T, I>[ <[T]>::get_mut::<I> ](
    slice: &mut [T],
    index: I,
) -> (ret: Option<&mut <I as SliceIndex<[T]>>::Output>)
    where I: SliceIndex<[T]>
    ensures
        ret.is_some() ==> slice_index_in_range(old(slice)@, index)
            && slice_index_mut_frame(old(slice)@, index, final(slice)@),
        ret.is_none() ==> !slice_index_in_range(old(slice)@, index)
            && final(slice)@ == old(slice)@,
;

pub broadcast group group_slice_axioms {
    axiom_slice_get_range,
    axiom_slice_get_range_to,
    axiom_slice_get_range_from,
    axiom_slice_get_range_to_inclusive,
    axiom_slice_get_range_full,
    axiom_slice_get_range_inclusive,
    axiom_slice_iterator_view_well_formed,
}

} // verus!
