use super::super::prelude::*;
//use super::super::slice::SliceIndexSpec;
use super::super::utf8::is_char_boundary;
use super::core::{IndexSetTrustedSpec, IndexSpec, TrustedSpecSealed};
use super::iter::IteratorSpec;

#[cfg(not(verus_verify_core))]
use super::super::string::StringSliceAdditionalSpecFns;
use core::ops::Index;
use core::slice::{Iter, SliceIndex};

use core::ops::{Range, RangeFrom, RangeFull, RangeInclusive, RangeTo, RangeToInclusive};

use verus as verus_;

verus_! {

impl<T, const N: usize> TrustedSpecSealed for [T; N] {}

impl<T, const N: usize> IndexSetTrustedSpec<usize> for [T; N] {
    open spec fn spec_index_set_requires(&self, index: usize) -> bool {
        0 <= index < N
    }

    open spec fn spec_index_set_ensures(&self, new_container: &Self, index: usize, val: T) -> bool {
        new_container@ == self@.update(index as int, val)
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

// pub assume_specification<T>[ <usize as SliceIndex<[T]>>::index ](i: usize, slice: &[T]) -> &T
//     returns
//         slice@[i as int],
// ;

// pub assume_specification<T>[ <Range<usize> as SliceIndex<[T]>>::index ](i: Range<usize>, slice: &[T]) -> (r: &[T])
//     ensures
//         r@ == slice@.subrange(i.start as int, i.end as int),
// ;

impl<T, I: SliceIndex<[T]>> super::core::IndexSpecImpl<I> for [T] {
    open spec fn index_req(&self, index: &I) -> bool {
        valid_indices(index.spec_start(self), index.spec_end(self), self)
    }
}

impl<T, I, const N: usize> super::core::IndexSpecImpl<I> for [T; N]
    where [T]: Index<I>
{
    open spec fn index_req(&self, index: &I) -> bool {
        <[T] as IndexSpec<I>>::index_req(self, index)
    }
}

pub assume_specification<T, I: SliceIndex<[T]>> [<[T] as Index<I>>::index] (
    slice: &[T],
    index: I,
) -> (output: &<I as core::slice::SliceIndex<[T]>>::Output)
    ensures
        call_ensures(<I as SliceIndex<[T]>>::index, (index, slice), output),
;

pub assume_specification<T, I, const N: usize> [<[T; N] as Index<I>>::index] (
    array: &[T; N],
    index: I,
) -> (output: &<[T; N] as core::ops::Index<I>>::Output)
    where [T]: Index<I>,
    ensures
        call_ensures(<[T] as Index<I>>::index, (array, index), output),
;

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
pub uninterp spec fn valid_indices<T: ?Sized>(start: int, end: int, slice: &T) -> bool;

// For slices, the indices must be in bounds.
pub broadcast axiom fn valid_indices_slice<T>(start: int, end: int, slice: &[T])
    ensures
        start <= end <= slice@.len() ==> #[trigger] valid_indices(start, end, slice);

#[cfg(not(verus_verify_core))]
// For str, the indices must be in bounds and fall on a char boundary.
pub broadcast axiom fn valid_indices_str(start: int, end: int, slice: &str)
    ensures
        start <= end <= slice.spec_bytes().len() && is_char_boundary(slice.spec_bytes(), start) && is_char_boundary(slice.spec_bytes(), end) ==> #[trigger] valid_indices(start, end, slice);

/// True when `output` is the result of slicing `slice` from `start` to `end` (exclusive) indices.
// This is written as a relation because `Output` is an exec type (e.g. [T]),
// and so we cannot necessarily return it from a spec function.
pub uninterp spec fn index_result<T: ?Sized, Output: ?Sized>(start: int, end: int, slice: &T, output: &Output) -> bool;

pub broadcast axiom fn index_result_slice_usize<T>(start: int, end: int, slice: &[T], output: &T)
    ensures
        #[trigger] index_result::<[T], T>(start, end, slice, output) <==> *output =~= slice@[start];

pub broadcast axiom fn index_result_slice<T>(start: int, end: int, slice: &[T], output: &[T])
    ensures
        #[trigger] index_result::<[T], [T]>(start, end, slice, output) <==> output@ =~= slice@.subrange(start, end);

#[cfg(not(verus_verify_core))]
pub broadcast axiom fn index_result_str(start: int, end: int, slice: &str, output: &str)
    ensures
        #[trigger] index_result::<str, str>(start, end, slice, output) <==> output.spec_bytes() == slice.spec_bytes().subrange(start, end);

/// True when the final value of the slice (`final_slice`) will be the result of
/// mutating the original slice (`old_slice`) between the indices `start` and `end`,
/// where the final value between those indices is given by `final_output`.
pub uninterp spec fn index_mut_result<T: ?Sized, Output: ?Sized>(start: int, end: int, old_slice: &T, final_slice: &T, final_output: &Output) -> bool;

pub broadcast axiom fn index_mut_result_slice<T>(start: int, end: int, old_slice: &[T], final_slice: &[T], final_output: &[T])
    ensures
        #[trigger] index_mut_result::<[T], [T]>(start, end, old_slice, final_slice, final_output) <==> final_slice@ =~= old_slice@.subrange(0, start) + final_output@ + old_slice@.subrange(end, old_slice@.len() as int)
    ;

pub broadcast axiom fn index_mut_result_slice_usize<T>(start: int, end: int, old_slice: &[T], final_slice: &[T], final_output: &T)
    ensures
        #[trigger] index_mut_result::<[T], T>(start, end, old_slice, final_slice, final_output) <==> final_slice@ =~= old_slice@.update(start, *final_output)
    ;

#[cfg(not(verus_verify_core))]
pub broadcast axiom fn index_mut_result_str(start: int, end: int, old_slice: &str, final_slice: &str, final_output: &str)
    ensures
        #[trigger] index_mut_result::<str, str>(start, end, old_slice, final_slice, final_output) <==> final_slice.spec_bytes() =~= old_slice.spec_bytes().subrange(0, start) + final_output.spec_bytes() + old_slice.spec_bytes().subrange(end, old_slice.spec_bytes().len() as int)
    ;

#[verifier::external_trait_specification]
#[verifier::external_trait_extension(SliceIndexSpec via SliceIndexSpecImpl)]
#[verifier::external_trait_private_bound(core::slice::index::private_slice_index::Sealed)]
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
            out.is_some() <==> valid_indices(self.spec_start(slice), self.spec_end(slice), slice),
            out.is_some() ==> index_result(self.spec_start(slice), self.spec_end(slice), slice, out.unwrap())
    ;

    fn get_mut(self, slice: &mut T) -> (out: Option<&mut Self::Output>)
        requires
            valid_slice::<T>(old(slice)),
        ensures
            out.is_some() <==> valid_indices(self.spec_start(old(slice)), self.spec_end(old(slice)), old(slice)),
            out.is_some() ==> {
                &&& index_result(self.spec_start(old(slice)), self.spec_end(old(slice)), old(slice), out.unwrap())
                &&& index_mut_result(self.spec_start(old(slice)), self.spec_end(old(slice)), old(slice), final(slice), final(out.unwrap()))
            },
    ;

    fn index(self, slice: &T) -> (out: &Self::Output)
        requires
            valid_slice::<T>(slice),
            valid_indices(self.spec_start(slice), self.spec_end(slice), slice)
        ensures
            index_result(self.spec_start(slice), self.spec_end(slice), slice, out)
        ;

    fn index_mut(self, slice: &mut T) -> (out: &mut Self::Output)
        requires
            valid_slice::<T>(old(slice)),
            valid_indices(self.spec_start(old(slice)), self.spec_end(old(slice)), old(slice))
        ensures
            index_result(self.spec_start(old(slice)), self.spec_end(old(slice)), old(slice), out),
            index_mut_result(self.spec_start(old(slice)), self.spec_end(old(slice)), old(slice), final(slice), final(out))
        ;
}

impl<T> SliceIndexSpecImpl<[T]> for usize {
    open spec fn spec_start(&self, slice: &[T]) -> int {
        self as int
    }
    open spec fn spec_end(&self, slice: &[T]) -> int {
        self as int + 1
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
#[cfg(not(verus_verify_core))]
impl SliceIndexSpecImpl<str> for Range<usize> {
    open spec fn spec_start(&self, slice: &str) -> int {
        self.start as int
    }

    open spec fn spec_end(&self, slice: &str) -> int {
        self.end as int
    }
}
// describes range: start..
#[cfg(not(verus_verify_core))]
impl SliceIndexSpecImpl<str> for RangeFrom<usize> {
    open spec fn spec_start(&self, slice: &str) -> int {
        self.start as int
    }

    open spec fn spec_end(&self, slice: &str) -> int {
        slice.spec_bytes().len() as int
    }
}
// describes full range: ..
#[cfg(not(verus_verify_core))]
impl SliceIndexSpecImpl<str> for RangeFull {
    open spec fn spec_start(&self, slice: &str) -> int {
        0
    }

    open spec fn spec_end(&self, slice: &str) -> int {
        slice.spec_bytes().len() as int
    }
}
// describes range: start..=end
#[cfg(not(verus_verify_core))]
impl SliceIndexSpecImpl<str> for RangeInclusive<usize> {
    open spec fn spec_start(&self, slice: &str) -> int {
        self@.start as int
    }

    open spec fn spec_end(&self, slice: &str) -> int {
        self@.end as int + 1
    }
}
// describes range: ..end
#[cfg(not(verus_verify_core))]
impl SliceIndexSpecImpl<str> for RangeTo<usize> {
    open spec fn spec_start(&self, slice: &str) -> int {
        0
    }

    open spec fn spec_end(&self, slice: &str) -> int {
        self.end as int
    }
}
// describes range: ..=end
#[cfg(not(verus_verify_core))]
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
    valid_indices_slice,
    valid_indices_str,
    index_result_slice,
    index_result_slice_usize,
    index_result_str,
    index_mut_result_slice,
    index_mut_result_slice_usize,
    index_mut_result_str
}

#[cfg(verus_verify_core)]
pub broadcast group group_slice_index_specs {
    valid_slice_slice,
    valid_indices_slice,
    index_result_slice,
    index_result_slice_usize,
    index_mut_result_slice,
    index_mut_result_slice_usize
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

pub broadcast group group_slice_axioms {
    axiom_spec_slice_iter,
    group_slice_index_specs
}

} // verus!
