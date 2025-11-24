use super::super::prelude::*;
use super::cmp::{OrdSpec, PartialEqSpec, PartialOrdSpec};
use super::core::IndexSetTrustedSpec;
use super::core::TrustedSpecSealed;

use core::cmp::Ordering;
use core::slice::Iter;

use verus as verus_;

verus_! {

pub open spec fn is_sorted_spec<T: PartialOrd>(s: Seq<T>) -> bool {
    forall|i: int, j: int|
        #![trigger s[i].partial_cmp_spec(&s[j])]
        0 <= i < j < s.len() ==> s[i].partial_cmp_spec(&s[j]) == Some(Ordering::Less)
            || s[i].partial_cmp_spec(&s[j]) == Some(Ordering::Equal)
}

pub open spec fn is_sorted_by_spec<'a, T: 'a, F: FnMut(&'a T, &'a T) -> bool>(
    s: Seq<T>,
    f: F,
) -> bool {
    forall|i: int, j: int, b: bool|
        #![trigger f.ensures((&s[i], &s[j]), b)]
        0 <= i < j < s.len() ==> f.ensures((&s[i], &s[j]), b) ==> b
}

pub open spec fn is_sorted_by_pivot_spec<'a, T: 'a, F: FnMut(&'a T) -> Ordering>(
    s: Seq<T>,
    f: F,
) -> bool {
    // The sequence is partitioned into [Less*, Equal*, Greater*]
    forall|i: int, j: int, ord1: Ordering, ord2: Ordering|
        #![trigger f.ensures((&s[i],), ord1), f.ensures((&s[j],), ord2)]
        0 <= i < j < s.len() && f.ensures((&s[i],), ord1) && f.ensures(
            (&s[j],),
            ord2,
        )
        // Ordering itself is total.
         ==> ord1.cmp_spec(&ord2) != Ordering::Greater
}

pub open spec fn is_sorted_by_key_spec<'a, T: 'a, F: FnMut(&'a T) -> K, K: PartialOrd>(
    s: Seq<T>,
    f: F,
) -> bool {
    forall|i: int, j: int, k1: K, k2: K|
        #![trigger f.ensures((&s[i],), k1), f.ensures((&s[j],), k2)]
        0 <= i < j < s.len() && f.ensures((&s[i],), k1) && f.ensures(
            (&s[j],),
            k2,
        )
        // K is partially ordered.
         ==> k1.partial_cmp_spec(&k2) == Some(Ordering::Less) || k1.partial_cmp_spec(&k2) == Some(
            Ordering::Equal,
        )
}

pub assume_specification<T: PartialOrd>[ <[T]>::is_sorted ](s: &[T]) -> (r: bool)
    ensures
        r == is_sorted_spec(s@),
;

pub assume_specification<'a, T, F: FnMut(&'a T, &'a T) -> bool>[ <[T]>::is_sorted_by ](
    s: &'a [T],
    compare: F,
) -> (r: bool)
    ensures
        r == is_sorted_by_spec(s@, compare),
;

pub assume_specification<'a, T, F: FnMut(&'a T) -> K, K: PartialOrd>[ <[T]>::is_sorted_by_key ](
    s: &'a [T],
    compare: F,
) -> (r: bool)
    ensures
        r == is_sorted_by_key_spec(s@, compare),
;

/// Binary searches this slice for a given element.
///
/// Please be extra careful that if the slice is not properly sorted, the result is
/// unspecified and meaningless.
///
/// See https://doc.rust-lang.org/stable/core/primitive.slice.html#method.binary_search
pub assume_specification<T: Ord>[ <[T]>::binary_search ](s: &[T], x: &T) -> (r: Result<
    usize,
    usize,
>)
    ensures
        is_sorted_spec(s@) ==> match r {
            Ok(index) => {
                &&& 0 <= index < s.len()
                &&& s[index as int] == *x
            },
            Err(insert_index) => {
                &&& 0 <= insert_index <= s.len()
                &&& forall|i: int|
                    #![trigger s[i].cmp_spec(x)]
                    0 <= i < s.len() ==> {
                        if i < insert_index {
                            s[i].cmp_spec(x) != Ordering::Greater
                        } else {
                            s[i].cmp_spec(x) != Ordering::Less
                        }
                    }
            },
        },
;

/// Binary searches this slice with a comparator function.
///
/// Similar to `binary_search`, but allows the caller to provide a custom comparator function
/// that compares each element to the desired pivot value.
pub assume_specification<'a, T, F: FnMut(&'a T) -> Ordering>[ <[T]>::binary_search_by ](
    s: &'a [T],
    f: F,
) -> (r: Result<usize, usize>)
    ensures
        is_sorted_by_pivot_spec(s@, f) ==> match r {
            Ok(index) => {
                &&& 0 <= index < s.len()
                &&& forall|ord: Ordering|
                    #![trigger f.ensures((&s[index as int],), ord)]
                    f.ensures((&s[index as int],), ord) ==> ord == Ordering::Equal
            },
            Err(insert_index) => {
                &&& 0 <= insert_index <= s.len()
                &&& forall|i: int, ord: Ordering|
                    #![trigger f.ensures((&s[i],), ord)]
                    0 <= i < s.len() && i < insert_index && f.ensures((&s[i],), ord) ==> ord
                        != Ordering::Greater
                &&& forall|i: int, ord: Ordering|
                    #![trigger f.ensures((&s[i],), ord)]
                    0 <= i < s.len() && i >= insert_index && f.ensures((&s[i],), ord) ==> ord
                        != Ordering::Less
            },
        },
;

/// Binary searches this slice with a key extraction function.
pub assume_specification<'a, T, B: Ord, F: FnMut(&'a T) -> B>[ <[T]>::binary_search_by_key ](
    s: &'a [T],
    b: &B,
    f: F,
) -> (r: Result<usize, usize>)
    ensures
        is_sorted_by_key_spec(s@, f) ==> match r {
            Ok(index) => {
                &&& 0 <= index < s.len()
                &&& forall|key: B|
                    #![trigger f.ensures((&s[index as int],), key)]
                    f.ensures((&s[index as int],), key) ==> key.cmp_spec(b) == Ordering::Equal
            },
            Err(insert_index) => {
                &&& 0 <= insert_index <= s.len()
                &&& forall|i: int, key: B|
                    #![trigger f.ensures((&s[i],), key)]
                    0 <= i < s.len() && i < insert_index && f.ensures((&s[i],), key)
                        ==> key.cmp_spec(b) != Ordering::Greater
                &&& forall|i: int, key: B|
                    #![trigger f.ensures((&s[i],), key)]
                    0 <= i < s.len() && i >= insert_index && f.ensures((&s[i],), key)
                        ==> key.cmp_spec(b) != Ordering::Less
            },
        },
;

pub assume_specification<T: PartialEq>[ <[T]>::contains ](s: &[T], x: &T) -> (r: bool)
    ensures
        r <==> exists|i: int| 0 <= i < s.len() && #[trigger] s[i].eq_spec(x),
;

pub assume_specification<T: PartialEq>[ <[T]>::starts_with ](s: &[T], needle: &[T]) -> (r: bool)
    ensures
        r <==> {
            &&& needle@.len() <= s@.len()
            &&& forall|i: int| 0 <= i < needle@.len() ==> #[trigger] s[i].eq_spec(&needle[i])
        },
;

pub assume_specification<T: PartialEq>[ <[T]>::ends_with ](s: &[T], needle: &[T]) -> (r: bool)
    ensures
        r <==> {
            &&& needle@.len() <= s@.len()
            &&& forall|i: int|
                0 <= i < needle@.len() ==> s[(s@.len() - needle@.len()) + i].eq_spec(&needle[i])
        },
;

pub assume_specification<T>[ <[T]>::swap ](s: &mut [T], i: usize, j: usize)
    requires
        0 <= i < old(s).len(),
        0 <= j < old(s).len(),
    ensures
        s@ =~= old(s)@.update(i as int, old(s)@[j as int]).update(j as int, old(s)@[i as int]),
;

pub assume_specification<T>[ <[T]>::reverse ](s: &mut [T])
    ensures
        s@ =~= old(s)@.reverse(),
;

pub assume_specification<T>[ <[T]>::first ](s: &[T]) -> (r: Option<&T>)
    ensures
        r == if s@.len() == 0 {
            None
        } else {
            Some(&s@.first())
        },
;

pub assume_specification<T>[ <[T]>::last ](s: &[T]) -> (r: Option<&T>)
    ensures
        r == if s@.len() == 0 {
            None
        } else {
            Some(&s@.last())
        },
;

pub assume_specification<T>[ <[T]>::split_at_checked ](s: &[T], mid: usize) -> (r: Option<
    (&[T], &[T]),
>)
    ensures
        mid <= s@.len() ==> {
            &&& r matches Some((left, right)) && {
                &&& left@ =~= s@.subrange(0, mid as int)
                &&& right@ =~= s@.subrange(mid as int, s@.len() as int)
            }
        },
        mid > s@.len() ==> r matches None::<(&[T], &[T])>,
;

pub assume_specification<T>[ <[T]>::split_at ](s: &[T], mid: usize) -> (r: (&[T], &[T]))
    ensures
        mid <= s@.len() ==> {
            &&& r.0@ =~= s@.subrange(0, mid as int)
            &&& r.1@ =~= s@.subrange(mid as int, s@.len() as int)
        },
;

pub assume_specification<T>[ <[T]>::rotate_left ](s: &mut [T], mid: usize)
    ensures
        mid <= s@.len() ==> s@ =~= old(s)@.subrange(mid as int, s@.len() as int) + old(s)@.subrange(
            0,
            mid as int,
        ),
;

pub assume_specification<T>[ <[T]>::rotate_right ](s: &mut [T], mid: usize)
    ensures
        mid <= s@.len() ==> s@ =~= old(s)@.subrange((s@.len() - mid as int), s@.len() as int) + old(
            s,
        )@.subrange(0, (s@.len() - mid as int)),
;

pub assume_specification<T, const N: usize>[ <[[T; N]]>::as_flattened ](s: &[[T; N]]) -> (r: &[T])
    ensures
        r@ =~= Seq::new(s@.len() as nat, |i: int| s@[i]@).flatten(),
;

impl<T, const N: usize> TrustedSpecSealed for [T; N] {

}

impl<T, const N: usize> IndexSetTrustedSpec<usize> for [T; N] {
    open spec fn spec_index_set_requires(&self, index: usize) -> bool {
        0 <= index < N
    }

    open spec fn spec_index_set_ensures(&self, new_container: &Self, index: usize, val: T) -> bool {
        new_container@ === self@.update(index as int, val)
    }
}

impl<T> TrustedSpecSealed for [T] {

}

impl<T> IndexSetTrustedSpec<usize> for [T] {
    open spec fn spec_index_set_requires(&self, index: usize) -> bool {
        0 <= index < self@.len()
    }

    open spec fn spec_index_set_ensures(&self, new_container: &Self, index: usize, val: T) -> bool {
        new_container@ == self@.update(index as int, val)
    }
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

pub broadcast group group_slice_axioms {
    axiom_spec_slice_iter,
}

} // verus!
