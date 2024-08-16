#[allow(unused_imports)]
use super::multiset::Multiset;
#[allow(unused_imports)]
use super::pervasive::*;
#[allow(unused_imports)]
use super::prelude::*;
#[allow(unused_imports)]
use super::relations::*;
#[allow(unused_imports)]
use super::seq::*;
#[allow(unused_imports)]
use super::set::Set;
#[cfg(verus_keep_ghost)]
use super::set_lib::lemma_set_properties;

verus! {

broadcast use group_seq_axioms;

impl<A> Seq<A> {
    /// Applies the function `f` to each element of the sequence, and returns
    /// the resulting sequence.
    /// The `int` parameter of `f` is the index of the element being mapped.
    // TODO(verus): rename to map_entries, for consistency with Map::map
    pub open spec fn map<B>(self, f: spec_fn(int, A) -> B) -> Seq<B> {
        Seq::new(self.len(), |i: int| f(i, self[i]))
    }

    /// Applies the function `f` to each element of the sequence, and returns
    /// the resulting sequence.
    // TODO(verus): rename to map, because this is what everybody wants.
    pub open spec fn map_values<B>(self, f: spec_fn(A) -> B) -> Seq<B> {
        Seq::new(self.len(), |i: int| f(self[i]))
    }

    /// Is true if the calling sequence is a prefix of the given sequence 'other'.
    ///
    /// ## Example
    ///
    /// ```rust
    /// proof fn prefix_test() {
    ///     let pre: Seq<int> = seq![1, 2, 3];
    ///     let whole: Seq<int> = seq![1, 2, 3, 4, 5];
    ///     assert(pre.is_prefix_of(whole));
    /// }
    /// ```
    pub open spec fn is_prefix_of(self, other: Self) -> bool {
        self.len() <= other.len() && self =~= other.subrange(0, self.len() as int)
    }

    /// Is true if the calling sequence is a suffix of the given sequence 'other'.
    ///
    /// ## Example
    ///
    /// ```rust
    /// proof fn suffix_test() {
    ///     let end: Seq<int> = seq![3, 4, 5];
    ///     let whole: Seq<int> = seq![1, 2, 3, 4, 5];
    ///     assert(end.is_suffix_of(whole));
    /// }
    /// ```
    pub open spec fn is_suffix_of(self, other: Self) -> bool {
        self.len() <= other.len() && self =~= other.subrange(
            (other.len() - self.len()) as int,
            other.len() as int,
        )
    }

    /// Sorts the sequence according to the given leq function
    ///
    /// ## Example
    ///
    /// ```rust
    /// {{#include ../../../rust_verify/example/multiset.rs:sorted_by_leq}}
    /// ```
    pub closed spec fn sort_by(self, leq: spec_fn(A, A) -> bool) -> Seq<A>
        recommends
            total_ordering(leq),
        decreases self.len(),
    {
        if self.len() <= 1 {
            self
        } else {
            let split_index = self.len() / 2;
            let left = self.subrange(0, split_index as int);
            let right = self.subrange(split_index as int, self.len() as int);
            let left_sorted = left.sort_by(leq);
            let right_sorted = right.sort_by(leq);
            merge_sorted_with(left_sorted, right_sorted, leq)
        }
    }

    pub proof fn lemma_sort_by_ensures(self, leq: spec_fn(A, A) -> bool)
        requires
            total_ordering(leq),
        ensures
            self.to_multiset() =~= self.sort_by(leq).to_multiset(),
            sorted_by(self.sort_by(leq), leq),
            forall|x: A| !self.contains(x) ==> !(#[trigger] self.sort_by(leq).contains(x)),
        decreases self.len(),
    {
        if self.len() <= 1 {
        } else {
            let split_index = self.len() / 2;
            let left = self.subrange(0, split_index as int);
            let right = self.subrange(split_index as int, self.len() as int);
            assert(self =~= left + right);
            let left_sorted = left.sort_by(leq);
            left.lemma_sort_by_ensures(leq);
            let right_sorted = right.sort_by(leq);
            right.lemma_sort_by_ensures(leq);
            lemma_merge_sorted_with_ensures(left_sorted, right_sorted, leq);
            lemma_multiset_commutative(left, right);
            lemma_multiset_commutative(left_sorted, right_sorted);
            assert forall|x: A| !self.contains(x) implies !(#[trigger] self.sort_by(leq).contains(
                x,
            )) by {
                self.to_multiset_ensures();
                self.sort_by(leq).to_multiset_ensures();
                assert(!self.contains(x) ==> self.to_multiset().count(x) == 0);
            }
        }
    }

    /// Returns the sequence containing only the elements of the original sequence
    /// such that pred(element) is true.
    ///
    /// ## Example
    ///
    /// ```rust
    /// proof fn filter_test() {
    ///    let seq: Seq<int> = seq![1, 2, 3, 4, 5];
    ///    let even: Seq<int> = seq.filter(|x| x % 2 == 0);
    ///    reveal_with_fuel(Seq::<int>::filter, 6); //Needed for Verus to unfold the recursive definition of filter
    ///    assert(even =~= seq![2, 4]);
    /// }
    /// ```
    #[verifier::opaque]
    pub open spec fn filter(self, pred: spec_fn(A) -> bool) -> Self
        decreases self.len(),
    {
        if self.len() == 0 {
            self
        } else {
            let subseq = self.drop_last().filter(pred);
            if pred(self.last()) {
                subseq.push(self.last())
            } else {
                subseq
            }
        }
    }

    pub broadcast proof fn filter_lemma(self, pred: spec_fn(A) -> bool)
        ensures
    // we don't keep anything bad
    // TODO(andrea): recommends didn't catch this error, where i isn't known to be in
    // self.filter(pred).len()
    //forall |i: int| 0 <= i < self.len() ==> pred(#[trigger] self.filter(pred)[i]),

            forall|i: int|
                0 <= i < self.filter(pred).len() ==> pred(#[trigger] self.filter(pred)[i]),
            // we keep everything we should
            forall|i: int|
                0 <= i < self.len() && pred(self[i]) ==> #[trigger] self.filter(pred).contains(
                    self[i],
                ),
            // the filtered list can't grow
            #[trigger] self.filter(pred).len() <= self.len(),
        decreases self.len(),
    {
        reveal(Seq::filter);
        let out = self.filter(pred);
        if 0 < self.len() {
            self.drop_last().filter_lemma(pred);
            assert forall|i: int| 0 <= i < out.len() implies pred(out[i]) by {
                if i < out.len() - 1 {
                    assert(self.drop_last().filter(pred)[i] == out.drop_last()[i]);  // trigger drop_last
                    assert(pred(out[i]));  // TODO(andrea): why is this line required? It's the conclusion of the assert-forall.
                }
            }
            assert forall|i: int|
                0 <= i < self.len() && pred(self[i]) implies #[trigger] out.contains(self[i]) by {
                if i == self.len() - 1 {
                    assert(self[i] == out[out.len() - 1]);  // witness to contains
                } else {
                    let subseq = self.drop_last().filter(pred);
                    assert(subseq.contains(self.drop_last()[i]));  // trigger recursive invocation
                    let j = choose|j| 0 <= j < subseq.len() && subseq[j] == self[i];
                    assert(out[j] == self[i]);  // TODO(andrea): same, seems needless
                }
            }
        }
    }

    pub broadcast proof fn filter_distributes_over_add(a: Self, b: Self, pred: spec_fn(A) -> bool)
        ensures
            #[trigger] (a + b).filter(pred) == a.filter(pred) + b.filter(pred),
        decreases b.len(),
    {
        reveal(Seq::filter);
        if 0 < b.len() {
            Self::drop_last_distributes_over_add(a, b);
            Self::filter_distributes_over_add(a, b.drop_last(), pred);
            if pred(b.last()) {
                Self::push_distributes_over_add(
                    a.filter(pred),
                    b.drop_last().filter(pred),
                    b.last(),
                );
            }
        } else {
            Self::add_empty_right(a, b);
            Self::add_empty_right(a.filter(pred), b.filter(pred));
        }
    }

    pub broadcast proof fn add_empty_left(a: Self, b: Self)
        requires
            a.len() == 0,
        ensures
            #[trigger] (a + b) == b,
    {
        assert(a + b =~= b);
    }

    pub broadcast proof fn add_empty_right(a: Self, b: Self)
        requires
            b.len() == 0,
        ensures
            #[trigger] (a + b) == a,
    {
        assert(a + b =~= a);
    }

    pub broadcast proof fn push_distributes_over_add(a: Self, b: Self, elt: A)
        ensures
            #[trigger] (a + b).push(elt) == a + b.push(elt),
    {
        assert((a + b).push(elt) =~= a + b.push(elt));
    }

    /// Returns the maximum value in a non-empty sequence, given sorting function leq
    pub open spec fn max_via(self, leq: spec_fn(A, A) -> bool) -> A
        recommends
            self.len() > 0,
        decreases self.len(),
    {
        if self.len() > 1 {
            if leq(self[0], self.subrange(1, self.len() as int).max_via(leq)) {
                self.subrange(1, self.len() as int).max_via(leq)
            } else {
                self[0]
            }
        } else {
            self[0]
        }
    }

    /// Returns the minimum value in a non-empty sequence, given sorting function leq
    pub open spec fn min_via(self, leq: spec_fn(A, A) -> bool) -> A
        recommends
            self.len() > 0,
        decreases self.len(),
    {
        if self.len() > 1 {
            let subseq = self.subrange(1, self.len() as int);
            let elt = subseq.min_via(leq);
            if leq(elt, self[0]) {
                elt
            } else {
                self[0]
            }
        } else {
            self[0]
        }
    }

    // TODO is_sorted -- extract from summer_school e22
    pub open spec fn contains(self, needle: A) -> bool {
        exists|i: int| 0 <= i < self.len() && self[i] == needle
    }

    /// Returns an index where `needle` appears in the sequence.
    /// Returns an arbitrary value if the sequence does not contain the `needle`.
    pub open spec fn index_of(self, needle: A) -> int {
        choose|i: int| 0 <= i < self.len() && self[i] == needle
    }

    /// For an element that occurs at least once in a sequence, if its first occurence
    /// is at index i, Some(i) is returned. Otherwise, None is returned
    pub closed spec fn index_of_first(self, needle: A) -> (result: Option<int>) {
        if self.contains(needle) {
            Some(self.first_index_helper(needle))
        } else {
            None
        }
    }

    // Recursive helper function for index_of_first
    spec fn first_index_helper(self, needle: A) -> int
        recommends
            self.contains(needle),
        decreases self.len(),
    {
        if self.len() <= 0 {
            -1  //arbitrary, will never get to this case

        } else if self[0] == needle {
            0
        } else {
            1 + self.subrange(1, self.len() as int).first_index_helper(needle)
        }
    }

    pub proof fn index_of_first_ensures(self, needle: A)
        ensures
            match self.index_of_first(needle) {
                Some(index) => {
                    &&& self.contains(needle)
                    &&& 0 <= index < self.len()
                    &&& self[index] == needle
                    &&& forall|j: int| 0 <= j < index < self.len() ==> self[j] != needle
                },
                None => { !self.contains(needle) },
            },
        decreases self.len(),
    {
        if self.contains(needle) {
            let index = self.index_of_first(needle).unwrap();
            if self.len() <= 0 {
            } else if self[0] == needle {
            } else {
                assert(Seq::empty().push(self.first()).add(self.drop_first()) =~= self);
                self.drop_first().index_of_first_ensures(needle);
            }
        }
    }

    /// For an element that occurs at least once in a sequence, if its last occurence
    /// is at index i, Some(i) is returned. Otherwise, None is returned
    pub closed spec fn index_of_last(self, needle: A) -> Option<int> {
        if self.contains(needle) {
            Some(self.last_index_helper(needle))
        } else {
            None
        }
    }

    // Recursive helper function for last_index_of
    spec fn last_index_helper(self, needle: A) -> int
        recommends
            self.contains(needle),
        decreases self.len(),
    {
        if self.len() <= 0 {
            -1  //arbitrary, will never get to this case

        } else if self.last() == needle {
            self.len() - 1
        } else {
            self.drop_last().last_index_helper(needle)
        }
    }

    pub proof fn index_of_last_ensures(self, needle: A)
        ensures
            match self.index_of_last(needle) {
                Some(index) => {
                    &&& self.contains(needle)
                    &&& 0 <= index < self.len()
                    &&& self[index] == needle
                    &&& forall|j: int| 0 <= index < j < self.len() ==> self[j] != needle
                },
                None => { !self.contains(needle) },
            },
        decreases self.len(),
    {
        if self.contains(needle) {
            let index = self.index_of_last(needle).unwrap();
            if self.len() <= 0 {
            } else if self.last() == needle {
            } else {
                assert(self.drop_last().push(self.last()) =~= self);
                self.drop_last().index_of_last_ensures(needle);
            }
        }
    }

    /// Drops the last element of a sequence and returns a sequence whose length is
    /// thereby 1 smaller.
    ///
    /// If the input sequence is empty, the result is meaningless and arbitrary.
    pub open spec fn drop_last(self) -> Seq<A>
        recommends
            self.len() >= 1,
    {
        self.subrange(0, self.len() as int - 1)
    }

    /// Dropping the last element of a concatenation of `a` and `b` is equivalent
    /// to skipping the last element of `b` and then concatenating `a` and `b`
    pub proof fn drop_last_distributes_over_add(a: Self, b: Self)
        requires
            0 < b.len(),
        ensures
            (a + b).drop_last() == a + b.drop_last(),
    {
        assert_seqs_equal!((a+b).drop_last(), a+b.drop_last());
    }

    pub open spec fn drop_first(self) -> Seq<A>
        recommends
            self.len() >= 1,
    {
        self.subrange(1, self.len() as int)
    }

    /// returns `true` if the sequence has no duplicate elements
    pub open spec fn no_duplicates(self) -> bool {
        forall|i, j| (0 <= i < self.len() && 0 <= j < self.len() && i != j) ==> self[i] != self[j]
    }

    /// Returns `true` if two sequences are disjoint
    pub open spec fn disjoint(self, other: Self) -> bool {
        forall|i: int, j: int| 0 <= i < self.len() && 0 <= j < other.len() ==> self[i] != other[j]
    }

    /// Converts a sequence into a set
    pub open spec fn to_set(self) -> Set<A> {
        Set::new(|a: A| self.contains(a))
    }

    /// Converts a sequence into a multiset
    pub closed spec fn to_multiset(self) -> Multiset<A>
        decreases self.len(),
    {
        if self.len() == 0 {
            Multiset::<A>::empty()
        } else {
            Multiset::<A>::empty().insert(self.first()).add(self.drop_first().to_multiset())
        }
    }

    /// Proof of function to_multiset() correctness
    pub proof fn to_multiset_ensures(self)
        ensures
            forall|a: A| #[trigger] (self.push(a).to_multiset()) =~= self.to_multiset().insert(a),
            self.len() == self.to_multiset().len(),
            forall|a: A| self.contains(a) <==> #[trigger] self.to_multiset().count(a) > 0,
    {
        assert forall|a: A| #[trigger]
            (self.push(a).to_multiset()) =~= self.to_multiset().insert(a) by {
            to_multiset_build(self, a);
        }
        to_multiset_len(self);
        assert forall|a: A| self.contains(a) <==> #[trigger] self.to_multiset().count(a) > 0 by {
            to_multiset_contains(self, a);
        }
    }

    /// Insert item a at index i, shifting remaining elements (if any) to the right
    pub open spec fn insert(self, i: int, a: A) -> Seq<A>
        recommends
            0 <= i <= self.len(),
    {
        self.subrange(0, i).push(a) + self.subrange(i, self.len() as int)
    }

    /// Proof of correctness and expected properties of insert function
    pub proof fn insert_ensures(self, pos: int, elt: A)
        requires
            0 <= pos <= self.len(),
        ensures
            self.insert(pos, elt).len() == self.len() + 1,
            forall|i: int| 0 <= i < pos ==> #[trigger] self.insert(pos, elt)[i] == self[i],
            forall|i: int| pos <= i < self.len() ==> self.insert(pos, elt)[i + 1] == self[i],
            self.insert(pos, elt)[pos] == elt,
    {
    }

    /// Remove item at index i, shifting remaining elements to the left
    pub open spec fn remove(self, i: int) -> Seq<A>
        recommends
            0 <= i < self.len(),
    {
        self.subrange(0, i) + self.subrange(i + 1, self.len() as int)
    }

    /// Proof of function remove() correctness
    pub proof fn remove_ensures(self, i: int)
        requires
            0 <= i < self.len(),
        ensures
            self.remove(i).len() == self.len() - 1,
            forall|index: int| 0 <= index < i ==> #[trigger] self.remove(i)[index] == self[index],
            forall|index: int|
                i <= index < self.len() - 1 ==> #[trigger] self.remove(i)[index] == self[index + 1],
    {
    }

    /// If a given element occurs at least once in a sequence, the sequence without
    /// its first occurrence is returned. Otherwise the same sequence is returned.
    pub open spec fn remove_value(self, val: A) -> Seq<A> {
        let index = self.index_of_first(val);
        match index {
            Some(i) => self.remove(i),
            None => self,
        }
    }

    /// Returns the sequence that is in reverse order to a given sequence.
    pub open spec fn reverse(self) -> Seq<A>
        decreases self.len(),
    {
        if self.len() == 0 {
            Seq::empty()
        } else {
            Seq::new(self.len(), |i: int| self[self.len() - 1 - i])
        }
    }

    /// Zips two sequences of equal length into one sequence that consists of pairs.
    /// If the two sequences are different lengths, returns an empty sequence
    pub open spec fn zip_with<B>(self, other: Seq<B>) -> Seq<(A, B)>
        recommends
            self.len() == other.len(),
        decreases self.len(),
    {
        if self.len() != other.len() {
            Seq::empty()
        } else if self.len() == 0 {
            Seq::empty()
        } else {
            Seq::new(self.len(), |i: int| (self[i], other[i]))
        }
    }

    /// Folds the sequence to the left, applying `f` to perform the fold.
    ///
    /// Equivalent to `Iterator::fold` in Rust.
    ///
    /// Given a sequence `s = [x0, x1, x2, ..., xn]`, applying this function `s.fold_left(b, f)`
    /// returns `f(...f(f(b, x0), x1), ..., xn)`.
    pub open spec fn fold_left<B>(self, b: B, f: spec_fn(B, A) -> B) -> (res: B)
        decreases self.len(),
    {
        if self.len() == 0 {
            b
        } else {
            f(self.drop_last().fold_left(b, f), self.last())
        }
    }

    /// Equivalent to [`Self::fold_left`] but defined by breaking off the leftmost element when
    /// recursing, rather than the rightmost. See [`Self::lemma_fold_left_alt`] that proves
    /// equivalence.
    pub open spec fn fold_left_alt<B>(self, b: B, f: spec_fn(B, A) -> B) -> (res: B)
        decreases self.len(),
    {
        if self.len() == 0 {
            b
        } else {
            self.subrange(1, self.len() as int).fold_left_alt(f(b, self[0]), f)
        }
    }

    /// An auxiliary lemma for proving [`Self::lemma_fold_left_alt`].
    proof fn aux_lemma_fold_left_alt<B>(self, b: B, f: spec_fn(B, A) -> B, k: int)
        requires
            0 < k <= self.len(),
        ensures
            self.subrange(k, self.len() as int).fold_left_alt(
                self.subrange(0, k).fold_left_alt(b, f),
                f,
            ) == self.fold_left_alt(b, f),
        decreases k,
    {
        reveal_with_fuel(Seq::fold_left_alt, 2);
        if k == 1 {
            // trivial base case
        } else {
            self.subrange(1, self.len() as int).aux_lemma_fold_left_alt(f(b, self[0]), f, k - 1);
            assert_seqs_equal!(
                self.subrange(1, self.len() as int)
                    .subrange(k - 1, self.subrange(1, self.len() as int).len() as int) ==
                self.subrange(k, self.len() as int)
            );
            assert_seqs_equal!(
                self.subrange(1, self.len() as int).subrange(0, k - 1) ==
                self.subrange(1, k)
            );
            assert_seqs_equal!(
                self.subrange(0, k).subrange(1, self.subrange(0, k).len() as int) ==
                self.subrange(1, k)
            );
        }
    }

    /// [`Self::fold_left`] and [`Self::fold_left_alt`] are equivalent.
    pub proof fn lemma_fold_left_alt<B>(self, b: B, f: spec_fn(B, A) -> B)
        ensures
            self.fold_left(b, f) == self.fold_left_alt(b, f),
        decreases self.len(),
    {
        reveal_with_fuel(Seq::fold_left, 2);
        reveal_with_fuel(Seq::fold_left_alt, 2);
        if self.len() <= 1 {
            // trivial base cases
        } else {
            self.aux_lemma_fold_left_alt(b, f, self.len() - 1);
            self.subrange(self.len() - 1, self.len() as int).lemma_fold_left_alt(
                self.drop_last().fold_left_alt(b, f),
                f,
            );
            self.subrange(0, self.len() - 1).lemma_fold_left_alt(b, f);
        }
    }

    /// Folds the sequence to the right, applying `f` to perform the fold.
    ///
    /// Equivalent to `DoubleEndedIterator::rfold` in Rust.
    ///
    /// Given a sequence `s = [x0, x1, x2, ..., xn]`, applying this function `s.fold_right(b, f)`
    /// returns `f(x0, f(x1, f(x2, ..., f(xn, b)...)))`.
    pub open spec fn fold_right<B>(self, f: spec_fn(A, B) -> B, b: B) -> (res: B)
        decreases self.len(),
    {
        if self.len() == 0 {
            b
        } else {
            self.drop_last().fold_right(f, f(self.last(), b))
        }
    }

    /// Equivalent to [`Self::fold_right`] but defined by breaking off the leftmost element when
    /// recursing, rather than the rightmost. See [`Self::lemma_fold_right_alt`] that proves
    /// equivalence.
    pub open spec fn fold_right_alt<B>(self, f: spec_fn(A, B) -> B, b: B) -> (res: B)
        decreases self.len(),
    {
        if self.len() == 0 {
            b
        } else {
            f(self[0], self.subrange(1, self.len() as int).fold_right_alt(f, b))
        }
    }

    /// An auxiliary lemma for proving [`Self::lemma_fold_right_alt`].
    proof fn aux_lemma_fold_right_alt<B>(self, f: spec_fn(A, B) -> B, b: B, k: int)
        requires
            0 <= k < self.len(),
        ensures
            self.subrange(0, k).fold_right(f, self.subrange(k, self.len() as int).fold_right(f, b))
                == self.fold_right(f, b),
        decreases self.len(),
    {
        reveal_with_fuel(Seq::fold_right, 2);
        if k == self.len() - 1 {
            // trivial base case
        } else {
            self.subrange(0, self.len() - 1).aux_lemma_fold_right_alt(f, f(self.last(), b), k);
            assert_seqs_equal!(
                self.subrange(0, self.len() - 1).subrange(0, k) ==
                self.subrange(0, k)
            );
            assert_seqs_equal!(
                self.subrange(0, self.len() - 1).subrange(k, self.subrange(0, self.len() - 1).len() as int) ==
                self.subrange(k, self.len() - 1)
            );
            assert_seqs_equal!(
                self.subrange(k, self.len() as int).drop_last() ==
                self.subrange(k, self.len() - 1)
            );
        }
    }

    /// [`Self::fold_right`] and [`Self::fold_right_alt`] are equivalent.
    pub proof fn lemma_fold_right_alt<B>(self, f: spec_fn(A, B) -> B, b: B)
        ensures
            self.fold_right(f, b) == self.fold_right_alt(f, b),
        decreases self.len(),
    {
        reveal_with_fuel(Seq::fold_right, 2);
        reveal_with_fuel(Seq::fold_right_alt, 2);
        if self.len() <= 1 {
            // trivial base cases
        } else {
            self.subrange(1, self.len() as int).lemma_fold_right_alt(f, b);
            self.aux_lemma_fold_right_alt(f, b, 1);
        }
    }

    // Proven lemmas
    /// Given a sequence with no duplicates, each element occurs only
    /// once in its conversion to a multiset
    pub proof fn lemma_multiset_has_no_duplicates(self)
        requires
            self.no_duplicates(),
        ensures
            forall|x: A| self.to_multiset().contains(x) ==> self.to_multiset().count(x) == 1,
        decreases self.len(),
    {
        broadcast use super::multiset::group_multiset_axioms;

        if self.len() == 0 {
            assert(forall|x: A|
                self.to_multiset().contains(x) ==> self.to_multiset().count(x) == 1);
        } else {
            lemma_seq_properties::<A>();
            assert(self.drop_last().push(self.last()) =~= self);
            self.drop_last().lemma_multiset_has_no_duplicates();
        }
    }

    /// The concatenation of two subsequences derived from a non-empty sequence,
    /// the first obtained from skipping the last element, the second consisting only
    /// of the last element, is the original sequence.
    pub proof fn lemma_add_last_back(self)
        requires
            0 < self.len(),
        ensures
            #[trigger] self.drop_last().push(self.last()) =~= self,
    {
    }

    /// If a predicate is true at every index of a sequence,
    /// it is true for every member of the sequence as a collection.
    /// Useful for converting quantifiers between the two forms
    /// to satisfy a precondition in the latter form.
    pub proof fn lemma_indexing_implies_membership(self, f: spec_fn(A) -> bool)
        requires
            forall|i: int| 0 <= i < self.len() ==> #[trigger] f(#[trigger] self[i]),
        ensures
            forall|x: A| #[trigger] self.contains(x) ==> #[trigger] f(x),
    {
        assert(forall|i: int| 0 <= i < self.len() ==> #[trigger] self.contains(self[i]));
    }

    /// If a predicate is true for every member of a sequence as a collection,
    /// it is true at every index of the sequence.
    /// Useful for converting quantifiers between the two forms
    /// to satisfy a precondition in the latter form.
    pub proof fn lemma_membership_implies_indexing(self, f: spec_fn(A) -> bool)
        requires
            forall|x: A| #[trigger] self.contains(x) ==> #[trigger] f(x),
        ensures
            forall|i: int| 0 <= i < self.len() ==> #[trigger] f(self[i]),
    {
        assert forall|i: int| 0 <= i < self.len() implies #[trigger] f(self[i]) by {
            assert(self.contains(self[i]));
        }
    }

    /// A sequence that is sliced at the pos-th element, concatenated
    /// with that same sequence sliced from the pos-th element, is equal to the
    /// original unsliced sequence.
    pub proof fn lemma_split_at(self, pos: int)
        requires
            0 <= pos <= self.len(),
        ensures
            self.subrange(0, pos) + self.subrange(pos, self.len() as int) =~= self,
    {
    }

    /// Any element in a slice is included in the original sequence.
    pub proof fn lemma_element_from_slice(self, new: Seq<A>, a: int, b: int, pos: int)
        requires
            0 <= a <= b <= self.len(),
            new == self.subrange(a, b),
            a <= pos < b,
        ensures
            pos - a < new.len(),
            new[pos - a] == self[pos],
    {
    }

    /// A slice (from s2..e2) of a slice (from s1..e1) of a sequence is equal to just a
    /// slice (s1+s2..s1+e2) of the original sequence.
    pub proof fn lemma_slice_of_slice(self, s1: int, e1: int, s2: int, e2: int)
        requires
            0 <= s1 <= e1 <= self.len(),
            0 <= s2 <= e2 <= e1 - s1,
        ensures
            self.subrange(s1, e1).subrange(s2, e2) =~= self.subrange(s1 + s2, s1 + e2),
    {
    }

    /// A sequence of unique items, when converted to a set, produces a set with matching length
    pub proof fn unique_seq_to_set(self)
        requires
            self.no_duplicates(),
        ensures
            self.len() == self.to_set().len(),
        decreases self.len(),
    {
        broadcast use super::set::group_set_axioms;

        seq_to_set_equal_rec::<A>(self);
        if self.len() == 0 {
        } else {
            let rest = self.drop_last();
            rest.unique_seq_to_set();
            seq_to_set_equal_rec::<A>(rest);
            seq_to_set_rec_is_finite::<A>(rest);
            assert(!seq_to_set_rec(rest).contains(self.last()));
            assert(seq_to_set_rec(rest).insert(self.last()).len() == seq_to_set_rec(rest).len()
                + 1);
        }
    }

    /// The cardinality of a set of elements is always less than or
    /// equal to that of the full sequence of elements.
    pub proof fn lemma_cardinality_of_set(self)
        ensures
            self.to_set().len() <= self.len(),
        decreases self.len(),
    {
        broadcast use super::set::group_set_axioms, seq_to_set_is_finite;

        lemma_seq_properties::<A>();
        lemma_set_properties::<A>();
        if self.len() == 0 {
        } else {
            assert(self.drop_last().to_set().insert(self.last()) =~= self.to_set());
            self.drop_last().lemma_cardinality_of_set();
        }
    }

    /// A sequence is of length 0 if and only if its conversion to
    /// a set results in the empty set.
    pub proof fn lemma_cardinality_of_empty_set_is_0(self)
        ensures
            self.to_set().len() == 0 <==> self.len() == 0,
    {
        broadcast use super::set::group_set_axioms, seq_to_set_is_finite;

        assert(self.len() == 0 ==> self.to_set().len() == 0) by { self.lemma_cardinality_of_set() }
        assert(!(self.len() == 0) ==> !(self.to_set().len() == 0)) by {
            if self.len() > 0 {
                assert(self.to_set().contains(self[0]));
                assert(self.to_set().remove(self[0]).len() <= self.to_set().len());
            }
        }
    }

    /// A sequence with cardinality equal to its set has no duplicates.
    /// Inverse property of that shown in lemma unique_seq_to_set
    pub proof fn lemma_no_dup_set_cardinality(self)
        requires
            self.to_set().len() == self.len(),
        ensures
            self.no_duplicates(),
        decreases self.len(),
    {
        broadcast use super::set::group_set_axioms, seq_to_set_is_finite;

        lemma_seq_properties::<A>();
        if self.len() == 0 {
        } else {
            assert(self =~= Seq::empty().push(self.first()).add(self.drop_first()));
            if self.drop_first().contains(self.first()) {
                // If there is a duplicate, then we show that |s.to_set()| == |s| cannot hold.
                assert(self.to_set() =~= self.drop_first().to_set());
                assert(self.to_set().len() <= self.drop_first().len()) by {
                    self.drop_first().lemma_cardinality_of_set()
                }
            } else {
                assert(self.to_set().len() == 1 + self.drop_first().to_set().len()) by {
                    assert(self.drop_first().to_set().insert(self.first()) =~= self.to_set());
                }
                self.drop_first().lemma_no_dup_set_cardinality();
            }
        }
    }
}

impl<A, B> Seq<(A, B)> {
    /// Unzips a sequence that contains pairs into two separate sequences.
    pub closed spec fn unzip(self) -> (Seq<A>, Seq<B>) {
        (Seq::new(self.len(), |i: int| self[i].0), Seq::new(self.len(), |i: int| self[i].1))
    }

    /// Proof of correctness and expected properties of unzip function
    pub proof fn unzip_ensures(self)
        ensures
            self.unzip().0.len() == self.unzip().1.len(),
            self.unzip().0.len() == self.len(),
            self.unzip().1.len() == self.len(),
            forall|i: int|
                0 <= i < self.len() ==> (#[trigger] self.unzip().0[i], #[trigger] self.unzip().1[i])
                    == self[i],
        decreases self.len(),
    {
        if self.len() > 0 {
            self.drop_last().unzip_ensures();
        }
    }

    /// Unzipping a sequence of sequences and then zipping the resulting two sequences
    /// back together results in the original sequence of sequences.
    pub proof fn lemma_zip_of_unzip(self)
        ensures
            self.unzip().0.zip_with(self.unzip().1) =~= self,
    {
    }
}

impl<A> Seq<Seq<A>> {
    /// Flattens a sequence of sequences into a single sequence by concatenating
    /// subsequences, starting from the first element.
    ///
    /// ## Example
    ///
    /// ```rust
    /// proof fn flatten_test() {
    ///    let seq: Seq<Seq<int>> = seq![seq![1, 2, 3], seq![4, 5, 6], seq![7, 8, 9]];
    ///    let flat: Seq<int> = seq.flatten();
    ///    reveal_with_fuel(Seq::<Seq<int>>::flatten, 5); //Needed for Verus to unfold the recursive definition of flatten
    ///    assert(flat =~= seq![1, 2, 3, 4, 5, 6, 7, 8, 9]);
    /// }
    /// ```
    pub open spec fn flatten(self) -> Seq<A>
        decreases self.len(),
    {
        if self.len() == 0 {
            Seq::empty()
        } else {
            self.first().add(self.drop_first().flatten())
        }
    }

    /// Flattens a sequence of sequences into a single sequence by concatenating
    /// subsequences in reverse order, i.e. starting from the last element.
    /// This is equivalent to a call to `flatten`, but with concatenation operation
    /// applied along the oppositive associativity for the sake of proof reasoning in that direction.
    pub open spec fn flatten_alt(self) -> Seq<A>
        decreases self.len(),
    {
        if self.len() == 0 {
            Seq::empty()
        } else {
            self.drop_last().flatten_alt().add(self.last())
        }
    }

    /// Flattening a sequence of a sequence x, where x has length 1,
    /// results in a sequence equivalent to the single element of x
    pub proof fn lemma_flatten_one_element(self)
        ensures
            self.len() == 1 ==> self.flatten() == self.first(),
    {
        broadcast use Seq::add_empty_right;

        if self.len() == 1 {
            assert(self.flatten() =~= self.first().add(self.drop_first().flatten()));
        }
    }

    /// The length of a flattened sequence of sequences x is greater than or
    /// equal to any of the lengths of the elements of x.
    pub proof fn lemma_flatten_length_ge_single_element_length(self, i: int)
        requires
            0 <= i < self.len(),
        ensures
            self.flatten_alt().len() >= self[i].len(),
        decreases self.len(),
    {
        if self.len() == 1 {
            self.lemma_flatten_one_element();
            self.lemma_flatten_and_flatten_alt_are_equivalent();
        } else if i < self.len() - 1 {
            self.drop_last().lemma_flatten_length_ge_single_element_length(i);
        } else {
            assert(self.flatten_alt() == self.drop_last().flatten_alt().add(self.last()));
        }
    }

    /// The length of a flattened sequence of sequences x is less than or equal
    /// to the length of x multiplied by a number greater than or equal to the
    /// length of the longest sequence in x.
    pub proof fn lemma_flatten_length_le_mul(self, j: int)
        requires
            forall|i: int| 0 <= i < self.len() ==> (#[trigger] self[i]).len() <= j,
        ensures
            self.flatten_alt().len() <= self.len() * j,
        decreases self.len(),
    {
        lemma_seq_properties::<A>();
        lemma_seq_properties::<Seq<A>>();
        if self.len() == 0 {
        } else {
            self.drop_last().lemma_flatten_length_le_mul(j);
            assert((self.len() - 1) * j == (self.len() * j) - (1 * j)) by (nonlinear_arith);  //TODO: use math library after imported
        }
    }

    /// Flattening sequences of sequences in order (starting from the beginning)
    /// and in reverse order (starting from the end) results in the same sequence.
    pub proof fn lemma_flatten_and_flatten_alt_are_equivalent(self)
        ensures
            self.flatten() =~= self.flatten_alt(),
        decreases self.len(),
    {
        broadcast use Seq::add_empty_right, Seq::push_distributes_over_add;

        if self.len() != 0 {
            self.drop_last().lemma_flatten_and_flatten_alt_are_equivalent();
            // let s = self.drop_last().flatten();
            // let s2 = self.drop_last().flatten_alt();
            // assert(s == s2);
            seq![self.last()].lemma_flatten_one_element();
            assert(seq![self.last()].flatten() == self.last());
            lemma_flatten_concat(self.drop_last(), seq![self.last()]);
            assert((self.drop_last() + seq![self.last()]).flatten() == self.drop_last().flatten()
                + self.last());
            assert(self.drop_last() + seq![self.last()] =~= self);
            assert(self.flatten_alt() == self.drop_last().flatten_alt() + self.last());
        }
    }
}

/********************************* Extrema in Sequences *********************************/

impl Seq<int> {
    /// Returns the maximum integer value in a non-empty sequence of integers.
    pub open spec fn max(self) -> int
        recommends
            0 < self.len(),
        decreases self.len(),
    {
        if self.len() == 1 {
            self[0]
        } else if self.len() == 0 {
            0
        } else {
            let later_max = self.drop_first().max();
            if self[0] >= later_max {
                self[0]
            } else {
                later_max
            }
        }
    }

    /// Proof of correctness and expected properties for max function
    pub proof fn max_ensures(self)
        ensures
            forall|x: int| self.contains(x) ==> x <= self.max(),
            forall|i: int| 0 <= i < self.len() ==> self[i] <= self.max(),
            self.len() == 0 || self.contains(self.max()),
        decreases self.len(),
    {
        if self.len() <= 1 {
        } else {
            let elt = self.drop_first().max();
            assert(self.drop_first().contains(elt)) by { self.drop_first().max_ensures() }
            assert forall|i: int| 0 <= i < self.len() implies self[i] <= self.max() by {
                assert(i == 0 || self[i] == self.drop_first()[i - 1]);
                assert(forall|j: int|
                    0 <= j < self.drop_first().len() ==> self.drop_first()[j]
                        <= self.drop_first().max()) by { self.drop_first().max_ensures() }
            }
        }
    }

    /// Returns the minimum integer value in a non-empty sequence of integers.
    pub open spec fn min(self) -> int
        recommends
            0 < self.len(),
        decreases self.len(),
    {
        if self.len() == 1 {
            self[0]
        } else if self.len() == 0 {
            0
        } else {
            let later_min = self.drop_first().min();
            if self[0] <= later_min {
                self[0]
            } else {
                later_min
            }
        }
    }

    /// Proof of correctness and expected properties for min function
    pub proof fn min_ensures(self)
        ensures
            forall|x: int| self.contains(x) ==> self.min() <= x,
            forall|i: int| 0 <= i < self.len() ==> self.min() <= self[i],
            self.len() == 0 || self.contains(self.min()),
        decreases self.len(),
    {
        if self.len() <= 1 {
        } else {
            let elt = self.drop_first().min();
            assert(self.subrange(1, self.len() as int).contains(elt)) by {
                self.drop_first().min_ensures()
            }
            assert forall|i: int| 0 <= i < self.len() implies self.min() <= self[i] by {
                assert(i == 0 || self[i] == self.drop_first()[i - 1]);
                assert(forall|j: int|
                    0 <= j < self.drop_first().len() ==> self.drop_first().min()
                        <= self.drop_first()[j]) by { self.drop_first().min_ensures() }
            }
        }
    }

    pub closed spec fn sort(self) -> Self {
        self.sort_by(|x: int, y: int| x <= y)
    }

    pub proof fn lemma_sort_ensures(self)
        ensures
            self.to_multiset() =~= self.sort().to_multiset(),
            sorted_by(self.sort(), |x: int, y: int| x <= y),
    {
        self.lemma_sort_by_ensures(|x: int, y: int| x <= y);
    }

    /// The maximum element in a non-empty sequence is greater than or equal to
    /// the maxima of its non-empty subsequences.
    pub proof fn lemma_subrange_max(self, from: int, to: int)
        requires
            0 <= from < to <= self.len(),
        ensures
            self.subrange(from, to).max() <= self.max(),
    {
        self.max_ensures();
        self.subrange(from, to).max_ensures();
    }

    /// The minimum element in a non-empty sequence is less than or equal to
    /// the minima of its non-empty subsequences.
    pub proof fn lemma_subrange_min(self, from: int, to: int)
        requires
            0 <= from < to <= self.len(),
        ensures
            self.subrange(from, to).min() >= self.min(),
    {
        self.min_ensures();
        self.subrange(from, to).min_ensures();
    }
}

// Helper function to aid with merge sort
spec fn merge_sorted_with<A>(left: Seq<A>, right: Seq<A>, leq: spec_fn(A, A) -> bool) -> Seq<A>
    recommends
        sorted_by(left, leq),
        sorted_by(right, leq),
        total_ordering(leq),
    decreases left.len(), right.len(),
{
    if left.len() == 0 {
        right
    } else if right.len() == 0 {
        left
    } else if leq(left.first(), right.first()) {
        Seq::<A>::empty().push(left.first()) + merge_sorted_with(left.drop_first(), right, leq)
    } else {
        Seq::<A>::empty().push(right.first()) + merge_sorted_with(left, right.drop_first(), leq)
    }
}

proof fn lemma_merge_sorted_with_ensures<A>(left: Seq<A>, right: Seq<A>, leq: spec_fn(A, A) -> bool)
    requires
        sorted_by(left, leq),
        sorted_by(right, leq),
        total_ordering(leq),
    ensures
        (left + right).to_multiset() =~= merge_sorted_with(left, right, leq).to_multiset(),
        sorted_by(merge_sorted_with(left, right, leq), leq),
    decreases left.len(), right.len(),
{
    lemma_seq_properties::<A>();
    if left.len() == 0 {
        assert(left + right =~= right);
    } else if right.len() == 0 {
        assert(left + right =~= left);
    } else if leq(left.first(), right.first()) {
        let result = Seq::<A>::empty().push(left.first()) + merge_sorted_with(
            left.drop_first(),
            right,
            leq,
        );
        lemma_merge_sorted_with_ensures(left.drop_first(), right, leq);
        let rest = merge_sorted_with(left.drop_first(), right, leq);
        assert(rest.len() == 0 || rest.first() == left.drop_first().first() || rest.first()
            == right.first()) by {
            if left.drop_first().len() == 0 {
            } else if leq(left.drop_first().first(), right.first()) {
                assert(rest =~= Seq::<A>::empty().push(left.drop_first().first())
                    + merge_sorted_with(left.drop_first().drop_first(), right, leq));
            } else {
                assert(rest =~= Seq::<A>::empty().push(right.first()) + merge_sorted_with(
                    left.drop_first(),
                    right.drop_first(),
                    leq,
                ));
            }
        }
        lemma_new_first_element_still_sorted_by(left.first(), rest, leq);
        assert((left.drop_first() + right) =~= (left + right).drop_first());
    } else {
        let result = Seq::<A>::empty().push(right.first()) + merge_sorted_with(
            left,
            right.drop_first(),
            leq,
        );
        lemma_merge_sorted_with_ensures(left, right.drop_first(), leq);
        let rest = merge_sorted_with(left, right.drop_first(), leq);
        assert(rest.len() == 0 || rest.first() == left.first() || rest.first()
            == right.drop_first().first()) by {
            assert(left.len() > 0);
            if right.drop_first().len() == 0 {  /*assert(rest =~= left);*/
            } else if leq(left.first(), right.drop_first().first()) {  //right might be length 1
                assert(rest =~= Seq::<A>::empty().push(left.first()) + merge_sorted_with(
                    left.drop_first(),
                    right.drop_first(),
                    leq,
                ));
            } else {
                assert(rest =~= Seq::<A>::empty().push(right.drop_first().first())
                    + merge_sorted_with(left, right.drop_first().drop_first(), leq));
            }
        }
        lemma_new_first_element_still_sorted_by(
            right.first(),
            merge_sorted_with(left, right.drop_first(), leq),
            leq,
        );
        lemma_seq_union_to_multiset_commutative(left, right);
        assert((right.drop_first() + left) =~= (right + left).drop_first());
        lemma_seq_union_to_multiset_commutative(right.drop_first(), left);
    }
}

/// The maximum of the concatenation of two non-empty sequences is greater than or
/// equal to the maxima of its two non-empty subsequences.
pub proof fn lemma_max_of_concat(x: Seq<int>, y: Seq<int>)
    requires
        0 < x.len() && 0 < y.len(),
    ensures
        x.max() <= (x + y).max(),
        y.max() <= (x + y).max(),
        forall|elt: int| (x + y).contains(elt) ==> elt <= (x + y).max(),
    decreases x.len(),
{
    lemma_seq_properties::<int>();
    x.max_ensures();
    y.max_ensures();
    (x + y).max_ensures();
    assert(x.drop_first().len() == x.len() - 1);
    if x.len() == 1 {
        assert(y.max() <= (x + y).max()) by {
            assert((x + y).contains(y.max()));
        }
    } else {
        assert(x.max() <= (x + y).max()) by {
            assert(x.contains(x.max()));
            assert((x + y).contains(x.max()));
        }
        assert(x.drop_first() + y =~= (x + y).drop_first());
        lemma_max_of_concat(x.drop_first(), y);
    }
}

/// The minimum of the concatenation of two non-empty sequences is less than or
/// equal to the minimum of its two non-empty subsequences.
pub proof fn lemma_min_of_concat(x: Seq<int>, y: Seq<int>)
    requires
        0 < x.len() && 0 < y.len(),
    ensures
        (x + y).min() <= x.min(),
        (x + y).min() <= y.min(),
        forall|elt: int| (x + y).contains(elt) ==> (x + y).min() <= elt,
    decreases x.len(),
{
    x.min_ensures();
    y.min_ensures();
    (x + y).min_ensures();
    lemma_seq_properties::<int>();
    if x.len() == 1 {
        assert((x + y).min() <= y.min()) by {
            assert((x + y).contains(y.min()));
        }
    } else {
        assert((x + y).min() <= x.min()) by {
            assert((x + y).contains(x.min()));
        }
        assert((x + y).min() <= y.min()) by {
            assert((x + y).contains(y.min()));
        }
        assert(x.drop_first() + y =~= (x + y).drop_first());
        lemma_max_of_concat(x.drop_first(), y)
    }
}

/************************* Sequence to Multiset Conversion **************************/

/// push(a) o to_multiset = to_multiset o insert(a)
proof fn to_multiset_build<A>(s: Seq<A>, a: A)
    ensures
        s.push(a).to_multiset() =~= s.to_multiset().insert(a),
    decreases s.len(),
{
    broadcast use super::multiset::group_multiset_axioms;

    if s.len() == 0 {
        assert(s.to_multiset() =~= Multiset::<A>::empty());
        assert(s.push(a).drop_first() =~= Seq::<A>::empty());
        assert(s.push(a).to_multiset() =~= Multiset::<A>::empty().insert(a).add(
            Seq::<A>::empty().to_multiset(),
        ));
    } else {
        to_multiset_build(s.drop_first(), a);
        assert(s.drop_first().push(a).to_multiset() =~= s.drop_first().to_multiset().insert(a));
        assert(s.push(a).drop_first() =~= s.drop_first().push(a));
    }
}

/// to_multiset() preserves length
proof fn to_multiset_len<A>(s: Seq<A>)
    ensures
        s.len() == s.to_multiset().len(),
    decreases s.len(),
{
    broadcast use super::multiset::group_multiset_axioms;

    if s.len() == 0 {
        assert(s.to_multiset() =~= Multiset::<A>::empty());
        assert(s.len() == 0);
    } else {
        to_multiset_len(s.drop_first());
        assert(s.len() == s.drop_first().len() + 1);
        assert(s.to_multiset().len() == s.drop_first().to_multiset().len() + 1);
    }
}

/// to_multiset() contains only the elements of the sequence
proof fn to_multiset_contains<A>(s: Seq<A>, a: A)
    ensures
        s.contains(a) <==> s.to_multiset().count(a) > 0,
    decreases s.len(),
{
    broadcast use super::multiset::group_multiset_axioms;

    if s.len() != 0 {
        // ==>
        if s.contains(a) {
            if s.first() == a {
                to_multiset_build(s, a);
                assert(s.to_multiset() =~= Multiset::<A>::empty().insert(s.first()).add(
                    s.drop_first().to_multiset(),
                ));
                assert(Multiset::<A>::empty().insert(s.first()).contains(s.first()));
            } else {
                to_multiset_contains(s.drop_first(), a);
                assert(s.skip(1) =~= s.drop_first());
                lemma_seq_skip_contains(s, 1, a);
                assert(s.to_multiset().count(a) == s.drop_first().to_multiset().count(a));
                assert(s.contains(a) <==> s.to_multiset().count(a) > 0);
            }
        }
        // <==

        if s.to_multiset().count(a) > 0 {
            to_multiset_contains(s.drop_first(), a);
            assert(s.contains(a) <==> s.to_multiset().count(a) > 0);
        } else {
            assert(s.contains(a) <==> s.to_multiset().count(a) > 0);
        }
    }
}

/// The last element of two concatenated sequences, the second one being non-empty, will be the
/// last element of the latter sequence.
pub proof fn lemma_append_last<A>(s1: Seq<A>, s2: Seq<A>)
    requires
        0 < s2.len(),
    ensures
        (s1 + s2).last() == s2.last(),
{
}

/// The concatenation of sequences is associative
pub proof fn lemma_concat_associative<A>(s1: Seq<A>, s2: Seq<A>, s3: Seq<A>)
    ensures
        s1.add(s2.add(s3)) =~= s1.add(s2).add(s3),
{
}

/// Recursive definition of seq to set conversion
spec fn seq_to_set_rec<A>(seq: Seq<A>) -> Set<A>
    decreases seq.len(),
{
    if seq.len() == 0 {
        Set::empty()
    } else {
        seq_to_set_rec(seq.drop_last()).insert(seq.last())
    }
}

// Helper function showing that the recursive definition of set_to_seq produces a finite set
proof fn seq_to_set_rec_is_finite<A>(seq: Seq<A>)
    ensures
        seq_to_set_rec(seq).finite(),
    decreases seq.len(),
{
    broadcast use super::set::group_set_axioms;

    if seq.len() > 0 {
        let sub_seq = seq.drop_last();
        assert(seq_to_set_rec(sub_seq).finite()) by {
            seq_to_set_rec_is_finite(sub_seq);
        }
    }
}

// Helper function showing that the resulting set contains all elements of the sequence
proof fn seq_to_set_rec_contains<A>(seq: Seq<A>)
    ensures
        forall|a| #[trigger] seq.contains(a) <==> seq_to_set_rec(seq).contains(a),
    decreases seq.len(),
{
    broadcast use super::set::group_set_axioms;

    if seq.len() > 0 {
        assert(forall|a| #[trigger]
            seq.drop_last().contains(a) <==> seq_to_set_rec(seq.drop_last()).contains(a)) by {
            seq_to_set_rec_contains(seq.drop_last());
        }
        assert(seq =~= seq.drop_last().push(seq.last()));
        assert forall|a| #[trigger] seq.contains(a) <==> seq_to_set_rec(seq).contains(a) by {
            if !seq.drop_last().contains(a) {
                if a == seq.last() {
                    assert(seq.contains(a));
                    assert(seq_to_set_rec(seq).contains(a));
                } else {
                    assert(!seq_to_set_rec(seq).contains(a));
                }
            }
        }
    }
}

// Helper function showing that the recursive definition matches the set comprehension one
proof fn seq_to_set_equal_rec<A>(seq: Seq<A>)
    ensures
        seq.to_set() == seq_to_set_rec(seq),
{
    broadcast use super::set::group_set_axioms;

    assert(forall|n| #[trigger] seq.contains(n) <==> seq_to_set_rec(seq).contains(n)) by {
        seq_to_set_rec_contains(seq);
    }
    assert(forall|n| #[trigger] seq.contains(n) <==> seq.to_set().contains(n));
    assert(seq.to_set() =~= seq_to_set_rec(seq));
}

/// The set obtained from a sequence is finite
pub broadcast proof fn seq_to_set_is_finite<A>(seq: Seq<A>)
    ensures
        #[trigger] seq.to_set().finite(),
{
    broadcast use super::set::group_set_axioms;

    assert(seq.to_set().finite()) by {
        seq_to_set_equal_rec(seq);
        seq_to_set_rec_is_finite(seq);
    }
}

/// If sequences a and b don't have duplicates, and there are no
/// elements in common between them, then the concatenated sequence
/// a + b will not contain duplicates either.
pub proof fn lemma_no_dup_in_concat<A>(a: Seq<A>, b: Seq<A>)
    requires
        a.no_duplicates(),
        b.no_duplicates(),
        forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < b.len() ==> a[i] != b[j],
    ensures
        #[trigger] (a + b).no_duplicates(),
{
}

/// Flattening sequences of sequences is distributive over concatenation. That is, concatenating
/// the flattening of two sequences of sequences is the same as flattening the
/// concatenation of two sequences of sequences.
pub proof fn lemma_flatten_concat<A>(x: Seq<Seq<A>>, y: Seq<Seq<A>>)
    ensures
        (x + y).flatten() =~= x.flatten() + y.flatten(),
    decreases x.len(),
{
    if x.len() == 0 {
        assert(x + y =~= y);
    } else {
        assert((x + y).drop_first() =~= x.drop_first() + y);
        assert(x.first() + (x.drop_first() + y).flatten() =~= x.first() + x.drop_first().flatten()
            + y.flatten()) by {
            lemma_flatten_concat(x.drop_first(), y);
        }
    }
}

/// Flattening sequences of sequences in reverse order is distributive over concatentation.
/// That is, concatenating the flattening of two sequences of sequences in reverse
/// order is the same as flattening the concatenation of two sequences of sequences
/// in reverse order.
pub proof fn lemma_flatten_alt_concat<A>(x: Seq<Seq<A>>, y: Seq<Seq<A>>)
    ensures
        (x + y).flatten_alt() =~= x.flatten_alt() + y.flatten_alt(),
    decreases y.len(),
{
    if y.len() == 0 {
        assert(x + y =~= x);
    } else {
        assert((x + y).drop_last() =~= x + y.drop_last());
        assert((x + y.drop_last()).flatten_alt() + y.last() =~= x.flatten_alt()
            + y.drop_last().flatten_alt() + y.last()) by {
            lemma_flatten_alt_concat(x, y.drop_last());
        }
    }
}

/// The multiset of a concatenated sequence `a + b` is equivalent to the multiset of the
/// concatenated sequence `b + a`.
pub proof fn lemma_seq_union_to_multiset_commutative<A>(a: Seq<A>, b: Seq<A>)
    ensures
        (a + b).to_multiset() =~= (b + a).to_multiset(),
{
    broadcast use super::multiset::group_multiset_axioms;

    lemma_multiset_commutative(a, b);
    lemma_multiset_commutative(b, a);
}

/// The multiset of a concatenated sequence `a + b` is equivalent to the multiset of just
/// sequence `a` added to the multiset of just sequence `b`.
pub proof fn lemma_multiset_commutative<A>(a: Seq<A>, b: Seq<A>)
    ensures
        (a + b).to_multiset() =~= a.to_multiset().add(b.to_multiset()),
    decreases a.len(),
{
    broadcast use super::multiset::group_multiset_axioms;

    if a.len() == 0 {
        assert(a + b =~= b);
    } else {
        lemma_multiset_commutative(a.drop_first(), b);
        assert(a.drop_first() + b =~= (a + b).drop_first());
    }
}

/// Any two sequences that are sorted by a total order and that have the same elements are equal.
pub proof fn lemma_sorted_unique<A>(x: Seq<A>, y: Seq<A>, leq: spec_fn(A, A) -> bool)
    requires
        sorted_by(x, leq),
        sorted_by(y, leq),
        total_ordering(leq),
        x.to_multiset() == y.to_multiset(),
    ensures
        x =~= y,
    decreases x.len(), y.len(),
{
    broadcast use super::multiset::group_multiset_axioms;

    x.to_multiset_ensures();
    y.to_multiset_ensures();
    if x.len() == 0 || y.len() == 0 {
    } else {
        assert(x.to_multiset().contains(x[0]));
        assert(x.to_multiset().contains(y[0]));
        let i = choose|i: int| #![trigger x.spec_index(i) ] 0 <= i < x.len() && x[i] == y[0];
        assert(leq(x[i], x[0]));
        assert(leq(x[0], x[i]));
        assert(x.drop_first().to_multiset() =~= x.to_multiset().remove(x[0]));
        assert(y.drop_first().to_multiset() =~= y.to_multiset().remove(y[0]));
        lemma_sorted_unique(x.drop_first(), y.drop_first(), leq);
        assert(x.drop_first() =~= y.drop_first());
        assert(x.first() == y.first());
        assert(x =~= Seq::<A>::empty().push(x.first()).add(x.drop_first()));
        assert(x =~= y);
    }
}

// This verified lemma used to be an axiom in the Dafny prelude
pub proof fn lemma_seq_contains<A>(s: Seq<A>, x: A)
    ensures
        s.contains(x) <==> exists|i: int| 0 <= i < s.len() && s[i] == x,
{
}

// This verified lemma used to be an axiom in the Dafny prelude
/// The empty sequence contains nothing
pub proof fn lemma_seq_empty_contains_nothing<A>(x: A)
    ensures
        !Seq::<A>::empty().contains(x),
{
}

// This verified lemma used to be an axiom in the Dafny prelude
// Note: Dafny only does one way implication, but theoretically it could go both ways
/// A sequence with length 0 is equivalent to the empty sequence
pub proof fn lemma_seq_empty_equality<A>(s: Seq<A>)
    ensures
        s.len() == 0 ==> s =~= Seq::<A>::empty(),
{
}

// This verified lemma used to be an axiom in the Dafny prelude
/// The concatenation of two sequences contains only the elements
/// of the two sequences
pub proof fn lemma_seq_concat_contains_all_elements<A>(x: Seq<A>, y: Seq<A>, elt: A)
    ensures
        (x + y).contains(elt) <==> x.contains(elt) || y.contains(elt),
    decreases x.len(),
{
    if x.len() == 0 && y.len() > 0 {
        assert((x + y) =~= y);
    } else {
        assert forall|elt: A| #[trigger] x.contains(elt) implies #[trigger] (x + y).contains(
            elt,
        ) by {
            let index = choose|i: int| 0 <= i < x.len() && x[i] == elt;
            assert((x + y)[index] == elt);
        }
        assert forall|elt: A| #[trigger] y.contains(elt) implies #[trigger] (x + y).contains(
            elt,
        ) by {
            let index = choose|i: int| 0 <= i < y.len() && y[i] == elt;
            assert((x + y)[index + x.len()] == elt);
        }
    }
}

// This verified lemma used to be an axiom in the Dafny prelude
/// After pushing an element onto a sequence, the sequence contains that element
pub proof fn lemma_seq_contains_after_push<A>(s: Seq<A>, v: A, x: A)
    ensures
        (s.push(v).contains(x) <==> v == x || s.contains(x)) && s.push(v).contains(v),
{
    assert forall|elt: A| #[trigger] s.contains(elt) implies #[trigger] s.push(v).contains(elt) by {
        let index = choose|i: int| 0 <= i < s.len() && s[i] == elt;
        assert(s.push(v)[index] == elt);
    }
    assert(s.push(v)[s.len() as int] == v);
}

// This verified lemma used to be an axiom in the Dafny prelude
/// The subrange of a sequence contains only the elements within the indices `start` and `stop`
/// of the original sequence.
pub proof fn lemma_seq_subrange_elements<A>(s: Seq<A>, start: int, stop: int, x: A)
    requires
        0 <= start <= stop <= s.len(),
    ensures
        s.subrange(start, stop).contains(x) <==> (exists|i: int|
            0 <= start <= i < stop <= s.len() && s[i] == x),
{
    assert((exists|i: int| 0 <= start <= i < stop <= s.len() && s[i] == x) ==> s.subrange(
        start,
        stop,
    ).contains(x)) by {
        if exists|i: int| 0 <= start <= i < stop <= s.len() && s[i] == x {
            let index = choose|i: int| 0 <= start <= i < stop <= s.len() && s[i] == x;
            assert(s.subrange(start, stop)[index - start] == s[index]);
        }
    }
}

/************************** Lemmas about Take/Skip ***************************/

// This verified lemma used to be an axiom in the Dafny prelude
/// Taking the first `n` elements of a sequence results in a sequence of length `n`,
/// as long as `n` is within the bounds of the original sequence.
pub proof fn lemma_seq_take_len<A>(s: Seq<A>, n: int)
    ensures
        0 <= n <= s.len() ==> s.take(n).len() == n,
{
}

// This verified lemma used to be an axiom in the Dafny prelude
/// The resulting sequence after taking the first `n` elements from sequence `s` contains
/// element `x` if and only if `x` is contained in the first `n` elements of `s`.
pub proof fn lemma_seq_take_contains<A>(s: Seq<A>, n: int, x: A)
    requires
        0 <= n <= s.len(),
    ensures
        s.take(n).contains(x) <==> (exists|i: int| 0 <= i < n <= s.len() && s[i] == x),
{
    assert((exists|i: int| 0 <= i < n <= s.len() && #[trigger] s[i] == x) ==> s.take(n).contains(x))
        by {
        if exists|i: int| 0 <= i < n <= s.len() && #[trigger] s[i] == x {
            let index = choose|i: int| 0 <= i < n <= s.len() && #[trigger] s[i] == x;
            assert(s.take(n)[index] == s[index]);
        }
    }
}

// This verified lemma used to be an axiom in the Dafny prelude
/// If `j` is a valid index less than `n`, then the `j`th element of the sequence `s`
/// is the same as `j`th element of the sequence after taking the first `n` elements of `s`.
pub proof fn lemma_seq_take_index<A>(s: Seq<A>, n: int, j: int)
    ensures
        0 <= j < n <= s.len() ==> s.take(n)[j] == s[j],
{
}

// This verified lemma used to be an axiom in the Dafny prelude
/// Skipping the first `n` elements of a sequence gives a sequence of length `n` less than
/// the original sequence's length.
pub proof fn lemma_seq_skip_len<A>(s: Seq<A>, n: int)
    ensures
        0 <= n <= s.len() ==> s.skip(n).len() == s.len() - n,
{
}

// This verified lemma used to be an axiom in the Dafny prelude
/// The resulting sequence after skipping the first `n` elements from sequence `s` contains
/// element `x` if and only if `x` is contained in `s` before index `n`.
pub proof fn lemma_seq_skip_contains<A>(s: Seq<A>, n: int, x: A)
    requires
        0 <= n <= s.len(),
    ensures
        s.skip(n).contains(x) <==> (exists|i: int| 0 <= n <= i < s.len() && s[i] == x),
{
    assert((exists|i: int| 0 <= n <= i < s.len() && #[trigger] s[i] == x) ==> s.skip(n).contains(x))
        by {
        let index = choose|i: int| 0 <= n <= i < s.len() && #[trigger] s[i] == x;
        lemma_seq_skip_index(s, n, index - n);
    }
}

// This verified lemma used to be an axiom in the Dafny prelude
/// If `j` is a valid index less than `s.len() - n`, then the `j`th element of the sequence
/// `s.skip(n)` is the same as the `j+n`th element of the sequence `s`.
pub proof fn lemma_seq_skip_index<A>(s: Seq<A>, n: int, j: int)
    ensures
        0 <= n && 0 <= j < (s.len() - n) ==> s.skip(n)[j] == s[j + n],
{
}

// This verified lemma used to be an axiom in the Dafny prelude
/// If `k` is a valid index between `n` (inclusive) and the length of sequence `s` (exclusive),
/// then the `k-n`th element of the sequence `s.skip(n)` is the same as the `k`th element of the
/// original sequence `s`.
pub proof fn lemma_seq_skip_index2<A>(s: Seq<A>, n: int, k: int)
    ensures
        0 <= n <= k < s.len() ==> (s.skip(n))[k - n] == s[k],
{
}

// This verified lemma used to be an axiom in the Dafny prelude
/// If `n` is the length of sequence `a`, then taking the first `n` elements of the concatenation
/// `a + b` is equivalent to the sequence `a` and skipping the first `n` elements of the concatenation
/// `a + b` is equivalent to the sequence `b`.
pub proof fn lemma_seq_append_take_skip<A>(a: Seq<A>, b: Seq<A>, n: int)
    ensures
        n == a.len() ==> ((a + b).take(n) =~= a && (a + b).skip(n) =~= b),
{
}

/************* Lemmas about the Commutability of Take and Skip with Update ************/

// This verified lemma used to be an axiom in the Dafny prelude
/// If `i` is in the first `n` indices of sequence `s`, updating sequence `s` at index `i` with
/// value `v` and then taking the first `n` elements is equivalent to first taking the first `n`
/// elements of `s` and then updating index `i` to value `v`.
pub proof fn lemma_seq_take_update_commut1<A>(s: Seq<A>, i: int, v: A, n: int)
    ensures
        0 <= i < n <= s.len() ==> #[trigger] s.update(i, v).take(n) =~= s.take(n).update(i, v),
{
}

// This verified lemma used to be an axiom in the Dafny prelude
/// If `i` is a valid index after the first `n` indices of sequence `s`, updating sequence `s` at
/// index `i` with value `v` and then taking the first `n` elements is equivalent to just taking the first `n`
/// elements of `s` without the update.
pub proof fn lemma_seq_take_update_commut2<A>(s: Seq<A>, i: int, v: A, n: int)
    ensures
        0 <= n <= i < s.len() ==> #[trigger] s.update(i, v).take(n) =~= s.take(n),
{
}

// This verified lemma used to be an axiom in the Dafny prelude
/// If `i` is a valid index after the first `n` indices of sequence `s`, updating sequence `s` at
/// index `i` with value `v` and then skipping the first `n` elements is equivalent to skipping the first `n`
/// elements of `s` and then updating index `i-n` to value `v`.
pub proof fn lemma_seq_skip_update_commut1<A>(s: Seq<A>, i: int, v: A, n: int)
    ensures
        0 <= n <= i < s.len() ==> #[trigger] s.update(i, v).skip(n) =~= s.skip(n).update(i - n, v),
{
}

// This verified lemma used to be an axiom in the Dafny prelude
/// If `i` is a valid index in the first `n` indices of sequence `s`, updating sequence `s` at
/// index `i` with value `v` and then skipping the first `n` elements is equivalent to just skipping
/// the first `n` elements without the update.
pub proof fn lemma_seq_skip_update_commut2<A>(s: Seq<A>, i: int, v: A, n: int)
    ensures
        0 <= i < n <= s.len() ==> s.update(i, v).skip(n) =~= s.skip(n),
{
}

// This verified lemma used to be an axiom in the Dafny prelude
/// Pushing element `v` onto the end of sequence `s` and then skipping the first `n` elements is
/// equivalent to skipping the first `n` elements of `s` and then pushing `v` onto the end.
pub proof fn lemma_seq_skip_build_commut<A>(s: Seq<A>, v: A, n: int)
    ensures
        0 <= n <= s.len() ==> s.push(v).skip(n) =~= s.skip(n).push(v),
{
}

// This verified lemma used to be an axiom in the Dafny prelude
/// `s.skip(0)` is equivalent to `s`.
pub proof fn lemma_seq_skip_nothing<A>(s: Seq<A>, n: int)
    ensures
        n == 0 ==> s.skip(n) =~= s,
{
}

// This verified lemma used to be an axiom in the Dafny prelude
/// `s.take(0)` is equivalent to the empty sequence.
pub proof fn lemma_seq_take_nothing<A>(s: Seq<A>, n: int)
    ensures
        n == 0 ==> s.take(n) =~= Seq::<A>::empty(),
{
}

// This verified lemma used to be an axiom in the Dafny prelude
/// If `m + n` is less than or equal to the length of sequence `s`, then skipping the first `m` elements
/// and then skipping the first `n` elements of the resulting sequence is equivalent to just skipping
/// the first `m + n` elements.
pub proof fn lemma_seq_skip_of_skip<A>(s: Seq<A>, m: int, n: int)
    ensures
        (0 <= m && 0 <= n && m + n <= s.len()) ==> s.skip(m).skip(n) =~= s.skip(m + n),
{
}

/// Properties of sequences from the Dafny prelude (which were axioms in Dafny, but proven here in Verus)
pub proof fn lemma_seq_properties<A>()
    ensures
        forall|s: Seq<A>, x: A|
            s.contains(x) <==> exists|i: int| 0 <= i < s.len() && #[trigger] s[i] == x,  //from lemma_seq_contains(s, x),
        forall|x: A| !(#[trigger] Seq::<A>::empty().contains(x)),  //from lemma_seq_empty_contains_nothing(x),
        forall|s: Seq<A>| #[trigger] s.len() == 0 ==> s =~= Seq::<A>::empty(),  //from lemma_seq_empty_equality(s),
        forall|x: Seq<A>, y: Seq<A>, elt: A| #[trigger]
            (x + y).contains(elt) <==> x.contains(elt) || y.contains(elt),  //from lemma_seq_concat_contains_all_elements(x, y, elt),
        forall|s: Seq<A>, v: A, x: A|
            (#[trigger] s.push(v).contains(x) <==> v == x || s.contains(x)) && #[trigger] s.push(
                v,
            ).contains(v),  //from lemma_seq_contains_after_push(s, v, x)
        forall|s: Seq<A>, start: int, stop: int, x: A|
            (0 <= start <= stop <= s.len() && #[trigger] s.subrange(start, stop).contains(x)) <==> (
            exists|i: int| 0 <= start <= i < stop <= s.len() && #[trigger] s[i] == x),  //from lemma_seq_subrange_elements(s, start, stop, x),
        forall|s: Seq<A>, n: int| 0 <= n <= s.len() ==> #[trigger] s.take(n).len() == n,  //from lemma_seq_take_len(s, n)
        forall|s: Seq<A>, n: int, x: A|
            (#[trigger] s.take(n).contains(x) && 0 <= n <= s.len()) <==> (exists|i: int|
                0 <= i < n <= s.len() && #[trigger] s[i] == x),  //from lemma_seq_take_contains(s, n, x),
        forall|s: Seq<A>, n: int, j: int| 0 <= j < n <= s.len() ==> #[trigger] s.take(n)[j] == s[j],  //from lemma_seq_take_index(s, n, j),
        forall|s: Seq<A>, n: int| 0 <= n <= s.len() ==> #[trigger] s.skip(n).len() == s.len() - n,  //from lemma_seq_skip_len(s, n),
        forall|s: Seq<A>, n: int, x: A|
            (#[trigger] s.skip(n).contains(x) && 0 <= n <= s.len()) <==> (exists|i: int|
                0 <= n <= i < s.len() && #[trigger] s[i] == x),  //from lemma_seq_skip_contains(s, n, x),
        forall|s: Seq<A>, n: int, j: int|
            0 <= n && 0 <= j < (s.len() - n) ==> #[trigger] s.skip(n)[j] == s[j + n],  //from lemma_seq_skip_index(s, n, j),
        forall|a: Seq<A>, b: Seq<A>, n: int|
            #![trigger (a+b).take(n)]
            #![trigger (a+b).skip(n)]
            n == a.len() ==> ((a + b).take(n) =~= a && (a + b).skip(n) =~= b),  //from lemma_seq_append_take_skip(a, b, n),
        forall|s: Seq<A>, i: int, v: A, n: int|
            0 <= i < n <= s.len() ==> #[trigger] s.update(i, v).take(n) == s.take(n).update(i, v),  //from lemma_seq_take_update_commut1(s, i, v, n),
        forall|s: Seq<A>, i: int, v: A, n: int|
            0 <= n <= i < s.len() ==> #[trigger] s.update(i, v).take(n) == s.take(n),  //from lemma_seq_take_update_commut2(s, i, v, n),
        forall|s: Seq<A>, i: int, v: A, n: int|
            0 <= n <= i < s.len() ==> #[trigger] s.update(i, v).skip(n) == s.skip(n).update(
                i - n,
                v,
            ),  //from lemma_seq_skip_update_commut1(s, i, v, n),
        forall|s: Seq<A>, i: int, v: A, n: int|
            0 <= i < n <= s.len() ==> #[trigger] s.update(i, v).skip(n) == s.skip(n),  //from lemma_seq_skip_update_commut2(s, i, v, n),
        forall|s: Seq<A>, v: A, n: int|
            0 <= n <= s.len() ==> #[trigger] s.push(v).skip(n) == s.skip(n).push(v),  //from lemma_seq_skip_build_commut(s, v, n),
        forall|s: Seq<A>, n: int| n == 0 ==> #[trigger] s.skip(n) == s,  //from lemma_seq_skip_nothing(s, n),
        forall|s: Seq<A>, n: int| n == 0 ==> #[trigger] s.take(n) == Seq::<A>::empty(),  //from lemma_seq_take_nothing(s, n),
        forall|s: Seq<A>, m: int, n: int|
            (0 <= m && 0 <= n && m + n <= s.len()) ==> s.skip(m).skip(n) == s.skip(m + n),  //from lemma_seq_skip_of_skip(s, m, n),
        forall|s: Seq<A>, a: A| #[trigger] (s.push(a).to_multiset()) =~= s.to_multiset().insert(a),  //from o_multiset_properties
        forall|s: Seq<A>| s.len() == #[trigger] s.to_multiset().len(),  //from to_multiset_ensures
        forall|s: Seq<A>, a: A|
            s.contains(a) <==> #[trigger] s.to_multiset().count(a)
                > 0,  //from to_multiset_ensures
{
    assert forall|x: Seq<A>, y: Seq<A>, elt: A| #[trigger] (x + y).contains(elt) implies x.contains(
        elt,
    ) || y.contains(elt) by {
        lemma_seq_concat_contains_all_elements(x, y, elt);
    }
    assert forall|x: Seq<A>, y: Seq<A>, elt: A|
        x.contains(elt) || y.contains(elt) implies #[trigger] (x + y).contains(elt) by {
        lemma_seq_concat_contains_all_elements(x, y, elt);
    }
    assert forall|s: Seq<A>, v: A, x: A| #[trigger] s.push(v).contains(x) implies v == x
        || s.contains(x) by {
        lemma_seq_contains_after_push(s, v, x);
    }
    assert forall|s: Seq<A>, v: A, x: A| v == x || s.contains(x) implies #[trigger] s.push(
        v,
    ).contains(x) by {
        lemma_seq_contains_after_push(s, v, x);
    }
    assert forall|s: Seq<A>, start: int, stop: int, x: A|
        0 <= start <= stop <= s.len() && #[trigger] s.subrange(start, stop).contains(
            x,
        ) implies exists|i: int| 0 <= start <= i < stop <= s.len() && #[trigger] s[i] == x by {
        lemma_seq_subrange_elements(s, start, stop, x);
    }
    assert forall|s: Seq<A>, start: int, stop: int, x: A|
        exists|i: int|
            0 <= start <= i < stop <= s.len() && #[trigger] s[i] == x implies #[trigger] s.subrange(
        start,
        stop,
    ).contains(x) by {
        lemma_seq_subrange_elements(s, start, stop, x);
    }
    assert forall|s: Seq<A>, n: int, x: A| #[trigger]
        s.take(n).contains(x) && 0 <= n <= s.len() implies (exists|i: int|
        0 <= i < n <= s.len() && #[trigger] s[i] == x) by {
        lemma_seq_take_contains(s, n, x);
    }
    assert forall|s: Seq<A>, n: int, x: A|
        (exists|i: int| 0 <= i < n <= s.len() && #[trigger] s[i] == x) implies #[trigger] s.take(
        n,
    ).contains(x) by {
        lemma_seq_take_contains(s, n, x);
    }
    assert forall|s: Seq<A>, n: int, j: int| 0 <= j < n <= s.len() implies #[trigger] s.take(n)[j]
        == s[j] by {
        lemma_seq_take_len(s, n);
        assert(0 <= n <= s.len() ==> s.take(n).len() == n);
        assert(0 <= n <= s.len());
        assert(s.take(n).len() == n);
        lemma_seq_take_index(s, n, j);
    }
    assert forall|s: Seq<A>, n: int, x: A| #[trigger]
        s.skip(n).contains(x) && 0 <= n <= s.len() implies (exists|i: int|
        0 <= n <= i < s.len() && #[trigger] s[i] == x) by {
        lemma_seq_skip_contains(s, n, x);
    }
    assert forall|s: Seq<A>, n: int, x: A|
        (exists|i: int| 0 <= n <= i < s.len() && #[trigger] s[i] == x) implies #[trigger] s.skip(
        n,
    ).contains(x) && 0 <= n <= s.len() by {
        lemma_seq_skip_contains(s, n, x);
    }
    assert forall|s: Seq<A>, i: int, v: A, n: int|
        0 <= i < n <= s.len() implies #[trigger] s.update(i, v).take(n) == s.take(n).update(
        i,
        v,
    ) by {
        lemma_seq_take_update_commut1(s, i, v, n);
    }
    assert forall|s: Seq<A>, i: int, v: A, n: int|
        0 <= n <= i < s.len() implies #[trigger] s.update(i, v).take(n) == s.take(n) by {
        lemma_seq_take_update_commut2(s, i, v, n);
    }
    assert forall|s: Seq<A>, i: int, v: A, n: int|
        0 <= n <= i < s.len() implies #[trigger] s.update(i, v).skip(n) == s.skip(n).update(
        i - n,
        v,
    ) by {
        lemma_seq_skip_update_commut1(s, i, v, n);
    }
    assert forall|s: Seq<A>, i: int, v: A, n: int|
        0 <= i < n <= s.len() implies #[trigger] s.update(i, v).skip(n) == s.skip(n) by {
        lemma_seq_skip_update_commut2(s, i, v, n);
    }
    assert forall|s: Seq<A>, v: A, n: int| 0 <= n <= s.len() implies #[trigger] s.push(v).skip(n)
        == s.skip(n).push(v) by {
        lemma_seq_skip_build_commut(s, v, n);
    }
    assert forall|s: Seq<A>, n: int| n == 0 implies #[trigger] s.skip(n) == s by {
        lemma_seq_skip_nothing(s, n);
    }
    assert forall|s: Seq<A>, n: int| n == 0 implies #[trigger] s.take(n) == Seq::<A>::empty() by {
        lemma_seq_take_nothing(s, n);
    }
    assert forall|s: Seq<A>, m: int, n: int| (0 <= m && 0 <= n && m + n <= s.len()) implies s.skip(
        m,
    ).skip(n) == s.skip(m + n) by {
        lemma_seq_skip_of_skip(s, m, n);
    }
    assert forall|s: Seq<A>, a: A| #[trigger]
        (s.push(a).to_multiset()) =~= s.to_multiset().insert(a) by {
        s.to_multiset_ensures();
    }
    assert forall|s: Seq<A>| s.len() == #[trigger] s.to_multiset().len() by {
        s.to_multiset_ensures();
    }
    assert forall|s: Seq<A>, a: A| s.contains(a) implies #[trigger] s.to_multiset().count(a)
        > 0 by {
        s.to_multiset_ensures();
    }
    assert forall|s: Seq<A>, a: A| #[trigger] s.to_multiset().count(a) > 0 implies s.contains(
        a,
    ) by {
        s.to_multiset_ensures();
    }
}

#[doc(hidden)]
#[verifier::inline]
pub open spec fn check_argument_is_seq<A>(s: Seq<A>) -> Seq<A> {
    s
}

/// Prove two sequences `s1` and `s2` are equal by proving that their elements are equal at each index.
///
/// More precisely, `assert_seqs_equal!` requires:
///  * `s1` and `s2` have the same length (`s1.len() == s2.len()`), and
///  * for all `i` in the range `0 <= i < s1.len()`, we have `s1[i] == s2[i]`.
///
/// The property that equality follows from these facts is often called _extensionality_.
///
/// `assert_seqs_equal!` can handle many trivial-looking
/// identities without any additional help:
///
/// ```rust
/// proof fn subrange_concat(s: Seq<u64>, i: int) {
///     requires([
///         0 <= i && i <= s.len(),
///     ]);
///
///     let t1 = s.subrange(0, i);
///     let t2 = s.subrange(i, s.len());
///     let t = t1.add(t2);
///
///     assert_seqs_equal!(s == t);
///
///     assert(s == t);
/// }
/// ```
///
/// In more complex cases, a proof may be required for the equality of each element pair.
/// For example,
///
/// ```rust
/// proof fn bitvector_seqs() {
///     let s = Seq::<u64>::new(5, |i| i as u64);
///     let t = Seq::<u64>::new(5, |i| i as u64 | 0);
///
///     assert_seqs_equal!(s == t, i => {
///         // Need to show that s[i] == t[i]
///         // Prove that the elements are equal by appealing to a bitvector solver:
///         let j = i as u64;
///         assert_bit_vector(j | 0 == j);
///         assert(s[i] == t[i]);
///     });
/// }
/// ```
#[macro_export]
macro_rules! assert_seqs_equal {
    [$($tail:tt)*] => {
        ::builtin_macros::verus_proof_macro_exprs!($crate::vstd::seq_lib::assert_seqs_equal_internal!($($tail)*))
    };
}

#[macro_export]
#[doc(hidden)]
macro_rules! assert_seqs_equal_internal {
    (::builtin::spec_eq($s1:expr, $s2:expr)) => {
        $crate::vstd::seq_lib::assert_seqs_equal_internal!($s1, $s2)
    };
    (::builtin::spec_eq($s1:expr, $s2:expr), $idx:ident => $bblock:block) => {
        $crate::vstd::seq_lib::assert_seqs_equal_internal!($s1, $s2, $idx => $bblock)
    };
    (crate::builtin::spec_eq($s1:expr, $s2:expr)) => {
        $crate::vstd::seq_lib::assert_seqs_equal_internal!($s1, $s2)
    };
    (crate::builtin::spec_eq($s1:expr, $s2:expr), $idx:ident => $bblock:block) => {
        $crate::vstd::seq_lib::assert_seqs_equal_internal!($s1, $s2, $idx => $bblock)
    };
    ($s1:expr, $s2:expr $(,)?) => {
        $crate::vstd::seq_lib::assert_seqs_equal_internal!($s1, $s2, idx => { })
    };
    ($s1:expr, $s2:expr, $idx:ident => $bblock:block) => {
        #[verifier::spec] let s1 = $crate::vstd::seq_lib::check_argument_is_seq($s1);
        #[verifier::spec] let s2 = $crate::vstd::seq_lib::check_argument_is_seq($s2);
        $crate::vstd::prelude::assert_by($crate::vstd::prelude::equal(s1, s2), {
            $crate::vstd::prelude::assert_(s1.len() == s2.len());
            $crate::vstd::prelude::assert_forall_by(|$idx : $crate::vstd::prelude::int| {
                $crate::vstd::prelude::requires(::builtin_macros::verus_proof_expr!(0 <= $idx && $idx < s1.len()));
                $crate::vstd::prelude::ensures($crate::vstd::prelude::equal(s1.index($idx), s2.index($idx)));
                { $bblock }
            });
            $crate::vstd::prelude::assert_($crate::vstd::prelude::ext_equal(s1, s2));
        });
    }
}

pub broadcast group group_seq_lib_default {
    Seq::filter_lemma,
    Seq::add_empty_left,
    Seq::add_empty_right,
    Seq::push_distributes_over_add,
    Seq::filter_distributes_over_add,
    seq_to_set_is_finite,
}

#[doc(hidden)]
pub use assert_seqs_equal_internal;
pub use assert_seqs_equal;

} // verus!
