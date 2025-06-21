#[allow(unused_imports)]
use super::calc_macro::*;
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

    /// Applies the function `f` to each element of the sequence,
    /// producing a sequence of sequences, and then concatenates (flattens)
    /// those into a single flat sequence of `B`.
    ///
    /// ## Example
    ///
    /// ```rust
    /// fn example() {
    ///     let s = seq![1, 2, 3];
    ///     let result = s.flat_map(|x| seq![x, x]);
    ///     assert_eq!(result, seq![1, 1, 2, 2, 3, 3]);
    /// }
    /// ``
    pub open spec fn flat_map<B>(self, f: spec_fn(A) -> Seq<B>) -> Seq<B> {
        self.map_values(f).flatten()
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
    /// {{#include ../../../../examples/multiset.rs:sorted_by_leq}}
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

    /// Tests if all elements in the sequence satisfy the predicate.
    ///
    /// ## Example
    ///
    /// ```rust
    /// fn example() {
    ///     let s = seq![2, 4, 6, 8];
    ///     assert!(s.all(|x| x % 2 == 0));
    /// }
    /// ```
    pub open spec fn all(self, pred: spec_fn(A) -> bool) -> bool {
        forall|i: int| 0 <= i < self.len() ==> #[trigger] pred(self[i])
    }

    /// Tests if any element in the sequence satisfies the predicate.
    ///
    /// ## Example
    ///
    /// ```rust
    /// fn example() {
    ///     let s = seq![1, 2, 3, 4];
    ///     assert!(s.any(|x| x > 3));
    /// }
    /// ```
    pub open spec fn any(self, pred: spec_fn(A) -> bool) -> bool {
        exists|i: int| 0 <= i < self.len() && #[trigger] pred(self[i])
    }

    /// Checks that exactly one element in the sequence satisfies the given predicate.
    /// ## Example
    ///
    /// ```rust
    /// fn example() {
    ///     let s = seq![1, 2, 3];
    ///     assert!(s.exactly_one(|x| x == 2));
    /// }
    /// ```
    pub open spec fn exactly_one(self, pred: spec_fn(A) -> bool) -> bool {
        self.filter(pred).len() == 1
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
                broadcast use group_to_multiset_ensures;

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

    pub broadcast proof fn lemma_filter_len(self, pred: spec_fn(A) -> bool)
        ensures
    // the filtered list can't grow

            #[trigger] self.filter(pred).len() <= self.len(),
        decreases self.len(),
    {
        reveal(Seq::filter);
        let out = self.filter(pred);
        if 0 < self.len() {
            self.drop_last().lemma_filter_len(pred);
        }
    }

    pub broadcast proof fn lemma_filter_pred(self, pred: spec_fn(A) -> bool, i: int)
        requires
            0 <= i < self.filter(pred).len(),
        ensures
            pred(#[trigger] self.filter(pred)[i]),
    {
        // TODO: remove this after proved filter_lemma is proved
        #[allow(deprecated)]
        self.filter_lemma(pred);
    }

    pub broadcast proof fn lemma_filter_contains(self, pred: spec_fn(A) -> bool, i: int)
        requires
            0 <= i < self.len() && pred(self[i]),
        ensures
            #[trigger] self.filter(pred).contains(self[i]),
    {
        // TODO: remove this after proved filter_lemma is proved
        #[allow(deprecated)]
        self.filter_lemma(pred);
    }

    // deprecated since the triggers inside of 2 of the conjuncts are blocked
    #[deprecated = "Use `broadcast use group_filter_ensures` instead" ]
    pub proof fn filter_lemma(self, pred: spec_fn(A) -> bool)
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

    // Parts of verified lemma used to be an axiom in the Dafny prelude
    // Note: the inner triggers in this lemma are blocked by `to_multiset_len`
    /// Proof of function to_multiset() correctness
    pub broadcast proof fn to_multiset_ensures(self)
        ensures
            forall|a: A| #[trigger] (self.push(a).to_multiset()) =~= self.to_multiset().insert(a),  // to_multiset_build
            forall|i: int|
                0 <= i < self.len() ==> #[trigger] (self.remove(i).to_multiset())
                    =~= self.to_multiset().remove(self[i]),  // to_multiset_remove
            self.len() == #[trigger] self.to_multiset().len(),  // to_multiset_len
            forall|a: A|
                self.contains(a) <==> #[trigger] self.to_multiset().count(a)
                    > 0,  // to_multiset_contains
    {
        broadcast use group_seq_properties;

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

    /// A lemma that proves how [`Self::fold_left`] distributes over splitting a sequence.
    pub broadcast proof fn lemma_fold_left_split<B>(self, b: B, f: spec_fn(B, A) -> B, k: int)
        requires
            0 <= k <= self.len(),
        ensures
            self.subrange(k, self.len() as int).fold_left(
                (#[trigger] self.subrange(0, k).fold_left(b, f)),
                f,
            ) == self.fold_left(b, f),
        decreases self.len(),
    {
        reveal_with_fuel(Seq::fold_left, 2);
        if k == self.len() {
            assert(self.subrange(0, self.len() as int) == self);
        } else {
            self.drop_last().lemma_fold_left_split(b, f, k);
            assert_seqs_equal!(
                self.drop_last().subrange(k, self.drop_last().len() as int) ==
                self.subrange(k, self.len()-1)
            );
            assert_seqs_equal!(
                self.drop_last().subrange(0, k) ==
                self.subrange(0, k)
            );
            assert_seqs_equal!(
                self.subrange(k, self.len() as int).drop_last() ==
                self.subrange(k, self.len() - 1)
            );
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

    /// A lemma that proves how [`Self::fold_right`] distributes over splitting a sequence.
    pub broadcast proof fn lemma_fold_right_split<B>(self, f: spec_fn(A, B) -> B, b: B, k: int)
        requires
            0 <= k <= self.len(),
        ensures
            self.subrange(0, k).fold_right(
                f,
                (#[trigger] self.subrange(k, self.len() as int).fold_right(f, b)),
            ) == self.fold_right(f, b),
        decreases self.len(),
    {
        reveal_with_fuel(Seq::fold_right, 2);
        if k == self.len() {
            assert(self.subrange(0, k) == self);
        } else if k == self.len() - 1 {
            // trivial base case
        } else {
            self.subrange(0, self.len() - 1).lemma_fold_right_split(f, f(self.last(), b), k);
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

    // Lemma that proves it's possible to commute a commutative operator across fold_right.
    pub proof fn lemma_fold_right_commute_one<B>(self, a: A, f: spec_fn(A, B) -> B, v: B)
        requires
            commutative_foldr(f),
        ensures
            self.fold_right(f, f(a, v)) == f(a, self.fold_right(f, v)),
        decreases self.len(),
    {
        if self.len() > 0 {
            self.drop_last().lemma_fold_right_commute_one(a, f, f(self.last(), v));
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
            self.lemma_fold_right_split(f, b, 1);
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
            broadcast use group_seq_properties;

            assert(self.drop_last().push(self.last()) =~= self);
            self.drop_last().lemma_multiset_has_no_duplicates();
        }
    }

    /// If, in a sequence's conversion to a multiset, each element occurs only once,
    /// the sequence has no duplicates.
    pub proof fn lemma_multiset_has_no_duplicates_conv(self)
        requires
            forall|x: A| self.to_multiset().contains(x) ==> self.to_multiset().count(x) == 1,
        ensures
            self.no_duplicates(),
    {
        broadcast use super::multiset::group_multiset_axioms;

        assert forall|i, j| (0 <= i < self.len() && 0 <= j < self.len() && i != j) implies self[i]
            != self[j] by {
            let mut a = if (i < j) {
                i
            } else {
                j
            };
            let mut b = if (i < j) {
                j
            } else {
                i
            };

            if (self[a] == self[b]) {
                let s0 = self.subrange(0, b);
                let s1 = self.subrange(b, self.len() as int);
                assert(self == s0 + s1);

                broadcast use group_to_multiset_ensures;

                lemma_multiset_commutative(s0, s1);
                assert(self.to_multiset().count(self[a]) >= 2);
            }
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
        broadcast use {super::set::group_set_axioms, seq_to_set_is_finite};
        broadcast use group_seq_properties;
        broadcast use super::set_lib::group_set_properties;

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
        broadcast use {super::set::group_set_axioms, seq_to_set_is_finite};

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
        broadcast use {super::set::group_set_axioms, seq_to_set_is_finite};

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

    /// Mapping a function over a sequence and converting to a set is the same
    /// as mapping it over the sequence converted to a set.
    pub broadcast proof fn lemma_to_set_map_commutes<B>(self, f: spec_fn(A) -> B)
        ensures
            #[trigger] self.to_set().map(f) =~= self.map_values(f).to_set(),
    {
        broadcast use crate::vstd::group_vstd_default;

        assert forall|elem: B|
            self.to_set().map(f).contains(elem) <==> self.map_values(f).to_set().contains(elem) by {
            if self.to_set().map(f).contains(elem) {
                let x = choose|x: A| self.to_set().contains(x) && f(x) == elem;
                let i = choose|i: int| 0 <= i < self.len() && self[i] == x;
                assert(self.map_values(f)[i] == elem);
            }
            if self.map_values(f).to_set().contains(elem) {
                let i = choose|i: int|
                    0 <= i < self.map_values(f).len() && self.map_values(f)[i] == elem;
                let x = self[i];
                assert(self.to_set().contains(x));
            }
        };
    }

    /// Appending an element to a sequence and converting to set, is equal
    /// to converting to set and inserting it.
    pub broadcast proof fn lemma_to_set_insert_commutes(sq: Seq<A>, elt: A)
        requires
        ensures
            #[trigger] (sq + seq![elt]).to_set() =~= sq.to_set().insert(elt),
    {
        broadcast use crate::vstd::group_vstd_default;
        broadcast use lemma_seq_concat_contains_all_elements;
        broadcast use lemma_seq_empty_contains_nothing;
        broadcast use lemma_seq_contains_after_push;
        broadcast use super::seq::group_seq_axioms;
        broadcast use super::set_lib::group_set_properties;

    }

    /// Update a subrange of a sequence starting at `off` to values `vs`.
    /// Expects that the updated subrange `off` up to `off+vs.len()` fits
    /// in the existing sequence.
    pub open spec fn update_subrange_with(self, off: int, vs: Self) -> Self
        recommends
            0 <= off,
            off + vs.len() <= self.len(),
    {
        Seq::new(
            self.len(),
            |i: int|
                if off <= i < off + vs.len() {
                    vs[i - off]
                } else {
                    self[i]
                },
        )
    }

    /// Skipping `i` elements and then 1 more is equivalent to skipping `i + 1` elements.
    ///
    /// ## Example
    ///
    /// ```rust
    /// proof fn example() {
    ///     let s = seq![1, 2, 3, 4];
    ///     s.lemma_seq_skip_skip(2);
    ///     assert(s.skip(2).skip(1) =~= s.skip(3));
    /// }
    /// ```
    pub broadcast proof fn lemma_seq_skip_skip(self, i: int)
        ensures
            0 <= i < self.len() ==> (self.skip(i)).skip(1) =~= #[trigger] self.skip(i + 1),
    {
        broadcast use group_seq_properties;

    }

    /// If an element is contained in a sequence, then there exists an index where that element appears.
    ///
    /// ## Example
    ///
    /// ```rust
    /// proof fn example() {
    ///     let s = seq![10, 20, 30];
    ///     assert(s.contains(20));
    ///     let idx = s.lemma_contains_to_index(20);
    ///     assert(s[idx] == 20);
    /// }
    /// ```
    pub proof fn lemma_contains_to_index(self, elem: A) -> (idx: int)
        requires
            self.contains(elem),
        ensures
            0 <= idx < self.len() && self[idx] == elem,
        decreases self.len(),
    {
        broadcast use group_seq_properties;

        if self[0] == elem {
            0
        } else {
            let i = self.skip(1).lemma_contains_to_index(elem);
            i + 1
        }
    }

    /// If a predicate holds for the first element and for all elements in the tail,
    /// then it holds for the entire sequence.
    ///
    /// ## Example
    ///
    /// ```rust
    /// proof fn example() {
    ///     let s = seq![2, 4, 6, 8];
    ///     let is_even = |x| x % 2 == 0;
    ///     assert(is_even(s[0]));
    ///     assert(s.skip(1).all(is_even));
    ///     s.lemma_all_from_head_tail(is_even);
    ///     assert(s.all(is_even));
    /// }
    /// ```
    pub proof fn lemma_all_from_head_tail(self, pred: spec_fn(A) -> bool)
        requires
            self.len() > 0,
            pred(self[0]) && self.skip(1).all(|x| pred(x)),
        ensures
            self.all(|x| pred(x)),
    {
        broadcast use group_seq_properties;

        assert(seq![self[0]] + self.skip(1) == self);
    }

    /// If a predicate holds for any element in the sequence and does not hold for the first element,
    /// then the predicate must hold for some element in the tail.
    ///
    /// ## Example
    ///
    /// ```rust
    /// proof fn example() {
    ///     let s = seq![1, 4, 6, 8];
    ///     let is_even = |x| x % 2 == 0;
    ///     assert(s.any(is_even));
    ///     assert(!is_even(s[0]));
    ///     s.lemma_any_tail(is_even);
    ///     assert(s.skip(1).any(is_even));
    /// }
    /// ```
    pub proof fn lemma_any_tail(self, pred: spec_fn(A) -> bool)
        requires
            self.any(|x| pred(x)),
        ensures
            !pred(self[0]) ==> self.skip(1).any(|x| pred(x)),
    {
        broadcast use group_seq_properties;

    }

    /// Removes duplicate elements from a sequence, maintaining the order of first appearance.
    /// Takes a `seen` sequence parameter to track previously encountered elements.
    ///
    /// ## Example
    ///
    /// ```rust
    /// fn example() {
    ///     let s = seq![1, 2, 1, 3, 2, 4];
    ///     let seen = seq![];
    ///     let result = s.remove_duplicates(seen);
    ///     assert_eq!(result, seq![1, 2, 3, 4]);
    ///
    ///     let seen2 = seq![2, 3];
    ///     let result2 = s.remove_duplicates(seen2);
    ///     assert_eq!(result2, seq![1, 4]);
    /// }
    /// ```
    pub open spec fn remove_duplicates(self, seen: Seq<A>) -> Seq<A>
        decreases self.len(),
    {
        if self.len() == 0 {
            seen
        } else if seen.contains(self[0]) {
            self.skip(1).remove_duplicates(seen)
        } else {
            self.skip(1).remove_duplicates(seen + seq![self[0]])
        }
    }

    /// Properties of remove_duplicates:
    /// - The output contains x if and only if x was in the input sequence or seen set
    /// - The output length is at most the sum of input and seen lengths
    ///
    /// ## Example
    ///
    /// ```rust
    /// proof fn example() {
    ///     let s = seq![1, 2, 1, 3];
    ///     let seen = seq![2];
    ///     s.lemma_remove_duplicates_properties(seen);
    ///     assert(s.remove_duplicates(seen).contains(1));
    ///     assert(s.remove_duplicates(seen).contains(3));
    ///     assert(!s.remove_duplicates(seen).contains(2));
    ///     assert(s.remove_duplicates(seen).len() <= s.len() + seen.len());
    /// }
    /// ```
    pub broadcast proof fn lemma_remove_duplicates_properties(self, seen: Seq<A>)
        ensures
            forall|x|
                (self + seen).contains(x) <==> #[trigger] self.remove_duplicates(seen).contains(x),
            #[trigger] self.remove_duplicates(seen).len() <= self.len() + seen.len(),
        decreases self.len(),
    {
        broadcast use group_seq_properties;

        if self.len() == 0 {
        } else if seen.contains(self[0]) {
            let rest = self.skip(1);
            rest.lemma_remove_duplicates_properties(seen);
        } else {
            let rest = self.skip(1);
            rest.lemma_remove_duplicates_properties(seen + seq![self[0]]);
        }
    }

    /// Shows that removing duplicates from a sequence is equivalent to:
    /// 1. First removing duplicates from the prefix up to index i (with the given seen set)
    /// 2. Using that result as the new seen set for removing duplicates from the suffix after i
    ///
    /// ## Example
    ///
    /// ```rust
    /// proof fn example() {
    ///     let s = seq![1, 2, 1, 3, 2, 4];
    ///     let seen = seq![];
    ///     s.lemma_remove_duplicates_append_index(seen, 2);
    ///     assert(s.remove_duplicates(seen)
    ///         =~= seq![1, 3, 2, 4].remove_duplicates(seq![1, 2].remove_duplicates(seen)));
    /// }
    /// ```
    pub proof fn lemma_remove_duplicates_append_index(self, i: int, seen: Seq<A>)
        requires
            0 <= i < self.len(),
        ensures
            self.remove_duplicates(seen) == self.skip(i).remove_duplicates(
                self.take(i).remove_duplicates(seen),
            ),
        decreases self.len(),
    {
        #[allow(deprecated)]
        lemma_seq_properties::<A>();  // new broadcast group not working here
        broadcast use Seq::lemma_remove_duplicates_properties;

        if i == 0 {
        } else if i == self.len() {
            assert(self.take(i) == self);
        } else {
            assert(self.skip(1).take(i - 1) == self.subrange(1, i));
            assert(self.take(i).skip(1) == self.subrange(1, i));
            assert(self.skip(1).take(i - 1) == self.take(i).skip(1));
            if seen.contains(self[0]) {
                self.skip(1).lemma_remove_duplicates_append_index(i - 1, seen);
            } else {
                self.skip(1).lemma_remove_duplicates_append_index(i - 1, seen + seq![self[0]]);
            }
        }
    }

    /// For two sequences, skipping one element after concatenation equals concatenating
    /// the result of skipping one element of the first sequence (which must be non-empty)
    /// with the second sequence.
    ///
    /// ## Example
    /// ```rust
    /// proof fn example() {
    ///     let s1 = seq![1, 2];
    ///     let s2 = seq![3, 4, 5];
    ///
    ///     lemma_skip1_concat(s1, s2);
    ///     assert((s1 + s2).skip(1) =~= seq![2, 3, 4, 5]);
    /// }
    /// ```
    proof fn lemma_skip1_concat(xs: Seq<A>, ys: Seq<A>)
        requires
            xs.len() > 0,
        ensures
            (xs + ys).skip(1) == xs.skip(1) + ys,
    {
        broadcast use group_seq_properties;

        assert((xs + ys).skip(1) == xs.skip(1) + ys);
    }

    /// When appending an element `x` to a sequence:
    /// - If `x` is in `self + seen`, removing duplicates equals removing duplicates from self
    /// - If x is not in (self + seen), removing duplicates equals removing duplicates from self,
    ///   concatenated with [x]
    ///
    /// ## Example
    /// ```rust
    /// proof fn example() {
    ///     let s1 = seq![1, 2];
    ///     let seen = seq![];
    ///     assert!(!s1.contains(3));
    ///     lemma_remove_duplicates_append(s1, 3, seen);
    ///     assert((s1 + seq![3]).remove_duplicates(seen) =~= s1.remove_duplicates(seen) + seq![3]);
    /// }
    /// ```
    pub proof fn lemma_remove_duplicates_append(self, x: A, seen: Seq<A>)
        ensures
            (self + seen).contains(x) ==> (self + seq![x]).remove_duplicates(seen)
                == self.remove_duplicates(seen),
            !(self + seen).contains(x) ==> (self + seq![x]).remove_duplicates(seen)
                == self.remove_duplicates(seen) + seq![x],
        decreases self.len(),
    {
        broadcast use group_seq_properties;

        reveal_with_fuel(Seq::remove_duplicates, 2);

        if self.len() != 0 {
            let head = self[0];
            let tail = self.skip(1);

            let seen2 = if seen.contains(head) {
                seen
            } else {
                seen + seq![head]
            };
            tail.lemma_remove_duplicates_append(x, seen2);
            assert((self + seq![x]).skip(1) == tail + seq![x]) by {
                Seq::lemma_skip1_concat(self, seq![x]);
            };
        }
    }

    /// If all elements in a sequence fail the predicate,
    /// filtering by that predicate yields an empty sequence
    ///
    /// ## Example
    /// ```rust
    /// proof fn example() {
    ///     let s = seq![1, 2, 3];
    ///     let pred = |x| x > 5;
    ///     lemma_all_neg_filter_empty(s, pred);
    ///     assert(s.filter(pred).len() == 0);
    /// }
    /// ```
    pub proof fn lemma_all_neg_filter_empty(self, pred: spec_fn(A) -> bool)
        requires
            self.all(|x: A| !pred(x)),
        ensures
            self.filter(pred).len() == 0,
        decreases self.len(),
    {
        broadcast use group_seq_properties;

        reveal(Seq::filter);
        if self.len() != 0 {
            let rest = self.drop_last();
            rest.lemma_all_neg_filter_empty(pred);
            rest.lemma_filter_len_push(pred, self.last());
            let neg_pred = |x| !pred(x);
            assert(neg_pred(self.last()));
        }
    }

    /// Applies an Option-returning function to each element, keeping only successful (Some) results
    ///
    /// ## Example
    /// ```rust
    /// let s = seq![1, 2, 3];
    /// let f = |x| if x % 2 == 0 { Some(x * 2) } else { None };
    /// assert(s.filter_map(f) =~= seq![4]);
    /// ```
    pub open spec fn filter_map<B>(self, f: spec_fn(A) -> Option<B>) -> Seq<B>
        decreases self.len(),
    {
        // We're defining this by starting at the end of the list since it makes it
        // easier to reason about in the common case of looping over a vector in the
        // implementation.
        if self.len() == 0 {
            Seq::empty()
        } else {
            let rest = self.drop_last();
            match f(self.last()) {
                Option::Some(s) => rest.filter_map(f) + seq![s],
                Option::None => rest.filter_map(f),
            }
        }
    }

    /// If an element exists in the filtered sequence,
    /// it must exist in the original sequence
    /// ```
    pub broadcast proof fn lemma_filter_contains_rev(self, p: spec_fn(A) -> bool, elem: A)
        requires
            #[trigger] self.filter(p).contains(elem),
        ensures
            self.contains(elem),
        decreases self.len(),
    {
        broadcast use group_seq_properties;

        reveal(Seq::filter);
        if self.len() == 0 {
        } else {
            let rest = self.drop_last();
            let last = self.last();
            if !p(last) || last != elem {
                rest.lemma_filter_contains_rev(p, elem);
            }
        }
    }

    /// If an element exists in filter_map's output,
    /// there must be an input element that mapped to it
    /// ```
    pub broadcast proof fn lemma_filter_map_contains<B>(self, f: spec_fn(A) -> Option<B>, elt: B)
        requires
            #[trigger] self.filter_map(f).contains(elt),
        ensures
            exists|t: A| #[trigger] self.contains(t) && f(t) == Some(elt),
        decreases self.len(),
    {
        broadcast use group_seq_properties;

        if self.len() == 0 {
        } else {
            let last = self.last();
            let rest = self.drop_last();
            if f(last) == Some(elt) {
                assert(self.contains(last));
            } else {
                rest.lemma_filter_map_contains(f, elt);
                let t = choose|t: A| #[trigger] rest.contains(t) && f(t) == Some(elt);
                assert(self.contains(t));
            }
        }
    }

    /// Taking k+1 elements is the same as taking k elements plus the kth element
    ///
    /// ## Example
    /// ```rust
    /// let s = seq![1, 2, 3];
    /// lemma_take_plus_one(s, 1);
    /// seq![1, 2] == seq![1] + seq![2]
    /// ```
    pub proof fn lemma_take_succ(xs: Seq<A>, k: int)
        requires
            0 <= k < xs.len(),
        ensures
            xs.take(k + 1) =~= xs.take(k) + seq![xs[k]],
    {
        broadcast use group_seq_properties;

    }

    /// filter_map on a single element sequence
    /// either produces a new single element sequence (if f returns Some)
    /// or an empty sequence (if f returns None)
    pub proof fn lemma_filter_map_singleton<B>(a: A, f: spec_fn(A) -> Option<B>)
        ensures
            seq![a].filter_map(f) =~= match f(a) {
                Option::Some(b) => seq![b],
                Option::None => Seq::empty(),
            },
    {
        reveal_with_fuel(Seq::filter_map, 2);
    }

    /// filter_map of take(i+1) equals
    /// filter_map of take(i) plus maybe the mapped i'th element
    ///
    /// ## Example
    /// ```rust
    /// let s = seq![1, 2, 3];
    /// let f = |x| if x % 2 == 0 { Some(x * 2) } else { None };
    /// s.lemma_filter_map_take_succ(s, f, 1);
    /// assert(s.take(2).filter_map(f) == s.take(1).filter_map(f) + seq![f(s[1]).unwrap()]);
    /// assert(s.take(2).filter_map(f) == seq![] + seq![4]);
    /// ```
    pub broadcast proof fn lemma_filter_map_take_succ<B>(self, f: spec_fn(A) -> Option<B>, i: int)
        requires
            0 <= i < self.len(),
        ensures
            #[trigger] self.take(i + 1).filter_map(f) =~= self.take(i).filter_map(f) + (match f(
                self[i],
            ) {
                Option::Some(s) => seq![s],
                Option::None => Seq::empty(),
            }),
        decreases self.len(),
    {
        broadcast use group_seq_properties;

        if i != 0 {
            self.drop_last().lemma_filter_map_take_succ(f, i - 1);
            assert(self.take(i + 1).drop_last() == self.take(i));
        }
    }

    /// An alternative implementation of filter that processes the sequence recursively from
    /// left to right, in contrast to the standard filter which processes from right to left.
    pub open spec fn filter_alt(self, p: spec_fn(A) -> bool) -> Seq<A> {
        if self.len() == 0 {
            Seq::empty()
        } else {
            let rest = self.drop_first().filter(p);
            let first = self.first();
            if p(first) {
                seq![first] + rest
            } else {
                rest
            }
        }
    }

    /// When filtering (x + sequence), if x satisfies the predicate, x is prepended to
    /// the filtered sequence. Otherwise, only the filtered sequence remains.
    ///
    /// ## Example
    /// ```rust
    /// proof fn filter_prepend_test() {
    ///     let s = seq![2, 3, 4];
    ///     let is_even = |x: int| x % 2 == 0;
    ///     let with_five = seq![5] + s;
    ///     assert(with_five.filter(is_even) =~= seq![2, 4]); // 5 filtered out
    ///     let with_six = seq![6] + s;
    ///     assert(with_six.filter(is_even) =~= seq![6, 2, 4]); // 6 included
    /// }
    /// ```
    pub broadcast proof fn lemma_filter_prepend(self, x: A, p: spec_fn(A) -> bool)
        ensures
            #[trigger] (seq![x] + self).filter(p) == (if p(x) {
                seq![x]
            } else {
                Seq::empty()
            }) + self.filter(p),
        decreases self.len(),
    {
        broadcast use group_seq_properties;

        reveal(Seq::filter);
        let lhs = (seq![x] + self).filter(p);
        let rhs = (if p(x) {
            seq![x]
        } else {
            Seq::empty()
        }) + self.filter(p);

        if self.len() == 0 {
            assert(lhs =~= rhs);
        } else {
            let tail_seq = if p(self.last()) {
                seq![self.last()]
            } else {
                Seq::empty()
            };

            assert(((seq![x] + self).drop_last()) =~= seq![x] + self.drop_last());
            let sub = (seq![x] + self.drop_last()).filter(p);
            assert(lhs =~= sub + tail_seq);
            assert(rhs =~= (if p(x) {
                seq![x]
            } else {
                Seq::empty()
            }) + self.drop_last().filter(p) + tail_seq);
            self.drop_last().lemma_filter_prepend(x, p);
        }
    }

    /// The filter() and filter_alt() methods produce equivalent results for any sequence
    pub proof fn lemma_filter_eq_filter_alt(self, p: spec_fn(A) -> bool)
        ensures
            self.filter(p) =~= self.filter_alt(p),
        decreases self.len(),
    {
        broadcast use group_seq_properties;
        broadcast use Seq::lemma_filter_prepend;

        reveal(Seq::filter);
        if self.len() == 0 {
        } else {
            let first = self.first();
            let but_first = self.drop_first();
            assert(self =~= seq![first] + but_first);
            self.drop_first().lemma_filter_eq_filter_alt(p);
        }
    }

    /// Filtering preserves the prefix relationship between sequences.
    ///
    /// ## Example
    /// ```rust
    /// proof fn filter_monotone_test() {
    ///     let s = seq![1, 2, 3];
    ///     let ys = seq![1, 2, 3, 4, 5];
    ///     let is_even = |x: int| x % 2 == 0;
    ///     assert(s.is_prefix_of(ys));
    ///     assert(s.filter(is_even).is_prefix_of(ys.filter(is_even)));
    ///     assert(s.filter(is_even) =~= seq![2]);
    ///     assert(ys.filter(is_even) =~= seq![2, 4]);
    /// }
    /// ```
    pub proof fn lemma_filter_monotone(self, ys: Seq<A>, p: spec_fn(A) -> bool)
        requires
            self.is_prefix_of(ys),
        ensures
            self.filter(p).is_prefix_of(ys.filter(p)),
        decreases self.len(),
    {
        broadcast use group_seq_properties;

        self.lemma_filter_eq_filter_alt(p);
        ys.lemma_filter_eq_filter_alt(p);
        if self.len() == 0 {
        } else {
            self.drop_first().lemma_filter_monotone(ys.drop_first(), p);
        }
    }

    /// The length of filter(take(i)) is never greater than the length of filter(entire_sequence).
    ///
    /// ## Example
    /// ```rust
    /// proof fn filter_take_len_test() {
    ///     let s = seq![1, 2, 3, 4, 5];
    ///     let is_even = |x: int| x % 2 == 0;
    ///     let i = 3;
    ///     assert(s.take(i) =~= seq![1, 2, 3]);
    ///     assert(s.take(i).filter(is_even) =~= seq![2]);
    ///     assert(s.filter(is_even) =~= seq![2, 4]);
    ///     assert(s.filter(is_even).len() >= s.take(i).filter(is_even).len());
    /// }
    /// ```
    pub proof fn lemma_filter_take_len(self, p: spec_fn(A) -> bool, i: int)
        requires
            0 <= i <= self.len(),
        ensures
            self.filter(p).len() >= self.take(i).filter(p).len(),
        decreases i,
    {
        broadcast use group_seq_properties;
        broadcast use Seq::lemma_filter_len_push;
        broadcast use Seq::lemma_filter_push;

        self.take(i).lemma_filter_monotone(self, p);
    }

    /// Filtering a prefix of a sequence produces the same number or fewer elements
    /// as filtering the entire sequence.
    ///
    /// ## Example
    /// ```rust
    /// proof fn filter_take_len_test() {
    ///     let s = seq![1, 2, 3, 4, 5];
    ///     let is_even = |x: int| x % 2 == 0;
    ///     assert(s.filter(is_even).len() >= s.take(3).filter(is_even).len());
    /// }
    /// ```
    pub broadcast proof fn lemma_filter_len_push(self, p: spec_fn(A) -> bool, elem: A)
        ensures
            #[trigger] self.push(elem).filter(p).len() == self.filter(p).len() + (if p(elem) {
                1int
            } else {
                0int
            }),
    {
        broadcast use group_seq_properties;
        broadcast use Seq::lemma_filter_push;

    }

    /// If an index i is valid for a sequence (0 ≤ i < len), then the element at that index
    /// is contained in the sequence.
    pub broadcast proof fn lemma_index_contains(self, i: int)
        requires
            0 <= i < self.len(),
        ensures
            self.contains(#[trigger] self[i]),
    {
    }

    /// Taking i+1 elements from a sequence is equivalent to taking i elements
    /// and then pushing the element at index i.
    pub broadcast proof fn lemma_take_succ_push(self, i: int)
        requires
            0 <= i < self.len(),
        ensures
            #[trigger] self.take(i + 1) =~= self.take(i).push(self[i]),
    {
        broadcast use group_seq_properties;

    }

    /// Taking the full length of a sequence returns the sequence itself.
    pub broadcast proof fn lemma_take_len(self)
        ensures
            #[trigger] self.take(self.len() as int) == self,
    {
        broadcast use group_seq_properties;

    }

    /// Taking i+1 elements and checking if any element satisfies predicate p is equivalent to:
    /// either taking i elements and checking if any satisfies p, OR checking if the i-th element satisfies p.
    ///
    /// ## Example
    /// ```rust
    /// proof fn take_any_succ_test() {
    ///     let s = seq![1, 2, 3];
    ///     let is_even = |x| x % 2 == 0;
    ///     let i = 1;
    ///     assert(s.take(i + 1).any(is_even) == (s.take(i).any(is_even) || is_even(s[i])));
    /// }
    /// ```
    pub broadcast proof fn lemma_take_any_succ(self, p: spec_fn(A) -> bool, i: int)
        requires
            0 <= i < self.len(),
        ensures
            #[trigger] self.take(i + 1).any(p) <==> self.take(i).any(p) || p(self[i]),
    {
        broadcast use group_seq_properties;

        self.lemma_take_succ_push(i);
        if self.take(i + 1).any(p) {
            let x = choose|x: A| self.take(i + 1).contains(x) && #[trigger] p(x);
            assert(self.take(i).contains(x) || x == self[i]);
        }
        if self.take(i).any(p) {
            let x = choose|x: A| self.take(i).contains(x) && #[trigger] p(x);
            assert(self.take(i + 1).contains(x));
        }
        if p(self[i]) {
            assert(self.take(i + 1).contains(self[i]));
        }
    }

    /// A sequence has no duplicates iff mapping an injective function over it
    /// produces a sequence with no duplicates.
    ///
    /// ## Example
    /// ```rust
    /// proof fn no_duplicates_injective_test() {
    ///     let s = seq![1, 2];
    ///     let f = |x| x + 1;  // injective function
    ///     assert(s.no_duplicates() == s.map_values(f).no_duplicates());
    /// }
    /// ```
    pub proof fn lemma_no_duplicates_injective<B>(self, f: spec_fn(A) -> B)
        requires
            injective(f),
        ensures
            self.no_duplicates() <==> self.map_values(f).no_duplicates(),
    {
        broadcast use group_seq_properties;
        broadcast use super::set_lib::group_set_properties;

        let mapped = self.map_values(f);
        assert(mapped.len() == self.len());
        if mapped.no_duplicates() {
            assert forall|i: int, j: int| 0 <= i < j < mapped.len() implies self[i] != self[j] by {
                assert(mapped[i] == f(self[i]));
                assert(mapped[j] == f(self[j]));
            }
        }
    }

    /// Pushing an element and then mapping a function over a sequence is equivalent to
    /// mapping the function over the sequence and then pushing the function applied to that element.
    ///
    /// ## Example
    /// ```rust
    /// proof fn push_map_test() {
    ///     let s = seq![1, 2];
    ///     let f = |x| x + 1;
    ///     assert(s.push(3).map_values(f) =~= s.map_values(f).push(f(3)));
    /// }
    /// ```
    pub broadcast proof fn lemma_push_map_commute<B>(self, f: spec_fn(A) -> B, x: A)
        ensures
            self.map_values(f).push(f(x)) =~= #[trigger] self.push(x).map_values(f),
        decreases self.len(),
    {
        broadcast use group_seq_properties;

    }

    /// Converting a sequence to a set after pushing an element is equivalent to
    /// converting to a set first and then inserting that element.
    ///
    /// ## Example
    /// ```rust
    /// proof fn push_to_set_test() {
    ///     let s = seq![1, 2];
    ///     assert(s.push(3).to_set() =~= s.to_set().insert(3));
    /// }
    /// ```
    pub broadcast proof fn lemma_push_to_set_commute(self, elem: A)
        ensures
            #[trigger] self.push(elem).to_set() =~= self.to_set().insert(elem),
    {
        broadcast use group_seq_properties;
        broadcast use super::set::group_set_axioms;

        let lhs = self.push(elem).to_set();
        let rhs = self.to_set().insert(elem);

        assert(lhs.subset_of(rhs));
        assert forall|x: A| rhs.contains(x) implies lhs.contains(x) by {
            lemma_seq_contains_after_push(self, elem, x);
            if x == elem {
            } else {
                lemma_seq_contains_after_push(self, elem, x);
            }
        }
    }

    /// Filtering a sequence after pushing an element is equivalent to:
    /// if the element satisfies the predicate, filter the sequence and push the element
    /// otherwise, just filter the sequence without the element.
    ///
    /// ## Example
    /// ```rust
    /// proof fn filter_push_test() {
    ///     let s = seq![1, 2];
    ///     let is_even = |x| x % 2 == 0;
    ///     assert(s.push(4).filter(is_even) == s.filter(is_even).push(4));
    ///     assert(s.push(3).filter(is_even) == s.filter(is_even));
    /// }
    /// ```
    pub broadcast proof fn lemma_filter_push(self, elem: A, pred: spec_fn(A) -> bool)
        ensures
            #[trigger] self.push(elem).filter(pred) == if pred(elem) {
                self.filter(pred).push(elem)
            } else {
                self.filter(pred)
            },
    {
        broadcast use group_seq_properties;

        reveal(Seq::filter);
        assert(self.push(elem).drop_last() =~= self);
    }

    /// If two sequences have the same length and `i` is a valid index,
    /// then the pair (a[i], b[i]) is contained in their zip.
    ///
    /// ## Example
    /// ```rust
    /// proof fn zip_contains_test() {
    ///     let a = seq![1, 2];
    ///     let b = seq!["a", "b"];
    ///     assert(a.zip_with(b).contains((a[0], b[0])));
    ///     assert(a.zip_with(b).contains((a[1], b[1])));
    /// }
    /// ```
    pub proof fn lemma_zip_with_contains_index<B>(self, b: Seq<B>, i: int)
        requires
            0 <= i < self.len(),
            self.len() == b.len(),
        ensures
            self.zip_with(b).contains((self[i], b[i])),
    {
        assert(self.zip_with(b)[i] == (self[i], b[i]));
    }

    /// Proves equivalence between checking a predicate over zipped sequences and checking
    /// corresponding elements by index. Requires sequences of equal length.
    ///
    /// # Example
    /// ```rust
    /// proof fn example() {
    ///     let xs = seq![1, 2];
    ///     let ys = seq![2, 3];
    ///     let f = |x, y| x < y;
    ///     assert(xs.zip_with(ys).all(|(x, y)| f(x, y)) <==>
    ///            forall|i| 0 <= i < xs.len() ==> f(xs[i], ys[i]));
    ///     // We can now prove specific index relationships
    ///     assert(xs[0] < ys[0]); // 1 < 2
    ///     assert(xs[1] < ys[1]); // 2 < 3
    /// }
    /// ```
    pub proof fn lemma_zip_with_uncurry_all<B>(self, b: Seq<B>, f: spec_fn(A, B) -> bool)
        requires
            self.len() == b.len(),
        ensures
            self.zip_with(b).all(|p: (A, B)| f(p.0, p.1)) <==> forall|i: int|
                0 <= i < self.len() ==> f(self[i], b[i]),
    {
        broadcast use group_seq_properties;

        let zipped = self.zip_with(b);
        let f_uncurr = |p: (A, B)| f(p.0, p.1);
        let lhs = zipped.all(f_uncurr);
        let rhs = (forall|i: int| 0 <= i < self.len() ==> f(self[i], b[i]));
        if lhs {
            assert forall|i: int| 0 <= i < self.len() implies f(self[i], b[i]) by {
                self.lemma_zip_with_contains_index(b, i);
                assert(forall|j| 0 <= j < zipped.len() ==> f_uncurr(zipped[j]));
            }
        }
    }

    /// flat_mapping after pushing an element is the same as
    /// flat_mapping first and then appending f of that element.
    ///
    /// # Example
    /// ```rust
    /// proof fn example() {
    ///     let xs = seq![1, 2];
    ///     let f = |x| seq![x, x + 1];
    ///     assert(xs.push(3).flat_map(f) =~= xs.flat_map(f) + f(3));
    ///     // xs.push(3).flat_map(f)    = [1,2,2,3,3,4]
    ///     // xs.flat_map(f) + f(3)     = [1,2,2,3] + [3,4]
    /// }
    /// ```
    pub proof fn lemma_flat_map_push<B>(self, f: spec_fn(A) -> Seq<B>, elem: A)
        ensures
            self.push(elem).flat_map(f) =~= self.flat_map(f) + f(elem),
        decreases self.len(),
    {
        broadcast use group_seq_properties;
        broadcast use Seq::lemma_flatten_push;
        broadcast use Seq::lemma_push_map_commute;

    }

    /// flat_mapping a sequence up to index i+1 is equivalent to
    /// flat_mapping up to index i and appending f of the element at index i.
    ///
    /// # Example
    /// ```rust
    /// proof fn example() {
    ///     let xs = seq![1, 2, 3];
    ///     let f = |x| seq![x, x + 1];
    ///
    ///     assert(xs.take(2).flat_map(f) =~= xs.take(1).flat_map(f) + f(xs[1]));
    ///     // xs.take(2).flat_map(f)        = [1,2,2,3]
    ///     // xs.take(1).flat_map(f) + f(2) = [1,2] + [2,3]
    /// }
    /// ```
    pub broadcast proof fn lemma_flat_map_take_append<B>(self, f: spec_fn(A) -> Seq<B>, i: int)
        requires
            0 <= i < self.len(),
        ensures
            #[trigger] self.take(i + 1).flat_map(f) =~= self.take(i).flat_map(f) + f(self[i]),
        decreases i,
    {
        broadcast use group_seq_properties;

        self.lemma_take_succ_push(i);
        self.take(i).lemma_flat_map_push(f, self[i]);
    }

    /// flat_mapping a sequence with a single element
    /// is equivalent to applying the function f to that element.
    pub broadcast proof fn lemma_flat_map_singleton<B>(self, f: spec_fn(A) -> Seq<B>)
        requires
            #[trigger] self.len() == 1,
        ensures
            #[trigger] self.flat_map(f) == f(self[0]),
    {
        broadcast use Seq::lemma_flatten_singleton;

    }

    /// Mapping a sequence's first i+1 elements equals
    /// mapping its first i elements plus f of the i-th element.
    ///
    /// # Example
    /// ```rust
    /// proof fn example() {
    ///     let xs = seq![1, 2, 3];
    ///     let f = |x| x * 2;
    ///
    ///     assert(xs.take(2).map_values(f) =~= xs.take(1).map_values(f).push(f(xs[1])));
    ///     // Left:  [1,2].map(f)          = [2,4]
    ///     // Right: [1].map(f).push(f(2)) = [2].push(4)
    /// }
    /// ```
    pub broadcast proof fn lemma_map_take_succ<B>(self, f: spec_fn(A) -> B, i: int)
        requires
            0 <= i < self.len(),
        ensures
            #[trigger] self.take(i + 1).map_values(f) =~= self.take(i).map_values(f).push(
                f(self[i]),
            ),
    {
        broadcast use group_seq_properties;

        self.lemma_take_succ_push(i);
    }

    /// If a sequence is a prefix of another sequence,
    /// their elements match at all indices within the prefix length.
    ///
    /// # Example
    /// ```rust
    /// proof fn example() {
    ///     let xs = seq![1, 2, 3];
    ///     let prefix = seq![1, 2];
    ///     assert(prefix.is_prefix_of(xs));
    ///     assert(prefix[0] == xs[0] && prefix[1] == xs[1]);
    /// }
    /// ```
    pub broadcast proof fn lemma_prefix_index_eq(self, prefix: Seq<A>)
        requires
            #[trigger] prefix.is_prefix_of(self),
        ensures
            forall|i: int| 0 <= i < prefix.len() ==> prefix[i] == self[i],
    {
    }

    /// If a concatenated sequence (prefix1 + prefix2) is a prefix of another sequence,
    /// then prefix1 by itself is also a prefix of that sequence.
    ///
    /// # Example
    /// ```rust
    /// proof fn example() {
    ///     let xs = seq![1, 2, 3, 4];
    ///     let prefix1 = seq![1, 2];
    ///     let prefix2 = seq![3];
    ///     assert((prefix1 + prefix2).is_prefix_of(xs));
    ///     assert(prefix1.is_prefix_of(xs));
    /// }
    /// ```
    pub broadcast proof fn lemma_prefix_concat(self, prefix1: Seq<A>, prefix2: Seq<A>)
        requires
            #[trigger] (prefix1 + prefix2).is_prefix_of(self),
        ensures
            prefix1.is_prefix_of(self),
    {
        broadcast use Seq::lemma_prefix_index_eq;

    }

    /// If `prefix1 + [t]` is a prefix of a sequence,
    /// `prefix1` is a prefix of `prefix2`,
    /// `prefix2` is a prefix of the sequence,
    /// `prefix1` and `prefix2` are different, and
    /// `prefix1` doesn't contain `t`,
    /// then `prefix2` must contain t.
    ///
    /// # Example
    /// ```rust
    /// proof fn example() {
    ///     let xs = seq![1, 2, 3, 4];
    ///     let prefix1 = seq![1];
    ///     let prefix2 = seq![1, 2];
    ///     let t = 2;
    ///     assert((prefix1 + seq![t]).is_prefix_of(xs));
    ///     assert(prefix1.is_prefix_of(prefix2));
    ///     assert(prefix2.is_prefix_of(xs));
    ///     assert(prefix2.contains(t));
    /// }
    /// ```
    pub broadcast proof fn lemma_prefix_chain_contains(self, prefix1: Seq<A>, prefix2: Seq<A>, t: A)
        requires
            #[trigger] (prefix1 + seq![t]).is_prefix_of(self),
            #[trigger] prefix1.is_prefix_of(prefix2),
            prefix2.is_prefix_of(self),
            prefix1 != prefix2,
            !prefix1.contains(t),
        ensures
            prefix2.contains(t),
    {
        broadcast use Seq::lemma_prefix_concat;
        broadcast use Seq::lemma_prefix_index_eq;

        assert(prefix2[prefix1.len() as int] == t);
    }

    /// If `prefix1 + [t]` and `prefix2 + [t]` are both prefixes of a sequence,
    /// and neither `prefix1` nor `prefix2` contains `t`,
    /// then `prefix1` equals `prefix2`.
    pub broadcast proof fn lemma_prefix_append_unique(self, prefix1: Seq<A>, prefix2: Seq<A>, t: A)
        requires
            #[trigger] (prefix1 + seq![t]).is_prefix_of(self),
            #[trigger] (prefix2 + seq![t]).is_prefix_of(self),
            !prefix1.contains(t),
            !prefix2.contains(t),
        ensures
            prefix1 == prefix2,
    {
        broadcast use Seq::lemma_prefix_concat;
        broadcast use Seq::lemma_prefix_index_eq;
        broadcast use Seq::lemma_prefix_chain_contains;

        if prefix1 != prefix2 {
            assert(prefix1.is_prefix_of(prefix2) || prefix2.is_prefix_of(prefix1));
        }
    }

    /// If a predicate `p` is true for all elements in a sequence,
    /// and `p` is true for an element `e`, then `p` remains true for all elements
    /// after pushing `e` to the sequence.
    ///
    /// # Example
    /// ```rust
    /// proof fn example() {
    ///     let xs = seq![2, 4, 6];
    ///     let is_even = |x| x % 2 == 0;
    ///     assert(xs.all(is_even));
    ///     assert(is_even(8));
    ///     assert(xs.push(8).all(is_even));
    /// }
    /// ```
    pub broadcast proof fn lemma_all_push(self, p: spec_fn(A) -> bool, elem: A)
        requires
            self.all(p),
            p(elem),
        ensures
            #[trigger] self.push(elem).all(p),
    {
        broadcast use group_seq_properties;

        assert forall|x: A| self.push(elem).contains(x) implies p(x) by {
            lemma_seq_contains_after_push(self, elem, x);
        }
    }

    /// Two sequences are equal when concatenated with the same prefix
    /// iff those two sequences are equal.
    pub proof fn lemma_concat_injective(self, s1: Seq<A>, s2: Seq<A>)
        ensures
            (self + s1 == self + s2) <==> (s1 == s2),
    {
        broadcast use group_seq_properties;

        assert((self + s1).skip(self.len() as int) == s1);
    }

    pub broadcast group group_seq_extra {
        Seq::<_>::lemma_seq_skip_skip,
        Seq::<_>::lemma_remove_duplicates_properties,
        Seq::<_>::lemma_filter_contains_rev,
        Seq::<_>::lemma_filter_map_take_succ,
        Seq::<_>::lemma_filter_prepend,
        Seq::<_>::lemma_filter_len_push,
        Seq::<_>::lemma_take_len,
        Seq::<_>::lemma_take_any_succ,
        Seq::<_>::lemma_push_map_commute,
        Seq::<_>::lemma_push_to_set_commute,
        Seq::<_>::lemma_filter_push,
        Seq::<_>::lemma_flat_map_take_append,
        Seq::<_>::lemma_flat_map_singleton,
        Seq::<_>::lemma_map_take_succ,
        Seq::<_>::lemma_prefix_index_eq,
        Seq::<_>::lemma_prefix_concat,
        Seq::<_>::lemma_prefix_chain_contains,
        Seq::<_>::lemma_prefix_append_unique,
        Seq::<_>::lemma_all_push,
    }
}

/// Filtering a sequence and then viewing its elements produces the same result as
/// viewing the elements first and then filtering with the corresponding predicate.
/// The predicates p and sp must be equivalent under view.
///
/// # Example
/// ```rust
/// proof fn example() {
///     let s = seq!["hello".to_string(), "world".to_string()];
///     let p = |x: String| x.len() > 4;
///     let sp = |x: Seq<char>| x.len() > 4;
///
///     let way1 = s.filter(p).map_values(|x| x.view());
///     let way2 = s.map_values(|x| x.view()).filter(sp);
///     assert(way1 == way2);
/// }
/// ```
pub proof fn lemma_filter_view_commute<S: View>(
    s: Seq<S>,
    p: spec_fn(S) -> bool,
    sp: spec_fn(S::V) -> bool,
)
    requires
        forall|s: S| p(s) <==> sp(s.view()),
    ensures
        s.filter(p).map_values(|x: S| x.view()) == s.map_values(|x: S| x.view()).filter(sp),
    decreases s.len(),
{
    broadcast use group_seq_properties;
    broadcast use Seq::lemma_push_map_commute;
    broadcast use Seq::lemma_filter_push;

    reveal(Seq::filter);
    let view = |x: S| x.view();
    if s.len() > 0 {
        let rest = s.drop_last();
        let last = s.last();
        assert(s =~= rest.push(last));
        assert(s.map_values(view).last() == view(last));
        lemma_filter_view_commute(rest, p, sp);
    }
}

/// A sequence has exactly one element satisfying a predicate iff
/// viewing all elements and filtering with the corresponding predicate
/// produces a sequence with exactly one element.
///
/// # Example
/// ```rust
/// proof fn example() {
///     let s = seq!["hello".to_string(), "world".to_string()];
///     let p = |x: String| x.len() == 5;
///     let sp = |x: Seq<char>| x.len() == 5;
///
///     assert(s.exactly_one(p) <==> s.map_values(|x| x.view()).exactly_one(sp));
/// }
/// ```
pub proof fn lemma_exactly_one_view<S: View>(
    s: Seq<S>,
    p: spec_fn(S) -> bool,
    sp: spec_fn(S::V) -> bool,
)
    requires
        forall|s: S| p(s) <==> sp(s.view()),
        injective(|x: S| x.view()),
    ensures
        s.exactly_one(p) <==> s.map_values(|x: S| x.view()).exactly_one(sp),
{
    lemma_filter_view_commute(s, p, sp);
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
        broadcast use group_seq_properties;

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
        broadcast use {Seq::add_empty_right, Seq::push_distributes_over_add};

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

    /// Flattening a sequence of sequences after pushing a new sequence is equivalent to
    /// concatenating that sequence to the original flattened result.
    pub broadcast proof fn lemma_flatten_push(self, elem: Seq<A>)
        ensures
            #[trigger] self.push(elem).flatten() =~= self.flatten() + elem,
        decreases self.len(),
    {
        broadcast use group_seq_properties;

        assert(self.push(elem).last() == elem);
        assert(self.push(elem).drop_last() =~= self);
        calc! {
            (==)
            self.push(elem).flatten(); {
                self.push(elem).lemma_flatten_and_flatten_alt_are_equivalent();
            }
            self.push(elem).flatten_alt(); {}
            self.flatten_alt() + elem; {
                self.lemma_flatten_and_flatten_alt_are_equivalent();
            }
            self.flatten() + elem;
        }
    }

    /// Flattening a sequence containing a single sequence yields that inner sequence.
    pub broadcast proof fn lemma_flatten_singleton(self)
        requires
            #[trigger] self.len() == 1,
        ensures
            #[trigger] self.flatten() == self[0],
    {
        assert(self.flatten() == self[0] + self.drop_first().flatten());
        assert(self.flatten() == self[0]);
    }

    pub broadcast group group_seq_flatten {
        Seq::<_>::lemma_flatten_push,
        Seq::<_>::lemma_flatten_singleton,
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
    // TODO: lemma_seq_skip_of_skip and lemma_seq_skip_index2 cause a lot of QIs
    broadcast use group_seq_properties;

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
    broadcast use group_seq_properties;

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
    broadcast use group_seq_properties;

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
pub broadcast proof fn to_multiset_build<A>(s: Seq<A>, a: A)
    ensures
        #![trigger s.push(a).to_multiset()]
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

pub broadcast proof fn to_multiset_remove<A>(s: Seq<A>, i: int)
    requires
        0 <= i < s.len(),
    ensures
        #![trigger s.remove(i).to_multiset()]
        s.remove(i).to_multiset() =~= s.to_multiset().remove(s[i]),
{
    broadcast use super::multiset::group_multiset_axioms;

    let s0 = s.subrange(0, i);
    let s1 = s.subrange(i, s.len() as int);
    let s2 = s.subrange(i + 1, s.len() as int);
    lemma_seq_union_to_multiset_commutative(s0, s2);
    lemma_seq_union_to_multiset_commutative(s0, s1);
    assert(s == s0 + s1);
    assert(s2 + s0 == (s1 + s0).drop_first());
}

/// to_multiset() preserves length
pub broadcast proof fn to_multiset_len<A>(s: Seq<A>)
    ensures
        s.len() == #[trigger] s.to_multiset().len(),
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
pub broadcast proof fn to_multiset_contains<A>(s: Seq<A>, a: A)
    ensures
        #![trigger s.to_multiset().count(a)]
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

pub proof fn seq_to_set_distributes_over_add<T>(s1: Seq<T>, s2: Seq<T>)
    ensures
        s1.to_set() + s2.to_set() =~= (s1 + s2).to_set(),
{
    broadcast use super::group_vstd_default;
    broadcast use super::set_lib::group_set_properties;
    broadcast use group_seq_properties;

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
    broadcast use group_to_multiset_ensures;

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
pub broadcast proof fn lemma_seq_contains<A>(s: Seq<A>, x: A)
    ensures
        #[trigger] s.contains(x) <==> exists|i: int| 0 <= i < s.len() && #[trigger] s[i] == x,
{
}

// This verified lemma used to be an axiom in the Dafny prelude
/// The empty sequence contains nothing
pub broadcast proof fn lemma_seq_empty_contains_nothing<A>(x: A)
    ensures
        !(#[trigger] Seq::<A>::empty().contains(x)),
{
}

// This verified lemma used to be an axiom in the Dafny prelude
// Note: Dafny only does one way implication, but theoretically it could go both ways
/// A sequence with length 0 is equivalent to the empty sequence
pub broadcast proof fn lemma_seq_empty_equality<A>(s: Seq<A>)
    ensures
        #[trigger] s.len() == 0 ==> s =~= Seq::<A>::empty(),
{
}

// This verified lemma used to be an axiom in the Dafny prelude
/// The concatenation of two sequences contains only the elements
/// of the two sequences
pub broadcast proof fn lemma_seq_concat_contains_all_elements<A>(x: Seq<A>, y: Seq<A>, elt: A)
    ensures
        #[trigger] (x + y).contains(elt) <==> x.contains(elt) || y.contains(elt),
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
pub broadcast proof fn lemma_seq_contains_after_push<A>(s: Seq<A>, v: A, x: A)
    ensures
        #[trigger] s.push(v).contains(x) <==> v == x || s.contains(x),
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
pub broadcast proof fn lemma_seq_subrange_elements<A>(s: Seq<A>, start: int, stop: int, x: A)
    requires
        0 <= start <= stop <= s.len(),
    ensures
        #[trigger] s.subrange(start, stop).contains(x) <==> (exists|i: int|
            0 <= start <= i < stop <= s.len() && #[trigger] s[i] == x),
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

// Definition of a commutative fold_right operator.
pub open spec fn commutative_foldr<A, B>(f: spec_fn(A, B) -> B) -> bool {
    forall|x: A, y: A, v: B| #[trigger] f(x, f(y, v)) == f(y, f(x, v))
}

// For a commutative fold_right operator, any folding order
// (i.e., any permutation) produces the same result.
pub proof fn lemma_fold_right_permutation<A, B>(l1: Seq<A>, l2: Seq<A>, f: spec_fn(A, B) -> B, v: B)
    requires
        commutative_foldr(f),
        l1.to_multiset() == l2.to_multiset(),
    ensures
        l1.fold_right(f, v) == l2.fold_right(f, v),
    decreases l1.len(),
{
    broadcast use group_to_multiset_ensures;

    if l1.len() > 0 {
        let a = l1.last();
        let i = l2.index_of(a);
        let l2r = l2.subrange(i + 1, l2.len() as int).fold_right(f, v);

        assert(l1.to_multiset().count(a) > 0);
        l1.drop_last().lemma_fold_right_commute_one(a, f, v);
        l2.subrange(0, i).lemma_fold_right_commute_one(a, f, l2r);

        l2.lemma_fold_right_split(f, v, i + 1);
        l2.remove(i).lemma_fold_right_split(f, v, i);

        assert(l2.subrange(0, i + 1).drop_last() == l2.subrange(0, i));
        assert(l1.drop_last() == l1.remove(l1.len() - 1));

        assert(l2.remove(i).subrange(0, i) == l2.subrange(0, i));
        assert(l2.remove(i).subrange(i, l2.remove(i).len() as int) == l2.subrange(
            i + 1,
            l2.len() as int,
        ));

        lemma_fold_right_permutation(l1.drop_last(), l2.remove(i), f, v);
    } else {
        assert(l2.to_multiset().len() == 0);
    }
}

/************************** Lemmas about Take/Skip ***************************/

// This verified lemma used to be an axiom in the Dafny prelude
/// Taking the first `n` elements of a sequence results in a sequence of length `n`,
/// as long as `n` is within the bounds of the original sequence.
pub broadcast proof fn lemma_seq_take_len<A>(s: Seq<A>, n: int)
    ensures
        0 <= n <= s.len() ==> #[trigger] s.take(n).len() == n,
{
}

// This verified lemma used to be an axiom in the Dafny prelude
/// The resulting sequence after taking the first `n` elements from sequence `s` contains
/// element `x` if and only if `x` is contained in the first `n` elements of `s`.
pub broadcast proof fn lemma_seq_take_contains<A>(s: Seq<A>, n: int, x: A)
    requires
        0 <= n <= s.len(),
    ensures
        #[trigger] s.take(n).contains(x) <==> (exists|i: int|
            0 <= i < n <= s.len() && #[trigger] s[i] == x),
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
pub broadcast proof fn lemma_seq_take_index<A>(s: Seq<A>, n: int, j: int)
    ensures
        0 <= j < n <= s.len() ==> #[trigger] s.take(n)[j] == s[j],
{
}

pub proof fn subrange_of_matching_take<T>(a: Seq<T>, b: Seq<T>, s: int, e: int, l: int)
    requires
        a.take(l) == b.take(l),
        l <= a.len(),
        l <= b.len(),
        0 <= s <= e <= l,
    ensures
        a.subrange(s, e) == b.subrange(s, e),
{
    assert forall|i| 0 <= i < e - s implies a.subrange(s, e)[i] == b.subrange(s, e)[i] by {
        assert(a.subrange(s, e)[i] == a.take(l)[i + s]);
        //             assert( b.subrange(s, e)[i] == b.take(l)[i + s] );   // either trigger will do
    }
    // trigger extn equality (verus issue #1257)

    assert(a.subrange(s, e) == b.subrange(s, e));
}

// This verified lemma used to be an axiom in the Dafny prelude
/// Skipping the first `n` elements of a sequence gives a sequence of length `n` less than
/// the original sequence's length.
pub broadcast proof fn lemma_seq_skip_len<A>(s: Seq<A>, n: int)
    ensures
        0 <= n <= s.len() ==> #[trigger] s.skip(n).len() == s.len() - n,
{
}

// This verified lemma used to be an axiom in the Dafny prelude
/// The resulting sequence after skipping the first `n` elements from sequence `s` contains
/// element `x` if and only if `x` is contained in `s` before index `n`.
pub broadcast proof fn lemma_seq_skip_contains<A>(s: Seq<A>, n: int, x: A)
    requires
        0 <= n <= s.len(),
    ensures
        #[trigger] s.skip(n).contains(x) <==> (exists|i: int|
            0 <= n <= i < s.len() && #[trigger] s[i] == x),
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
pub broadcast proof fn lemma_seq_skip_index<A>(s: Seq<A>, n: int, j: int)
    ensures
        0 <= n && 0 <= j < (s.len() - n) ==> #[trigger] s.skip(n)[j] == s[j + n],
{
}

// This verified lemma used to be an axiom in the Dafny prelude
/// If `k` is a valid index between `n` (inclusive) and the length of sequence `s` (exclusive),
/// then the `k-n`th element of the sequence `s.skip(n)` is the same as the `k`th element of the
/// original sequence `s`.
pub broadcast proof fn lemma_seq_skip_index2<A>(s: Seq<A>, n: int, k: int)
    ensures
        0 <= n <= k < s.len() ==> (#[trigger] s.skip(n))[k - n] == #[trigger] s[k],
{
}

// This verified lemma used to be an axiom in the Dafny prelude
/// If `n` is the length of sequence `a`, then taking the first `n` elements of the concatenation
/// `a + b` is equivalent to the sequence `a` and skipping the first `n` elements of the concatenation
/// `a + b` is equivalent to the sequence `b`.
pub broadcast proof fn lemma_seq_append_take_skip<A>(a: Seq<A>, b: Seq<A>, n: int)
    ensures
        #![trigger (a + b).take(n)]
        #![trigger (a + b).skip(n)]
        n == a.len() ==> ((a + b).take(n) =~= a && (a + b).skip(n) =~= b),
{
}

/************* Lemmas about the Commutability of Take and Skip with Update ************/

// This verified lemma used to be an axiom in the Dafny prelude
/// If `i` is in the first `n` indices of sequence `s`, updating sequence `s` at index `i` with
/// value `v` and then taking the first `n` elements is equivalent to first taking the first `n`
/// elements of `s` and then updating index `i` to value `v`.
pub broadcast proof fn lemma_seq_take_update_commut1<A>(s: Seq<A>, i: int, v: A, n: int)
    ensures
        #![trigger s.update(i, v).take(n)]
        0 <= i < n <= s.len() ==> #[trigger] s.update(i, v).take(n) =~= s.take(n).update(i, v),
{
}

// This verified lemma used to be an axiom in the Dafny prelude
/// If `i` is a valid index after the first `n` indices of sequence `s`, updating sequence `s` at
/// index `i` with value `v` and then taking the first `n` elements is equivalent to just taking the first `n`
/// elements of `s` without the update.
pub broadcast proof fn lemma_seq_take_update_commut2<A>(s: Seq<A>, i: int, v: A, n: int)
    ensures
        0 <= n <= i < s.len() ==> #[trigger] s.update(i, v).take(n) =~= s.take(n),
{
}

// This verified lemma used to be an axiom in the Dafny prelude
/// If `i` is a valid index after the first `n` indices of sequence `s`, updating sequence `s` at
/// index `i` with value `v` and then skipping the first `n` elements is equivalent to skipping the first `n`
/// elements of `s` and then updating index `i-n` to value `v`.
pub broadcast proof fn lemma_seq_skip_update_commut1<A>(s: Seq<A>, i: int, v: A, n: int)
    ensures
        0 <= n <= i < s.len() ==> #[trigger] s.update(i, v).skip(n) =~= s.skip(n).update(i - n, v),
{
}

// This verified lemma used to be an axiom in the Dafny prelude
/// If `i` is a valid index in the first `n` indices of sequence `s`, updating sequence `s` at
/// index `i` with value `v` and then skipping the first `n` elements is equivalent to just skipping
/// the first `n` elements without the update.
pub broadcast proof fn lemma_seq_skip_update_commut2<A>(s: Seq<A>, i: int, v: A, n: int)
    ensures
        0 <= i < n <= s.len() ==> #[trigger] s.update(i, v).skip(n) =~= s.skip(n),
{
}

// This verified lemma used to be an axiom in the Dafny prelude
/// Pushing element `v` onto the end of sequence `s` and then skipping the first `n` elements is
/// equivalent to skipping the first `n` elements of `s` and then pushing `v` onto the end.
pub broadcast proof fn lemma_seq_skip_build_commut<A>(s: Seq<A>, v: A, n: int)
    ensures
        #![trigger s.push(v).skip(n)]
        0 <= n <= s.len() ==> s.push(v).skip(n) =~= s.skip(n).push(v),
{
}

// This verified lemma used to be an axiom in the Dafny prelude
/// `s.skip(0)` is equivalent to `s`.
pub broadcast proof fn lemma_seq_skip_nothing<A>(s: Seq<A>, n: int)
    ensures
        n == 0 ==> #[trigger] s.skip(n) =~= s,
{
}

// This verified lemma used to be an axiom in the Dafny prelude
/// `s.take(0)` is equivalent to the empty sequence.
pub broadcast proof fn lemma_seq_take_nothing<A>(s: Seq<A>, n: int)
    ensures
        n == 0 ==> #[trigger] s.take(n) =~= Seq::<A>::empty(),
{
}

// This verified lemma used to be an axiom in the Dafny prelude
/// If `m + n` is less than or equal to the length of sequence `s`, then skipping the first `m` elements
/// and then skipping the first `n` elements of the resulting sequence is equivalent to just skipping
/// the first `m + n` elements.
pub broadcast proof fn lemma_seq_skip_of_skip<A>(s: Seq<A>, m: int, n: int)
    ensures
        (0 <= m && 0 <= n && m + n <= s.len()) ==> #[trigger] s.skip(m).skip(n) =~= s.skip(m + n),
{
}

/// Properties of sequences from the Dafny prelude (which were axioms in Dafny, but proven here in Verus)
// TODO: seems like this warning doesn't come up?
#[deprecated = "Use `broadcast use group_seq_properties` instead"]
pub proof fn lemma_seq_properties<A>()
    ensures
        forall|s: Seq<A>, x: A|
            s.contains(x) <==> exists|i: int| 0 <= i < s.len() && #[trigger] s[i] == x,  //from lemma_seq_contains(s, x),
        forall|x: A| !(#[trigger] Seq::<A>::empty().contains(x)),  //from lemma_seq_empty_contains_nothing(x),
        forall|s: Seq<A>| #[trigger] s.len() == 0 ==> s =~= Seq::<A>::empty(),  //from lemma_seq_empty_equality(s),
        forall|x: Seq<A>, y: Seq<A>, elt: A| #[trigger]
            (x + y).contains(elt) <==> x.contains(elt) || y.contains(elt),  //from lemma_seq_concat_contains_all_elements(x, y, elt),
        forall|s: Seq<A>, v: A, x: A| #[trigger] s.push(v).contains(x) <==> v == x || s.contains(x),  //from lemma_seq_contains_after_push(s, v, x)
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
            (0 <= m && 0 <= n && m + n <= s.len()) ==> #[trigger] s.skip(m).skip(n) == s.skip(
                m + n,
            ),  //from lemma_seq_skip_of_skip(s, m, n),
        forall|s: Seq<A>, a: A| #[trigger] (s.push(a).to_multiset()) =~= s.to_multiset().insert(a),  //from o_multiset_properties
        forall|s: Seq<A>| s.len() == #[trigger] s.to_multiset().len(),  //from to_multiset_ensures
        forall|s: Seq<A>, a: A|
            s.contains(a) <==> #[trigger] s.to_multiset().count(a)
                > 0,  //from to_multiset_ensures
{
    broadcast use {group_seq_properties, lemma_seq_skip_of_skip};
    // TODO: for some reason this still needs to be explicitly stated

    assert forall|s: Seq<A>, v: A, x: A| v == x || s.contains(x) implies #[trigger] s.push(
        v,
    ).contains(x) by {
        lemma_seq_contains_after_push(s, v, x);
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

pub broadcast group group_filter_ensures {
    Seq::lemma_filter_len,
    Seq::lemma_filter_pred,
    Seq::lemma_filter_contains,
}

pub broadcast group group_seq_lib_default {
    group_filter_ensures,
    Seq::add_empty_left,
    Seq::add_empty_right,
    Seq::push_distributes_over_add,
    Seq::filter_distributes_over_add,
    seq_to_set_is_finite,
    Seq::lemma_fold_right_split,
    Seq::lemma_fold_left_split,
}

pub broadcast group group_to_multiset_ensures {
    to_multiset_build,
    to_multiset_remove,
    to_multiset_len,
    to_multiset_contains,
}

// include all the Dafny prelude lemmas
pub broadcast group group_seq_properties {
    lemma_seq_contains,
    lemma_seq_empty_contains_nothing,
    lemma_seq_empty_equality,
    lemma_seq_concat_contains_all_elements,
    lemma_seq_contains_after_push,
    lemma_seq_subrange_elements,
    lemma_seq_take_len,
    lemma_seq_take_contains,
    lemma_seq_take_index,
    lemma_seq_skip_len,
    lemma_seq_skip_contains,
    lemma_seq_skip_index,
    lemma_seq_skip_index2,
    lemma_seq_append_take_skip,
    lemma_seq_take_update_commut1,
    lemma_seq_take_update_commut2,
    lemma_seq_skip_update_commut1,
    lemma_seq_skip_update_commut2,
    lemma_seq_skip_build_commut,
    lemma_seq_skip_nothing,
    lemma_seq_take_nothing,
    // Removed the following from group due to bad verification performance
    // for `lemma_merge_sorted_with_ensures`
    // lemma_seq_skip_of_skip,
    group_to_multiset_ensures,
}

#[doc(hidden)]
pub use assert_seqs_equal_internal;
pub use assert_seqs_equal;

} // verus!
