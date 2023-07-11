#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;
#[allow(unused_imports)]
use crate::pervasive::*;
#[allow(unused_imports)]
use crate::seq::*;
#[allow(unused_imports)]
use crate::set::Set;
#[allow(unused_imports)]
use crate::multiset::Multiset;

#[allow(unused_imports)]
use crate::calc_macro::*;

verus! {

impl<A> Seq<A> {
    /// Applies the function `f` to each element of the sequence, and returns
    /// the resulting sequence.
    /// The `int` parameter of `f` is the index of the element being mapped.
    // TODO(verus): rename to map_entries, for consistency with Map::map
    pub open spec fn map<B>(self, f: FnSpec(int, A) -> B) -> Seq<B> {
        Seq::new(self.len(), |i: int| f(i, self[i]))
    }

    /// Applies the function `f` to each element of the sequence, and returns
    /// the resulting sequence.
    /// The `int` parameter of `f` is the index of the element being mapped.
    // TODO(verus): rename to map, because this is what everybody wants.
    pub open spec fn map_values<B>(self, f: FnSpec(A) -> B) -> Seq<B> {
        Seq::new(self.len(), |i: int| f(self[i]))
    }

    /// Is true if the calling sequence is a prefix of the given sequence 'other'.
    pub open spec fn is_prefix_of(self, other: Self) ->bool
    {
        self.len() <= other.len() && self =~= other.subrange(0,self.len() as int)
    }

    /// Is true if the calling sequence is a suffix of the given sequence 'other'.
    pub open spec fn is_suffix_of(self, other: Self) ->bool
    {
        self.len() <= other.len() && self =~= 
            other.subrange((other.len() - self.len()) as int, other.len() as int)
    }

    #[verifier::opaque]
    pub open spec fn filter(self, pred: FnSpec(A) -> bool) -> Self
        decreases self.len()
    {
        if self.len() == 0 {
            self
        } else {
            let subseq = self.drop_last().filter(pred);
            if pred(self.last()) { subseq.push(self.last()) } else { subseq }
        }
    }

    pub proof fn filter_lemma(self, pred: FnSpec(A) -> bool)
        ensures
            // we don't keep anything bad
            // TODO(andrea): recommends didn't catch this error, where i isn't known to be in
            // self.filter(pred).len()
            //forall |i: int| 0 <= i < self.len() ==> pred(#[trigger] self.filter(pred)[i]),
            forall |i: int| 0 <= i < self.filter(pred).len() ==> pred(#[trigger] self.filter(pred)[i]),
            // we keep everything we should
            forall |i: int| 0 <= i < self.len() && pred(self[i])
                ==> #[trigger] self.filter(pred).contains(self[i]),
            // the filtered list can't grow
            self.filter(pred).len() <= self.len(),
        decreases self.len()
    {
        reveal(Self::filter);
        let out = self.filter(pred);
        if 0 < self.len() {
            self.drop_last().filter_lemma(pred);
            assert forall |i: int| 0 <= i < out.len() implies pred(out[i]) by {
                if i < out.len()-1 {
                    assert(self.drop_last().filter(pred)[i] == out.drop_last()[i]); // trigger drop_last
                    assert(pred(out[i]));   // TODO(andrea): why is this line required? It's the conclusion of the assert-forall.
                }
            }
            assert forall |i: int| 0 <= i < self.len() && pred(self[i])
                implies #[trigger] out.contains(self[i]) by {
                if i==self.len()-1 {
                    assert(self[i] == out[out.len()-1]);  // witness to contains
                } else {
                    let subseq = self.drop_last().filter(pred);
                    assert(subseq.contains(self.drop_last()[i]));   // trigger recursive invocation
                    let j = choose|j| 0<=j<subseq.len() && subseq[j]==self[i];
                    assert(out[j] == self[i]);  // TODO(andrea): same, seems needless
                }
            }
        }
    }

    #[verifier(external_body)]
    #[verifier(broadcast_forall)]
    pub proof fn filter_lemma_broadcast(self, pred: FnSpec(A) -> bool)
        ensures
            forall |i: int| 0 <= i < self.filter(pred).len() ==> pred(#[trigger] self.filter(pred)[i]),
            forall |i: int| 0 <= i < self.len() && pred(self[i])
                ==> #[trigger] self.filter(pred).contains(self[i]),
            #[trigger] self.filter(pred).len() <= self.len();

    proof fn filter_distributes_over_add(a:Self, b:Self, pred:FnSpec(A)->bool)
    ensures
        (a+b).filter(pred) == a.filter(pred) + b.filter(pred),
    decreases b.len()
    {
        reveal(Self::filter);
        if 0 < b.len()
        {
            Self::drop_last_distributes_over_add(a, b);
            Self::filter_distributes_over_add(a, b.drop_last(), pred);
            if pred(b.last()) {
                Self::push_distributes_over_add(a.filter(pred), b.drop_last().filter(pred), b.last());
            }
        } else {
            Self::add_empty(a, b);
            Self::add_empty(a.filter(pred), b.filter(pred));
        }
    }

    pub proof fn add_empty(a: Self, b: Self)
    requires
        b.len() == 0,
    ensures
        a+b == a,
    {
        assert_seqs_equal!(a+b, a);
    }

    pub proof fn push_distributes_over_add(a: Self, b: Self, elt: A)
    ensures
        (a+b).push(elt) == a+b.push(elt),
    {
        assert_seqs_equal!((a+b).push(elt), a+b.push(elt));
    }

    #[verifier(external_body)]
    #[verifier(broadcast_forall)]
    pub proof fn filter_distributes_over_add_broacast(a:Self, b:Self, pred:FnSpec(A)->bool)
    ensures
        #[trigger] (a+b).filter(pred) == a.filter(pred) + b.filter(pred),
    {
    // TODO(chris): We have perfectly good proofs sitting around for these broadcasts; they don't
    // need to be axioms!
//        assert forall |a:Self, b:Self, pred:FnSpec(A)->bool| (a+b).filter(pred) == a.filter(pred) + b.filter(pred) by {
//            Self::filter_distributes_over_add(a, b, pred);
//        }
    }

    #[verifier(external_body)]
    #[verifier(broadcast_forall)]
    pub proof fn add_empty_broacast(a:Self, b:Self)
    ensures
        b.len()==0 ==> a+b == a
    {
//        assert forall |a:Self, b:Self| b.len()==0 implies a+b == a {
//            add_empty(a, b);
//        }
    }

    #[verifier(external_body)]
    #[verifier(broadcast_forall)]
    pub proof fn push_distributes_over_add_broacast(a:Self, b:Self, elt: A)
    ensures
        (a+b).push(elt) == a+b.push(elt),
    {
//        assert forall |a:Self, b:Self, elt: A| (a+b).push(elt) == a+b.push(elt) {
//            push_distributes_over_add(a, b, elt);
//        }
    }

    /// Returns the maximum value in a non-empty sequence, given sorting function leq
    pub open spec fn max(self, leq: FnSpec(A,A) ->bool) -> A
       recommends self.len() > 0,
       decreases self.len(),
    {
        if self.len() > 1 {
            //let elt = self.subrange(1,self.len() as int).max(leq);
            if leq(self[0],self.subrange(1,self.len() as int).max(leq)) {
                self.subrange(1,self.len() as int).max(leq)
            }
            else {self[0]}
        } else {self[0]}
    }

    /// Returns the minimum value in a non-empty sequence, given sorting function leq
    pub open spec fn min(self, leq: FnSpec(A,A) ->bool) -> A
       recommends self.len() > 0,
       decreases self.len(),
    {
        if self.len() > 1 {
            let subseq = self.subrange(1,self.len() as int);
            let elt = subseq.min(leq);
            if leq(elt,self[0]) {elt}
            else {self[0]}
        } else {self[0]}
    }

    // TODO is_sorted -- extract from summer_school e22
    pub open spec fn contains(self, needle: A) -> bool {
        exists|i: int| 0 <= i < self.len() && self[i] == needle
    }

    /// Returns some index if an element occurs at least once in a sequence
    /// and occurs at index i. Otherwise returns an arbitrary value.
    pub open spec fn index_of(self, needle: A) -> int {
        choose|i: int| 0 <= i < self.len() && self[i] == needle
    }

    /// Returns Some(i), if an element occurs at least once in a sequence and
    /// occurs at index i. Otherwise the return is None.
    pub open spec fn index_of_option(self, needle: A) -> (result: Option<int>)
    {
        if (self.contains(needle)) {Some(self.index_of(needle))}
        else {None}
    }

    /// For an element that occurs at least once in a sequence, the index of its
    /// first occurence is returned. Otherwise, -1 is returned
    pub open spec fn first_index_of(self, needle:A) -> int{
        self.first_index_helper(needle,0)
    }

    /// Recursive helper function for first_index_of
    pub closed spec fn first_index_helper(self, needle: A, index: int) -> int
        decreases self.len(),
    {   if self.len() <= 0 {
            -1
        }
        else if self[0] == needle {
            index
        }
        else {
            self.subrange(1,self.len() as int).first_index_helper(needle, index+1)
        }
    }

    /// For an element that occurs at least once in a sequence, if its first occurence
    /// is at index i, Some(i) is returned. Otherwise, None is returned
    pub open spec fn first_index_of_option(self, needle:A) -> Option<int> {
        let val = self.first_index_of(needle);
        if val >= 0 {Some(val)}
        else {None}
    }

    /// For an element that occurs at least once in a sequence, the index of its
    /// last occurence is returned. Otherwise, -1 is returned
    pub open spec fn last_index_of(self, needle:A) -> int{
        self.last_index_helper(needle,self.len()-1 as int)
    }

    /// Recursive helper function for last_index_of
    pub closed spec fn last_index_helper(self, needle: A, index: int) -> int
        decreases self.len(),
    {   if self.len() <= 0 {
            -1
        }
        else if self.last() == needle {
            index
        }
        else {
            self.subrange(0,self.len()-1 as int).last_index_helper(needle, index-1)
        }
    }

    /// For an element that occurs at least once in a sequence, if its last occurence
    /// is at index i, Some(i) is returned. Otherwise, None is returned
    pub open spec fn last_index_of_option(self, needle:A) -> Option<int> {
        let val = self.last_index_of(needle);
        if val >= 0 {Some(val)}
        else {None}
    }

    /// Drops the last element of a sequence and returns a sequence whose length is
    /// thereby 1 smaller.
    ///
    /// If the input sequence is empty, the result is meaningless and arbitrary.
    pub open spec fn drop_last(self) -> Seq<A>
        recommends self.len() >= 1
    {
        self.subrange(0, self.len() as int - 1)
    }

    pub proof fn drop_last_distributes_over_add(a: Self, b: Self)
    requires
        0 < b.len(),
    ensures
        (a+b).drop_last() == a+b.drop_last(),
    {
        assert_seqs_equal!((a+b).drop_last(), a+b.drop_last());
    }

    pub open spec fn drop_first(self) -> Seq<A>
        recommends self.len() >= 1
    {
        self.subrange(1, self.len() as int)
    }

    /// returns `true` if the sequence has no duplicate elements
    pub open spec fn no_duplicates(self) -> bool {
        forall|i, j| 0 <= i < self.len() && 0 <= j < self.len() && i != j
            ==> self[i] != self[j]
    }

    /// Returns `true` if two sequences are disjoint
    pub open spec fn disjoint(self, other: Self) -> bool {
        forall|i: int, j: int| 0 <= i < self.len() && 0 <= j < other.len() ==> self[i] != other[j]
    }

    /// Converts a sequence into a set
    pub open spec fn to_set(self) -> Set<A> {
        Set::new(|a: A| self.contains(a))
    }

    // /// Converts a sequence into a multiset
    // pub open spec fn to_multiset(self) -> Multiset<A> 
    //     decreases self.len()
    // {
    //     if self.len() == 0 {
    //         Multiset::<A>::empty()
    //     } else {
    //         Multiset::<A>::empty().insert(self.first()).add(self.drop_first().to_multiset())
    //     }
    // }

    /// Insert item a at index i, shifting remaining elements (if any) to the right
    pub open spec fn insert(self, i: int, a:A) -> Seq<A>
        recommends 0 <= i <= self.len()
    {
        self.subrange(0, i).push(a) + self.subrange(i, self.len() as int)
    }

    /// Remove item at index i, shifting remaining elements to the left
    pub open spec fn remove(self, i: int) -> Seq<A>
        recommends 0 <= i < self.len()
    {
        self.subrange(0, i) + self.subrange(i + 1, self.len() as int)
    }

    /// If a given element occurs at least once in a sequence, the sequence without
    /// its first occurrence is returned. Otherwise the same sequence is returned.
    pub open spec fn remove_value(self, val :A) -> Seq<A>
    {
        let index = self.first_index_of(val);
        if index >= 0 {self.remove(index)}
        else {self}
    }

    /// Returns the sequence that is in reverse order to a given sequence.
    pub open spec fn reverse(self) -> Seq<A>
        decreases self.len()
    {
        if self.len() == 0 {Seq::empty()}
        else {
            Seq::new(self.len(), |i: int| self[self.len()-1-i])
        }
    }

    /// Zips two sequences of equal length into one sequence that consists of pairs.
    /// If the two sequences are different lengths, returns an empty sequence
    pub open spec fn zip_with<B>(self, other: Seq<B>) -> Seq<(A,B)>
        recommends self.len() == other.len()
        decreases self.len()
    {
        if self.len() != other.len() {Seq::empty()}
        else if self.len() == 0 {Seq::empty()}
        else{
            Seq::new(self.len(), |i: int| (self[i],other[i]))
        }
    }
        

    /// Folds the sequence to the left, applying `f` to perform the fold.
    ///
    /// Equivalent to `Iterator::fold` in Rust.
    ///
    /// Given a sequence `s = [x0, x1, x2, ..., xn]`, applying this function `s.fold_left(b, f)`
    /// returns `f(...f(f(b, x0), x1), ..., xn)`.
    pub open spec fn fold_left<B>(self, b: B, f: FnSpec(B, A) -> B) -> (res: B)
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
    pub open spec fn fold_left_alt<B>(self, b: B, f: FnSpec(B, A) -> B) -> (res: B)
        decreases self.len(),
    {
        if self.len() == 0 {
            b
        } else {
            self.subrange(1, self.len() as int).fold_left_alt(f(b, self[0]), f)
        }
    }

    /// An auxiliary lemma for proving [`Self::lemma_fold_left_alt`].
    proof fn aux_lemma_fold_left_alt<B>(self, b: B, f: FnSpec(B, A) -> B, k: int)
        requires 0 < k <= self.len(),
        ensures
          self.subrange(k, self.len() as int)
              .fold_left_alt(
                  self.subrange(0, k).fold_left_alt(b, f), f) ==
          self.fold_left_alt(b, f),
        decreases k,
    {
        reveal_with_fuel(Self::fold_left_alt::<B>, 2);
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
    pub proof fn lemma_fold_left_alt<B>(self, b: B, f: FnSpec(B, A) -> B)
        ensures self.fold_left(b, f) == self.fold_left_alt(b, f),
        decreases self.len(),
    {
        reveal_with_fuel(Self::fold_left::<B>, 2);
        reveal_with_fuel(Self::fold_left_alt::<B>, 2);
        if self.len() <= 1 {
            // trivial base cases
        } else {
            self.aux_lemma_fold_left_alt(b, f, self.len() - 1);
            self.subrange(self.len() - 1, self.len() as int)
                .lemma_fold_left_alt(self.drop_last().fold_left_alt(b, f), f);
            self.subrange(0, self.len() - 1).lemma_fold_left_alt(b, f);
        }
    }

    /// Folds the sequence to the right, applying `f` to perform the fold.
    ///
    /// Equivalent to `DoubleEndedIterator::rfold` in Rust.
    ///
    /// Given a sequence `s = [x0, x1, x2, ..., xn]`, applying this function `s.fold_right(b, f)`
    /// returns `f(x0, f(x1, f(x2, ..., f(xn, b)...)))`.
    pub open spec fn fold_right<B>(self, f: FnSpec(A, B) -> B, b: B) -> (res: B)
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
    pub open spec fn fold_right_alt<B>(self, f: FnSpec(A, B) -> B, b: B) -> (res: B)
        decreases self.len(),
    {
        if self.len() == 0 {
            b
        } else {
            f(self[0], self.subrange(1, self.len() as int).fold_right_alt(f, b))
        }
    }

    /// An auxiliary lemma for proving [`Self::lemma_fold_right_alt`].
    proof fn aux_lemma_fold_right_alt<B>(self, f: FnSpec(A, B) -> B, b: B, k: int)
        requires 0 <= k < self.len(),
        ensures
          self.subrange(0, k).fold_right(f, self.subrange(k, self.len() as int).fold_right(f, b)) ==
          self.fold_right(f, b),
        decreases self.len(),
    {
        reveal_with_fuel(Self::fold_right::<B>, 2);
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
    pub proof fn lemma_fold_right_alt<B>(self, f: FnSpec(A, B) -> B, b: B)
        ensures self.fold_right(f, b) == self.fold_right_alt(f, b),
        decreases self.len(),
    {
        reveal_with_fuel(Self::fold_right::<B>, 2);
        reveal_with_fuel(Self::fold_right_alt::<B>, 2);
        if self.len() <= 1 {
            // trivial base cases
        } else {
            self.subrange(1, self.len() as int).lemma_fold_right_alt(f, b);
            self.aux_lemma_fold_right_alt(f, b, 1);
        }
    }
}

//TODO: Should this be its own impl block, or somehow fit it into the previous one?
impl<A,B> Seq<(A,B)>{

    /// Unzips a sequence that contains pairs into two separate sequences.
    pub open spec fn unzip(self) -> (Seq<A>, Seq<B>)
        decreases self.len()
    {
        if self.len() == 0 {(Seq::empty(), Seq::empty())}
        else{
            let s0 = Seq::new(self.len(), |i: int| self[i].0);
            let s1 = Seq::new(self.len(), |i: int| self[i].1);
            (s0,s1)
        }
    }

}

impl<A> Seq<Seq<A>>{

    /// Flattens a sequence of sequences into a single sequence by concatenating 
    ///  subsequences, starting from the first element. 
    pub open spec fn flatten(self) -> Seq<A>
        decreases self.len()
    {
        if self.len() == 0 {Seq::empty()}
        else {
            self.first().add(self.drop_first().flatten())
        }
    }

    /// Flattens a sequence of sequences into a single sequence by concatenating 
    /// subsequences in reverse order, i.e. starting from the last element.
    pub open spec fn flatten_reverse(self) -> Seq<A>
        decreases self.len()
    {
        if self.len() == 0 {Seq::empty()}
        else {
            self.drop_last().flatten_reverse().add(self.last())
            //self.reverse().flatten()
        }
    }
}

/// The concatenation of two subsequences of a non-empty sequence, the first obtained 
/// from dropping the last element, the second consisting only of the last 
/// element, is the original sequence.
pub proof fn lemma_add_last_back<A>(s: Seq<A>)
    requires 
        0 < s.len(),
    ensures
        #[trigger] s.drop_last().push(s.last()) =~= s,
{}

/// The last element of two concatenated sequences, the second one being non-empty, will be the 
/// last element of the latter sequence.
pub proof fn lemma_append_last<A>(s1 :Seq<A>, s2 :Seq<A>)
    requires
        0 < s2.len(),
    ensures
        #[trigger] (s1 + s2).last() == s2.last(),
{}

/// The concatenation of sequences is associative
//#[verifier(broadcast_forall)]
pub proof fn lemma_concat_associative<A>(s1 : Seq<A>, s2 :Seq<A>, s3 :Seq<A>)
    ensures
        #[trigger] s1.add(s2.add(s3)) =~= #[trigger] s1.add(s2).add(s3),
{}

/* could not figure out triggers for these two */
/// If a predicate is true at every index of a sequence,
/// it is true for every member of the sequence as a collection.
/// Useful for converting quantifiers between the two forms
/// to satisfy a precondition in the latter form.
// #[verifier(broadcast_forall)]
pub proof fn lemma_indexing_implies_membership<A>(f: FnSpec(A)->bool, s: Seq<A>)
    requires
        forall |i: int| 0<= i < s.len() ==> #[trigger] f(#[trigger] s[i]),
    ensures
        forall |x: A| #[trigger] s.contains(x) ==> #[trigger] f(x),
{
    assert(forall |i: int| 0<= i < s.len() ==> #[trigger] s.contains(s[i]));
}

/// If a predicate is true for every member of a sequence as a collection,
/// it is true at every index of the sequence.
/// Useful for converting quantifiers between the two forms
/// to satisfy a precondition in the latter form.
//#[verifier(broadcast_forall)]
pub proof fn lemma_membership_implies_indexing<A>(f: FnSpec(A)->bool, s: Seq<A>)
    requires
        forall |x: A| #[trigger] s.contains(x) ==> #[trigger] f(x),
    ensures
        forall |i: int| 0<= i < s.len() ==> #[trigger] f(s[i]),   
{
    assert forall |i: int| 0<= i < s.len() implies #[trigger] f(s[i]) by {
        assert(#[trigger] s.contains(s[i]));
    }
}

/// A sequence that is sliced at the pos-th element, concatenated 
/// with that same sequence sliced from the pos-th element, is equal to the 
/// original unsliced sequence.
//#[verifier(broadcast_forall)]
pub proof fn lemma_split_at<A>(s: Seq<A>, pos: int)
    requires 
        0 <= pos <= s.len(),
    ensures 
        #[trigger] s.subrange(0,pos) + #[trigger] s.subrange(pos,s.len() as int) =~= s
{}

/// Any element in a slice is included in the original sequence.
//#[verifier(broadcast_forall)]
pub proof fn lemma_element_from_slice<A>(old: Seq<A>, new: Seq<A>, a: int, b:int, pos: int)
    requires
        0 <= a <= b <= #[trigger] old.len(),
        new == #[trigger] old.subrange(a,b),
        a <= pos < b
    ensures
        pos - a < #[trigger] new.len(),
        new[pos-a] == #[trigger] old[pos],
{}

/// A slice (from s2..e2) of a slice (from s1..e1) of a sequence is equal to just a 
/// slice (s1+s2..s1+e2) of the original sequence.
//#[verifier(broadcast_forall)]
pub proof fn lemma_slice_of_slice<A>(original: Seq<A>, s1 :int, e1: int, s2: int, e2: int)
    requires 
        0 <= s1 <= e1 <= original.len(),
        0 <= s2 <= e2 <= e1 - s1,
    ensures
        original.subrange(s1,e1).subrange(s2,e2) =~= original.subrange(s1+s2,s1+e2),
{}

/// recursive definition of seq to set conversion
spec fn seq_to_set_rec<A>(seq: Seq<A>) -> Set<A>
    decreases seq.len()
{
    if seq.len() == 0 {
        Set::empty()
    } else {
        seq_to_set_rec(seq.drop_last()).insert(seq.last())
    }
}

/// helper function showing that the recursive definition of set_to_seq produces a finite set
proof fn seq_to_set_rec_is_finite<A>(seq: Seq<A>)
    ensures seq_to_set_rec(seq).finite()
    decreases seq.len()
{
    if seq.len() > 0{
        let sub_seq = seq.drop_last();
        assert(seq_to_set_rec(sub_seq).finite()) by {
            seq_to_set_rec_is_finite(sub_seq);
        }
    }
}

/// helper function showing that the resulting set contains all elements of the sequence
proof fn seq_to_set_rec_contains<A>(seq: Seq<A>)
    ensures forall |a| #[trigger] seq.contains(a) <==> seq_to_set_rec(seq).contains(a)
    decreases seq.len()
{
    if seq.len() > 0 {
        assert(forall |a| #[trigger] seq.drop_last().contains(a) <==> seq_to_set_rec(seq.drop_last()).contains(a)) by {
            seq_to_set_rec_contains(seq.drop_last());
        }

        assert(seq =~= seq.drop_last().push(seq.last()));
        assert forall |a| #[trigger] seq.contains(a) <==> seq_to_set_rec(seq).contains(a) by {
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

/// helper function showing that the recursive definition matches the set comprehension one
proof fn seq_to_set_equal_rec<A>(seq: Seq<A>)
    ensures seq.to_set() == seq_to_set_rec(seq)
{
    assert(forall |n| #[trigger] seq.contains(n) <==> seq_to_set_rec(seq).contains(n)) by {
        seq_to_set_rec_contains(seq);
    }
    assert(forall |n| #[trigger] seq.contains(n) <==> seq.to_set().contains(n));
    assert(seq.to_set() =~= seq_to_set_rec(seq));
}


/// proof function showing that the set obtained from the sequence is finite
pub proof fn seq_to_set_is_finite<A>(seq: Seq<A>)
    ensures seq.to_set().finite()
{
    assert(seq.to_set().finite()) by {
        seq_to_set_equal_rec(seq);
        seq_to_set_rec_is_finite(seq);
    }
}

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn seq_to_set_is_finite_broadcast<A>(seq: Seq<A>)
    ensures #[trigger] seq.to_set().finite()
{
    // TODO: merge this with seq_to_set_is_finite when broadcast_forall is better supported
}

/// A sequence of unique items, when converted to a set, produces a set with matching length
pub proof fn unique_seq_to_set<A>(seq:Seq<A>)
    requires seq.no_duplicates(),
    ensures seq.len() == seq.to_set().len()
    decreases seq.len(),
{
    seq_to_set_equal_rec::<A>(seq);
    if seq.len() == 0 {
    } else {
        let rest = seq.drop_last();
        unique_seq_to_set::<A>(rest);
        seq_to_set_equal_rec::<A>(rest);
        seq_to_set_rec_is_finite::<A>(rest);
        assert(!seq_to_set_rec(rest).contains(seq.last()));
        assert(seq_to_set_rec(rest).insert(seq.last()).len() == seq_to_set_rec(rest).len() + 1);
    }
}

/// The cardinality of a set of elements is always less than or 
/// equal to that of the full sequence of elements.
pub proof fn lemma_cardinality_of_set<A>(s: Seq<A>)
    ensures s.to_set().len() <= s.len(),
    decreases s.len(),
{
    // if (s.no_duplicates()) {
    //     assert(s.to_set().len() == s.len()) by {
    //         unique_seq_to_set(s)
    //     }
    // }
    // else if s.len() > 0 {
    //     assert(forall |x: A| #[trigger] s.contains(x) 
    //         ==> #[trigger] s.drop_last().contains(x) || s.last() == x) by {
    //         lemma_add_last_back(s)
    //     }
    //     if s.drop_last().contains(s.last()) {
    //         // the last element is duplicated somewhere else.
    //         assert(s.drop_last().to_set() =~= s.to_set());
    //         lemma_cardinality_of_set(s.drop_last());
    //     } else {
    //        // the last element appears only once
    //         assert(s.drop_last().to_set().insert(s.last()) =~= s.to_set());
    //         lemma_cardinality_of_set(s.drop_last());
    //     }
    // }
    if s.len() == 0 {}
    else {
        // lemma_concat_elts(s.drop_last(), seq![s.last()]);
        // lemma_add_last_back(s);
        // assert(s.drop_last().push(s.last()) =~= s.drop_last() + seq![s.last()]);
        assert(s.drop_last().to_set().insert(s.last()) =~= s.to_set());
        lemma_cardinality_of_set(s.drop_last());
        // assert(s.drop_last().to_set().len() <= s.drop_last().len());
    }
}

/// A sequence is of length 0 if and only if its conversion to
/// a set results in the empty set.
pub proof fn lemma_cardinality_of_empty_set_is_0<A>(s: Seq<A>)
    ensures
        s.to_set().len() == 0 <==> s.len() == 0,
{
    assert(s.len() == 0 ==> s.to_set().len() == 0) by {
        lemma_cardinality_of_set(s)
    }
    assert(!(s.len() == 0) ==> !(s.to_set().len() == 0)) by {
        if s.len() > 0 {
            assert(s.to_set().contains(s[0]));
            assert(s.to_set().remove(s[0]).len() <= s.to_set().len());
        }
    }
}

pub proof fn lemma_insert_properties<A>(s: Seq<A>, pos: int, elt:A)
    requires 
        0 <= pos <= s.len(),
    ensures
        s.insert(pos, elt).len() == s.len() +1,
        forall |i: int| 0<= i < pos ==> #[trigger] s.insert(pos, elt)[i] == #[trigger] s[i],
        forall |i: int| pos <= i < s.len() ==> s.insert(pos, elt)[i+1] == s[i],
        s.insert(pos, elt)[pos] == elt,
{}

pub proof fn lemma_unzip_properties<A,B>(s: Seq<(A,B)>)
    ensures
        s.unzip().0.len() == s.unzip().1.len(),
        s.unzip().0.len() == s.len(),
        s.unzip().1.len() == s.len(),
        forall |i: int| 0<= i < s.len() 
                ==> (#[trigger] s.unzip().0[i], #[trigger] s.unzip().1[i]) == s[i],
    decreases
        s.len(),
{
    if s.len() > 0 {
        lemma_unzip_properties(s.drop_last());
    }
}

pub proof fn lemma_zip_of_unzip<A,B>(s: Seq<(A,B)>)
    ensures s.unzip().0.zip_with(s.unzip().1) =~= s,
    decreases s.len(),
{}

pub proof fn lemma_max_properties<A>(s: Seq<A>, leq: FnSpec(A,A) ->bool)
    requires
        forall |x: A| #[trigger] leq(x,x),
        forall |x: A, y: A| !(#[trigger] leq(x,y)) ==> #[trigger] leq(y,x),
        forall |x: A, y: A| #[trigger] leq(x,y) ==> x==y || !(#[trigger] leq(y,x)),
        forall |x: A, y: A, z: A| #[trigger] leq(x,y) && #[trigger] leq(y,z) ==> #[trigger] leq(x,z),
    ensures
        forall |x: A| s.contains(x) ==> leq(x,s.max(leq)),
        forall |i: int| 0<= i < s.len() ==> leq(s[i],s.max(leq)),
        s.len() == 0 || s.contains(s.max(leq)),
    decreases 
        s.len(),
{
    if s.len() <=1 {}
    else {
        let elt = s.subrange(1,s.len() as int).max(leq);
        assert(!leq(s[0], elt) ==> leq(elt, s[0]));
        assert(s.subrange(1,s.len() as int).contains(elt)) by {
            lemma_max_properties(s.subrange(1,s.len() as int), leq)
        }
        assert forall |i: int| 0<= i <s.len() implies leq(s[i],s.max(leq)) by {
            assert(i==0 || s[i] == s.drop_first()[i-1]);
            assert(forall |j: int| 0<= j < s.drop_first().len() 
                    ==> leq(s.drop_first()[j],s.drop_first().max(leq))) by {
                lemma_max_properties(s.drop_first(), leq)
            }
        }
    }
}

pub proof fn lemma_min_properties<A>(s: Seq<A>, leq: FnSpec(A,A) ->bool)
    requires
        forall |x: A| #[trigger] leq(x,x),
        forall |x: A, y: A| !(#[trigger] leq(x,y)) ==> #[trigger] leq(y,x),
        forall |x: A, y: A| #[trigger] leq(x,y) ==> x==y || !(#[trigger] leq(y,x)),
        forall |x: A, y: A, z: A| #[trigger] leq(x,y) && #[trigger] leq(y,z) ==> #[trigger] leq(x,z),
    ensures
        forall |x: A| s.contains(x) ==> leq(s.min(leq),x),
        forall |i: int| 0<= i < s.len() ==> leq(s.min(leq),s[i]),
        s.len() == 0 || s.contains(s.min(leq)),
    decreases 
        s.len(),
{
    if s.len() <=1 {}
    else {
        let elt = s.drop_first().min(leq);
        assert(!leq(s[0], elt) ==> leq(elt, s[0]));
        assert(s.subrange(1,s.len() as int).contains(elt)) by {
            lemma_min_properties(s.drop_first(), leq)
        }
        assert forall |i: int| 0<= i <s.len() implies leq(s.min(leq), s[i]) by {
            assert(i==0 || s[i] == s.drop_first()[i-1]);
            assert(forall |j: int| 0<= j < s.drop_first().len() 
                    ==> leq(s.drop_first().min(leq),s.drop_first()[j])) by {
                lemma_min_properties(s.drop_first(), leq)
            }
        }
    }
}

/// The maximum of the concatenation of two non-empty sequences is greater than or 
/// equal to the maxima of its two non-empty subsequences.
pub proof fn lemma_max_of_concat<A>(x: Seq<A>, y: Seq<A>, leq: FnSpec(A,A) ->bool)
    requires
        0 < x.len() && 0 < y.len(),
        //Properties of an leq function:
        forall |x: A| #[trigger] leq(x,x),
        forall |x: A, y: A| !(#[trigger] leq(x,y)) ==> #[trigger] leq(y,x),
        forall |x: A, y: A| #[trigger] leq(x,y) ==> x==y || !(#[trigger] leq(y,x)),
        forall |x: A, y: A, z: A| #[trigger] leq(x,y) && #[trigger] leq(y,z) ==> #[trigger] leq(x,z),
    ensures
        leq(x.max(leq), (x + y).max(leq)),
        leq(y.max(leq), (x + y).max(leq)),
        forall |elt: A| (x+y).contains(elt) ==> leq(elt, (x + y).max(leq)),
    decreases
        x.len(),
{
    lemma_max_properties(x,leq);
    lemma_max_properties(y,leq);
    lemma_max_properties((x+y),leq);
    lemma_concat_elts(x,y);
    if x.len() == 1 {
        assert(leq(y.max(leq), (x + y).max(leq))) by {
            assert((x+y).contains(y.max(leq)));
        }
    } else {
        assert(leq(x.max(leq), (x + y).max(leq))) by {
            assert((x+y).contains(x.max(leq)));
        }
        assert(x.drop_first() + y =~= (x+y).drop_first());
        lemma_max_of_concat(x.drop_first(),y,leq);
    }
}

/// The minimum of the concatenation of two non-empty sequences is less than or 
/// equal to the minimum of its two non-empty subsequences.
pub proof fn lemma_min_of_concat<A>(x: Seq<A>, y: Seq<A>, leq: FnSpec(A,A) ->bool)
    requires
        0 < x.len() && 0 < y.len(),
        //Properties of an leq function:
        forall |x: A| #[trigger] leq(x,x),
        forall |x: A, y: A| !(#[trigger] leq(x,y)) ==> #[trigger] leq(y,x),
        forall |x: A, y: A| #[trigger] leq(x,y) ==> x==y || !(#[trigger] leq(y,x)),
        forall |x: A, y: A, z: A| #[trigger] leq(x,y) && #[trigger] leq(y,z) ==> #[trigger] leq(x,z),
    ensures
        leq((x + y).min(leq),x.min(leq)),
        leq((x + y).min(leq), y.min(leq)),
        forall |elt: A| (x+y).contains(elt) ==> leq((x + y).min(leq),elt),
    decreases
        x.len(),
{
    lemma_min_properties(x,leq);
    lemma_min_properties(y,leq);
    lemma_min_properties((x+y),leq);
    lemma_concat_elts(x,y);
    if x.len() == 1 {
        assert(leq((x + y).min(leq),y.min(leq))) by {
            assert((x+y).contains(y.min(leq)));
        }
    } else {
        assert(leq((x + y).min(leq),x.min(leq))) by {
            assert((x+y).contains(x.min(leq)));
        }
        assert(x.drop_first() + y =~= (x+y).drop_first());
        lemma_max_of_concat(x.drop_first(),y,leq)
    }
}

/// The concatenation of two sequences contains only the elements
/// of the two sequences
// TODO: broadcast forall for dafny-level automation since dafny includes as an axiom
pub proof fn lemma_concat_elts<A>(x: Seq<A>, y: Seq<A>)
    ensures
        forall |elt: A| #[trigger] (x+y).contains(elt) <==> x.contains(elt) ||  y.contains(elt),
    decreases
        x.len(),
{
    if x.len() == 0 && y.len() >0 {
        assert((x+y) =~= y);
    } else {
        assert forall |elt: A| #[trigger] x.contains(elt) implies #[trigger] (x+y).contains(elt)
        by {
            let index = choose |i: int| 0 <= i < x.len() && x[i] == elt;
            assert((x+y)[index] == elt);
        }
        assert forall |elt: A| #[trigger] y.contains(elt) implies #[trigger] (x+y).contains(elt)
        by {
            let index = choose |i: int| 0 <= i < y.len() && y[i] == elt;
            assert((x+y)[index+x.len()] == elt);
        }
    }
}

/// A sequence with cardinality equal to its set has no duplicates.
/// Inverse of the above function unique_seq_to_set
//#[verifier(broadcast_forall)]
pub proof fn lemma_no_dup_set_cardinality<A>(s: Seq<A>)
    requires 
        s.to_set().len() == #[trigger] s.len(),
    ensures
        #[trigger] s.no_duplicates(),
    decreases s.len(),
{
    if s.len() > 0 {
        assert(s =~= Seq::empty().push(s.first()).add(s.drop_first()));
        if s.drop_first().contains(s.first()){
            // If there is a duplicate, then we show that |s.to_set()| == |s| cannot hold.
            assert(s.to_set() =~= s.drop_first().to_set());
            assert(s.to_set().len() <= s.drop_first().len()) by {
                lemma_cardinality_of_set(s.drop_first())
            }
        } else {
            assert(s.to_set().len() == 1 + s.drop_first().to_set().len()) by {
                assert(s.drop_first().to_set().insert(s.first()) =~= s.to_set());
            }
            lemma_no_dup_set_cardinality(s.drop_first());
        }
    }
}

/// If sequences a and b don't have duplicates and there are no 
/// elements in common between them, then the concatenated sequence 
/// a + b will not contain duplicates either.
//#[verifier(broadcast_forall)]
pub proof fn lemma_no_dup_in_concat<A>(a: Seq<A>, b: Seq<A>)
    requires
        a.no_duplicates(),
        b.no_duplicates(),
        forall |i: int, j: int| 0 <= i < a.len() && 0 <= j < b.len()
            ==> a[i] != b[j]
    ensures
        #[trigger] (a+b).no_duplicates(),
{}


/**********************************************/
/*           Lemmas about Flattening          */
/**********************************************/

/// Flattening sequences of sequences is distributive over concatenation. That is, concatenating
/// the flattening of two sequences of sequences is the same as flattening the 
/// concatenation of two sequences of sequences.
pub proof fn lemma_flatten_concat<A>(x: Seq<Seq<A>>, y: Seq<Seq<A>>)
    ensures 
        (x+y).flatten() =~= x.flatten() + y.flatten()
    decreases 
        x.len()
{
    if x.len() == 0 {
        assert(x.flatten() == Seq::<A>::empty());
        assert(x+y =~= y);
    } else {
        assert((x+y).first() == x.first());
        assert((x+y).drop_first() =~= x.drop_first() + y); // OBSERVE
        // step 1 - 2
        assert((x+y).flatten() =~= x.first() + (x.drop_first() + y).flatten());
        // step 2 - 3
        assert(x.first() + (x.drop_first() + y).flatten() =~= x.first() + x.drop_first().flatten() + y.flatten()) by {
            lemma_flatten_concat(x.drop_first(), y);
        } // OBSERVE
        // step 3 - 4
        assert(x.first() + x.drop_first().flatten() =~= x.flatten());
        assert(x.first() + x.drop_first().flatten() + y.flatten()
                =~= x.flatten() + y.flatten());
    }
}

/// Flattening sequences of sequences in reverse order is distributive over concatentation. 
/// That is, concatenating the flattening of two sequences of sequences in reverse 
/// order is the same as flattening the concatenation of two sequences of sequences
/// in reverse order.
pub proof fn lemma_flatten_reverse_concat<A>(x: Seq<Seq<A>>, y: Seq<Seq<A>>)
    ensures 
        (x+y).flatten_reverse() =~= x.flatten_reverse() + y.flatten_reverse()
    decreases 
        y.len()
{
    if y.len() == 0 {
        assert(y.flatten_reverse() == Seq::<A>::empty());
        assert(x+y =~= x);
    } else {
        // the original dafny uses a calculational proof, we might want to update
        // the calc! macro to support extensional equality
        // calc!{
        //     (=~=)
        //     (x+y).flatten_reverse;    // 1
        //     { assert((x+y).last() == y.last()); assert((x+y).drop_last() =~= x + y.drop_last()); }
        //     (x + y.drop_last()).flatten_reverse() + y.last();   // 2
        //     { }
        //     x.flatten_reverse() + y.drop_last().flatten_reverse() + y.last();   // 3
        //     { }
        //     x.flatten_reverse() + y.flatten_reverse();   // 4
        //     }
        assert((x+y).last() == y.last());
        assert((x+y).drop_last() =~= x + y.drop_last()); // OBSERVE
        // step 1 - 2
        assert((x+y).flatten_reverse() =~= (x + y.drop_last()).flatten_reverse() + y.last());
        // step 2 - 3
        assert((x + y.drop_last()).flatten_reverse() + y.last() =~= x.flatten_reverse() + y.drop_last().flatten_reverse() + y.last()) by {
            lemma_flatten_reverse_concat(x, y.drop_last());
        } // OBSERVE
        // step 3 - 4
        assert(y.drop_last().flatten_reverse() + y.last() =~= y.flatten_reverse());
        assert(x.flatten_reverse() + y.drop_last().flatten_reverse() + y.last() 
                =~= x.flatten_reverse() + y.flatten_reverse());
    }
}

/// Flattening a sequence of a sequence x, where x has length 1, 
/// results in a sequence equivalent to the single element of x
pub proof fn lemma_flatten_one_element<A>(x: Seq<Seq<A>>)
    ensures
        x.len() == 1 ==> x.flatten() == x.first(),
{
    if x.len() == 1
    {
        assert(x.flatten() =~= x.first().add(x.drop_first().flatten()));
    }
}

/// The length of a flattened sequence of sequences x is greater than or 
/// equal to any of the lengths of the elements of x.
pub proof fn lemma_flatten_length_ge_single_element_length<A>(x: Seq<Seq<A>>, i: int)
    requires
        0<= i < x.len(),
    ensures
        x.flatten_reverse().len() >= x[i].len()
    decreases
        x.len()
{
    if x.len() == 1 {
        lemma_flatten_one_element(x);
        lemma_flatten_and_flatten_reverse_are_equivalent(x);
    }
    else if i < x.len() -1 {
        lemma_flatten_length_ge_single_element_length(x.drop_last(), i);
    } else {
        assert(x.flatten_reverse() == x.drop_last().flatten_reverse().add(x.last()));
    }
}

/// The length of a flattened sequence of sequences x is less than or equal 
/// to the length of x multiplied by a number greater than or equal to the
/// length of the longest sequence in x.
pub proof fn lemma_flatten_length_le_mul<A>(x: Seq<Seq<A>>, j: int)
    requires
        forall |i: int| 0 <= i < x.len() ==> (#[trigger] x[i]).len() <= j,
    ensures
        x.flatten_reverse().len() <= x.len() * j,
    decreases
        x.len(),
{
    if x.len() == 0 {}
    else {
        lemma_flatten_length_le_mul(x.drop_last(), j);
        assert(x.drop_last().flatten_reverse().len() <= (x.len() -1) *j);
    }
}

/// Flattening sequences of sequences in order (starting from the beginning)
/// and in reverse order (starting from the end) results in the same sequence.
pub proof fn lemma_flatten_and_flatten_reverse_are_equivalent<A>(x: Seq<Seq<A>>)
    ensures
        x.flatten() == x.flatten_reverse(),
    decreases
        x.len(),
{
    if x.len() == 0 {}
    else {
        lemma_flatten_and_flatten_reverse_are_equivalent(x.drop_last());
        lemma_flatten_one_element(seq![x.last()]);
        lemma_flatten_concat(x.drop_last(), seq![x.last()]);
        assert(x =~= x.drop_last().push(x.last()));
    }
}



#[doc(hidden)]
#[verifier(inline)]
pub open spec fn check_argument_is_seq<A>(s: Seq<A>) -> Seq<A> { s }

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
        ::builtin_macros::verus_proof_macro_exprs!($crate::seq_lib::assert_seqs_equal_internal!($($tail)*))
    };
}

#[macro_export]
#[doc(hidden)]
macro_rules! assert_seqs_equal_internal {
    (::builtin::spec_eq($s1:expr, $s2:expr)) => {
        assert_seqs_equal_internal!($s1, $s2)
    };
    (::builtin::spec_eq($s1:expr, $s2:expr), $idx:ident => $bblock:block) => {
        assert_seqs_equal_internal!($s1, $s2, $idx => $bblock)
    };
    ($s1:expr, $s2:expr $(,)?) => {
        assert_seqs_equal_internal!($s1, $s2, idx => { })
    };
    ($s1:expr, $s2:expr, $idx:ident => $bblock:block) => {
        #[verifier::spec] let s1 = $crate::seq_lib::check_argument_is_seq($s1);
        #[verifier::spec] let s2 = $crate::seq_lib::check_argument_is_seq($s2);
        ::builtin::assert_by(::builtin::equal(s1, s2), {
            ::builtin::assert_(s1.len() == s2.len());
            ::builtin::assert_forall_by(|$idx : ::builtin::int| {
                ::builtin::requires(::builtin_macros::verus_proof_expr!(0 <= $idx && $idx < s1.len()));
                ::builtin::ensures(::builtin::equal(s1.index($idx), s2.index($idx)));
                { $bblock }
            });
            ::builtin::assert_(::builtin::ext_equal(s1, s2));
        });
    }
}

#[doc(hidden)]
pub use assert_seqs_equal_internal;
pub use assert_seqs_equal;

} // verus!
