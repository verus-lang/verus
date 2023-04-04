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

verus! {

impl<A> Seq<A> {
    /// Applies the function `f` to each element of the sequence, and returns
    /// the resulting sequence.
    /// The `int` parameter of `f` is the index of the element being mapped.

    pub open spec fn map<B>(self, f: FnSpec(int, A) -> B) -> Seq<B> {
        Seq::new(self.len(), |i: int| f(i, self[i]))
    }

    pub closed spec fn filter(self, pred: FnSpec(A) -> bool) -> Self
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
                    let j = choose(|j| 0<=j<subseq.len() && subseq[j]==self[i]);
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
            self.filter(pred).len() <= self.len();

    proof fn filter_distributes_over_add(a:Self, b:Self, pred:FnSpec(A)->bool)
    ensures
        (a+b).filter(pred) == a.filter(pred) + b.filter(pred),
    decreases b.len()
    {
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

    // TODO is_sorted -- extract from summer_school e22
    pub open spec fn contains(self, needle: A) -> bool {
        exists|i: int| 0 <= i < self.len() && self[i] == needle
    }

    pub open spec fn index_of(self, needle: A) -> int {
        choose|i: int| 0 <= i < self.len() && self[i] == needle
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

    /// returns `true` if the sequequence has no duplicate elements
    pub open spec fn no_duplicates(self) -> bool {
        forall(|i, j| 0 <= i < self.len() && 0 <= j < self.len() && i != j
            ==> self[i] != self[j])
    }

    /// Returns `true` if two sequences are disjoint
    pub open spec fn disjoint(self, other: Self) -> bool {
        forall|i: int, j: int| 0 <= i < self.len() && 0 <= j < other.len() ==> self[i] != other[j]
    }

    /// Converts a sequence into a set
    pub open spec fn to_set(self) -> Set<A> {
        Set::new(|a: A| self.contains(a))
    }

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
}


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

        assert(seq.ext_equal(seq.drop_last().push(seq.last())));
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
    assert(seq.to_set().ext_equal(seq_to_set_rec(seq)));
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
            ::builtin::assert_(s1.ext_equal(s2));
        });
    }
}

#[doc(hidden)]
pub use assert_seqs_equal_internal;
pub use assert_seqs_equal;

} // verus!
