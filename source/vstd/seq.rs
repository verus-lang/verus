use core::marker;

#[allow(unused_imports)]
use super::pervasive::*;
#[allow(unused_imports)]
use super::prelude::*;

verus! {

#[verifier::ext_equal]
#[verifier::accept_recursive_types(A)]
enum SeqInner<A> {
    Nil,
    Cons { head: A, tail: Box<SeqInner<A>> },
}

// This indirection is required to show the termination of `Seq::len`
//
// If we translated this to `Seq` we the decrease clauses wouldn't work,
// because we would have had to re-internalize the tail into a `Seq`
impl<A> SeqInner<A> {
    spec fn len(self) -> nat
        decreases self,
    {
        match self {
            SeqInner::Nil => 0,
            SeqInner::Cons { tail, .. } => { 1 + tail.len() },
        }
    }

    spec fn index(self, i: int) -> A
        recommends
            0 <= i < self.len(),
        decreases self.len(),
    {
        match self {
            SeqInner::Nil => arbitrary(),
            SeqInner::Cons { head, tail } => if i == 0 {
                head
            } else {
                tail.index(i - 1)
            },
        }
    }

    #[verifier::inline]
    spec fn spec_index(self, i: int) -> A
        recommends
            0 <= i < self.len(),
    {
        self.index(i)
    }

    spec fn push(self, a: A) -> SeqInner<A>
        decreases self.len(),
    {
        match self {
            SeqInner::Nil => SeqInner::Cons { head: a, tail: Box::new(SeqInner::Nil) },
            SeqInner::Cons { head, tail } => {
                let new_tail = tail.push(a);
                SeqInner::Cons { head, tail: Box::new(new_tail) }
            },
        }
    }

    spec fn update(self, i: int, a: A) -> SeqInner<A>
        recommends
            0 <= i < self.len(),
        decreases self.len(),
    {
        match self {
            SeqInner::Nil => arbitrary(),
            SeqInner::Cons { head, tail } => if i == 0 {
                SeqInner::Cons { head: a, tail }
            } else {
                let new_tail = tail.update(i - 1, a);
                SeqInner::Cons { head, tail: Box::new(new_tail) }
            },
        }
    }

    spec fn subrange(self, start_inclusive: int, end_exclusive: int) -> SeqInner<A>
        recommends
            0 <= start_inclusive <= end_exclusive <= self.len(),
        decreases start_inclusive, end_exclusive - start_inclusive,
    {
        match self {
            SeqInner::Nil => SeqInner::Nil,
            SeqInner::Cons {
                head,
                tail,
            } =>
            // skip elements until start_inclusive becomes 0
            if start_inclusive > 0 {
                tail.subrange(start_inclusive - 1, end_exclusive - 1)
            } else {
                if end_exclusive <= 0 {
                    SeqInner::Nil
                } else {
                    let new_tail = tail.subrange(start_inclusive, end_exclusive - 1);
                    SeqInner::Cons { head, tail: Box::new(new_tail) }
                }
            },
        }
    }

    spec fn add(self, rhs: SeqInner<A>) -> SeqInner<A>
        decreases self.len(),
    {
        match self {
            SeqInner::Nil => rhs,
            SeqInner::Cons { head, tail } => {
                let new_tail = tail.add(rhs);
                SeqInner::Cons { head, tail: Box::new(new_tail) }
            },
        }
    }
}

/// `Seq<A>` is a sequence type for specifications.
/// To use a "sequence" in compiled code, use an `exec` type like `vec::Vec`
/// that has `Seq<A>` as its specification type.
///
/// An object `seq: Seq<A>` has a length, given by [`seq.len()`](Seq::len),
/// and a value at each `i` for `0 <= i < seq.len()`, given by [`seq[i]`](Seq::index).
///
/// Sequences can be constructed in a few different ways:
///  * [`Seq::empty`] construct an empty sequence (`len() == 0`)
///  * [`Seq::new`] construct a sequence of a given length, initialized according
///     to a given function mapping indices `i` to values `A`.
///  * The [`seq!`] macro, to construct small sequences of a fixed size (analagous to the
///     [`std::vec!`] macro).
///  * By manipulating an existing sequence with [`Seq::push`], [`Seq::update`],
///    or [`Seq::add`].
///
/// To prove that two sequences are equal, it is usually easiest to use the
/// extensional equality operator `=~=`.
#[verifier::ext_equal]
#[verifier::accept_recursive_types(A)]
pub tracked struct Seq<A> {
    inner: SeqInner<A>,
}

impl<A> Seq<A> {
    /// An empty sequence (i.e., a sequence of length 0).
    #[rustc_diagnostic_item = "verus::vstd::seq::Seq::empty"]
    pub closed spec fn empty() -> Seq<A> {
        Seq { inner: SeqInner::Nil }
    }

    /// Construct a sequence `s` of length `len` where entry `s[i]` is given by `f(i)`.
    #[rustc_diagnostic_item = "verus::vstd::seq::Seq::new"]
    pub closed spec fn new(len: nat, f: spec_fn(int) -> A) -> Seq<A>
        decreases len,
    {
        if len == 0 {
            Seq { inner: SeqInner::Nil }
        } else {
            Self::new((len - 1) as nat, f).push(f(len - 1))
        }
    }

    /// The length of a sequence.
    #[rustc_diagnostic_item = "verus::vstd::seq::Seq::len"]
    pub closed spec fn len(self) -> nat {
        self.inner.len()
    }

    /// Gets the value at the given index `i`.
    ///
    /// If `i` is not in the range `[0, self.len())`, then the resulting value
    /// is meaningless and arbitrary.
    #[rustc_diagnostic_item = "verus::vstd::seq::Seq::index"]
    pub closed spec fn index(self, i: int) -> A
        recommends
            0 <= i < self.len(),
    {
        self.inner.index(i)
    }

    /// `[]` operator, synonymous with `index`
    #[verifier::inline]
    pub open spec fn spec_index(self, i: int) -> A
        recommends
            0 <= i < self.len(),
    {
        self.index(i)
    }

    /// Appends the value `a` to the end of the sequence.
    /// This always increases the length of the sequence by 1.
    /// This often requires annotating the type of the element literal in the sequence,
    /// e.g., `10int`.
    ///
    /// ## Example
    ///
    /// ```rust
    /// proof fn push_test() {
    ///     assert(seq![10int, 11, 12].push(13) =~= seq![10, 11, 12, 13]);
    /// }
    /// ```
    #[rustc_diagnostic_item = "verus::vstd::seq::Seq::push"]
    pub closed spec fn push(self, a: A) -> Seq<A> {
        Seq { inner: self.inner.push(a) }
    }

    /// Updates the sequence at the given index, replacing the element with the given
    /// value, and leaves all other entries unchanged.
    ///
    /// ## Example
    ///
    /// ```rust
    /// proof fn update_test() {
    ///     let s = seq![10, 11, 12, 13, 14];
    ///     let t = s.update(2, -5);
    ///     assert(t =~= seq![10, 11, -5, 13, 14]);
    /// }
    /// ```
    #[rustc_diagnostic_item = "verus::vstd::seq::Seq::update"]
    pub closed spec fn update(self, i: int, a: A) -> Seq<A>
        recommends
            0 <= i < self.len(),
    {
        Seq { inner: self.inner.update(i, a) }
    }

    /// Returns a sequence for the given subrange.
    ///
    /// ## Example
    ///
    /// ```rust
    /// proof fn subrange_test() {
    ///     let s = seq![10int, 11, 12, 13, 14];
    ///     //                      ^-------^
    ///     //           0      1   2   3   4   5
    ///     let sub = s.subrange(2, 4);
    ///     assert(sub =~= seq![12, 13]);
    /// }
    /// ```
    #[rustc_diagnostic_item = "verus::vstd::seq::Seq::subrange"]
    pub closed spec fn subrange(self, start_inclusive: int, end_exclusive: int) -> Seq<A>
        recommends
            0 <= start_inclusive <= end_exclusive <= self.len(),
    {
        Seq { inner: self.inner.subrange(start_inclusive, end_exclusive) }
    }

    /// Returns a sequence containing only the first n elements of the original sequence
    #[verifier::inline]
    pub open spec fn take(self, n: int) -> Seq<A> {
        self.subrange(0, n)
    }

    /// Returns a sequence without the first n elements of the original sequence
    #[verifier::inline]
    pub open spec fn skip(self, n: int) -> Seq<A> {
        self.subrange(n, self.len() as int)
    }

    /// Concatenates the sequences.
    ///
    /// ## Example
    ///
    /// ```rust
    /// proof fn add_test() {
    ///     assert(seq![10int, 11].add(seq![12, 13, 14])
    ///             =~= seq![10, 11, 12, 13, 14]);
    /// }
    /// ```
    #[rustc_diagnostic_item = "verus::vstd::seq::Seq::add"]
    pub closed spec fn add(self, rhs: Seq<A>) -> Seq<A> {
        Seq { inner: self.inner.add(rhs.inner) }
    }

    /// `+` operator, synonymous with `add`
    #[verifier::inline]
    pub open spec fn spec_add(self, rhs: Seq<A>) -> Seq<A> {
        self.add(rhs)
    }

    /// Returns the last element of the sequence.
    #[rustc_diagnostic_item = "verus::vstd::seq::Seq::last"]
    pub open spec fn last(self) -> A
        recommends
            0 < self.len(),
    {
        self[self.len() as int - 1]
    }

    /// Returns the first element of the sequence.
    #[rustc_diagnostic_item = "vstd::seq::Seq::first"]
    pub open spec fn first(self) -> A
        recommends
            0 < self.len(),
    {
        self[0]
    }

    #[verifier(external_body)]
    pub proof fn tracked_empty() -> (tracked ret: Self)
        ensures
            ret == Seq::empty(),
    {
        unimplemented!()
    }

    #[verifier(external_body)]
    pub proof fn tracked_remove(tracked &mut self, i: int) -> (tracked ret: A)
        requires
            0 <= i < old(self).len(),
        ensures
            ret == old(self)[i],
            final(self).len() == old(self).len() - 1,
            *final(self) == old(self).remove(i),
    {
        unimplemented!()
    }

    #[verifier(external_body)]
    pub proof fn tracked_insert(tracked &mut self, i: int, tracked v: A)
        requires
            0 <= i <= old(self).len(),
        ensures
            final(self).len() == old(self).len() + 1,
            *final(self) == old(self).insert(i, v),
    {
        unimplemented!()
    }

    #[verifier(external_body)]
    pub proof fn tracked_borrow(tracked &self, i: int) -> (tracked ret: &A)
        requires
            0 <= i < self.len(),
        ensures
            *ret == self[i],
    {
        unimplemented!()
    }

    pub proof fn tracked_push(tracked &mut self, tracked v: A)
        ensures
            *final(self) == old(self).push(v),
            final(self).len() == old(self).len() + 1,
    {
        broadcast use group_seq_axioms;

        assert(self.insert(self.len() as int, v) =~= self.push(v));
        self.tracked_insert(self.len() as int, v);
    }

    pub proof fn tracked_pop(tracked &mut self) -> (tracked ret: A)
        requires
            old(self).len() > 0,
        ensures
            ret == old(self).last(),
            final(self).len() == old(self).len() - 1,
            *final(self) == old(self).take(old(self).len() - 1),
    {
        broadcast use group_seq_axioms;

        assert(self.remove(self.len() - 1) =~= self.take(self.len() - 1));
        self.tracked_remove(self.len() - 1)
    }

    pub proof fn tracked_pop_front(tracked &mut self) -> (tracked ret: A)
        requires
            old(self).len() > 0,
        ensures
            ret == old(self).first(),
            final(self).len() == old(self).len() - 1,
            *final(self) == old(self).drop_first(),
    {
        broadcast use group_seq_axioms;

        assert(self.remove(0) =~= self.drop_first());
        self.tracked_remove(0)
    }
}

proof fn lemma_seq_inner_index_decreases<A>(s: SeqInner<A>, i: int)
    requires
        0 <= i < s.len(),
    ensures
        (decreases_to!(s => s[i])),
    decreases i,
{
    match s {
        SeqInner::Nil => {
            assert(s.len() == 0);
            assert(false);
        },
        SeqInner::Cons { head, tail } => {
            if i == 0 {
                assert(decreases_to!(s => s[i]));
            } else {
                assert(tail[i - 1] == s[i]);
                lemma_seq_inner_index_decreases(*tail, i - 1);
                assert(decreases_to!(s => *tail));
                assert(decreases_to!(*tail => tail[i-1]));
            }
        },
    }
}

pub broadcast proof fn axiom_seq_index_decreases<A>(s: Seq<A>, i: int)
    requires
        0 <= i < s.len(),
    ensures
        #[trigger] (decreases_to!(s => s[i])),
{
    lemma_seq_inner_index_decreases(s.inner, i)
}

// TODO: this should be provable
pub axiom fn axiom_seq_len_decreases<A>(s1: Seq<A>, s2: Seq<A>)
    requires
        s2.len() < s1.len(),
        forall|i2: int|
            0 <= i2 < s2.len() && #[trigger] trigger(s2[i2]) ==> exists|i1: int|
                0 <= i1 < s1.len() && s1[i1] == s2[i2],
    ensures
        decreases_to!(s1 => s2),
;

pub broadcast proof fn axiom_seq_subrange_decreases<A>(s: Seq<A>, i: int, j: int)
    requires
        0 <= i <= j <= s.len(),
        s.subrange(i, j).len() < s.len(),
    ensures
        #[trigger] (decreases_to!(s => s.subrange(i, j))),
{
    broadcast use {axiom_seq_subrange_len, axiom_seq_subrange_index};

    let s2 = s.subrange(i, j);
    assert forall|i2: int| 0 <= i2 < s2.len() && #[trigger] trigger(s2[i2]) implies exists|i1: int|
        0 <= i1 < s.len() && s[i1] == s2[i2] by {
        assert(s[i + i2] == s2[i2]);
    }
    axiom_seq_len_decreases(s, s2);
}

pub broadcast proof fn axiom_seq_empty<A>()
    ensures
        #[trigger] Seq::<A>::empty().len() == 0,
{
    let s = Seq::<A>::empty();
    match s.inner {
        SeqInner::Nil => {
            assert(s == Seq { inner: SeqInner::Nil });
        },
        SeqInner::Cons { tail, .. } => {
            let seq_tail = Seq { inner: *tail };
            assert(s.len() == 1 + seq_tail.len());
            assert(s.len() > 0);
        },
    }
}

pub broadcast proof fn axiom_seq_new_len<A>(len: nat, f: spec_fn(int) -> A)
    ensures
        #[trigger] Seq::new(len, f).len() == len,
    decreases len,
{
    let s = Seq::new(len, f);
    if len == 0 {
        assert(s.len() == 0);
    } else {
        broadcast use axiom_seq_push_len;

        let pref = Seq::new((len - 1) as nat, f);
        axiom_seq_new_len((len - 1) as nat, f);
        assert(pref.len() == (len - 1) as nat);

        let s2 = pref.push(f(len - 1));
        assert(s2.len() == pref.len() + 1);

        assert(s == s2);
        assert(s.len() == len);
    }
}

pub broadcast proof fn axiom_seq_new_index<A>(len: nat, f: spec_fn(int) -> A, i: int)
    requires
        0 <= i < len,
    ensures
        #[trigger] Seq::new(len, f)[i] == f(i),
    decreases len,
{
    broadcast use axiom_seq_new_len;

    let s = Seq::new(len, f);
    assert(s.len() == len);

    let pref = Seq::new((len - 1) as nat, f);
    assert(pref.len() == len - 1);

    let a = f(len - 1);
    assert(s == pref.push(a));

    if i == len - 1 {
        axiom_seq_push_index_same(pref, a, i);
        assert(s[i] == a);
    } else {
        assert(0 <= i < (len - 1));
        axiom_seq_new_index((len - 1) as nat, f, i);
        axiom_seq_push_index_different(pref, a, i);
    }
}

proof fn lemma_seq_inner_push_len<A>(s: SeqInner<A>, a: A)
    ensures
        s.push(a).len() == s.len() + 1,
    decreases s.len(),
{
    match s {
        SeqInner::Nil => {},
        SeqInner::Cons { tail, .. } => {
            lemma_seq_inner_push_len(*tail, a);
        },
    }
}

pub broadcast proof fn axiom_seq_push_len<A>(s: Seq<A>, a: A)
    ensures
        #[trigger] s.push(a).len() == s.len() + 1,
{
    lemma_seq_inner_push_len(s.inner, a)
}

proof fn lemma_seq_inner_push_index_same<A>(s: SeqInner<A>, a: A, i: int)
    requires
        i == s.len(),
    ensures
        #[trigger] s.push(a)[i] == a,
    decreases s,
{
    match s {
        SeqInner::Nil => {
            assert(s.push(a) == SeqInner::Cons { head: a, tail: Box::new(SeqInner::Nil) });
            assert(s.push(a)[0] == a);
        },
        SeqInner::Cons { tail, .. } => {
            lemma_seq_inner_push_index_same(*tail, a, i - 1);
        },
    }
}

pub broadcast proof fn axiom_seq_push_index_same<A>(s: Seq<A>, a: A, i: int)
    requires
        i == s.len(),
    ensures
        #[trigger] s.push(a)[i] == a,
{
    lemma_seq_inner_push_index_same(s.inner, a, i);
}

proof fn lemma_seq_inner_push_index_different<A>(s: SeqInner<A>, a: A, i: int)
    requires
        0 <= i < s.len(),
    ensures
        #[trigger] s.push(a)[i] == s[i],
    decreases s,
{
    match s {
        SeqInner::Nil => { assert(s.len() == 0) },
        SeqInner::Cons { tail, .. } => {
            if i == 0 {
            } else {
                lemma_seq_inner_push_index_different(*tail, a, i - 1);
            }
        },
    }
}

pub broadcast proof fn axiom_seq_push_index_different<A>(s: Seq<A>, a: A, i: int)
    requires
        0 <= i < s.len(),
    ensures
        #[trigger] s.push(a)[i] == s[i],
{
    lemma_seq_inner_push_index_different(s.inner, a, i);
}

// Expensive lemma; not in the default broadcast group
pub broadcast proof fn lemma_seq_push_index_different_alt<A>(s: Seq<A>, a: A, i: int)
    requires
        0 <= i < s.len(),
    ensures
        (#[trigger] s.push(a))[i] == #[trigger] s[i],
{
    broadcast use axiom_seq_push_index_different;

}

proof fn lemma_seq_inner_update_len<A>(s: SeqInner<A>, i: int, a: A)
    requires
        0 <= i < s.len(),
    ensures
        s.update(i, a).len() == s.len(),
    decreases i,
{
    let s_upd = s.update(i, a);
    match s {
        SeqInner::Nil => {},
        SeqInner::Cons { head, tail } => {
            match s_upd {
                SeqInner::Nil => {},
                SeqInner::Cons { head: head_upd, tail: tail_upd } => {
                    if i == 0 {
                        assert(head_upd == a);
                    } else {
                        lemma_seq_inner_update_len(*tail, (i - 1), a);
                    }
                },
            }
        },
    }
}

pub broadcast proof fn axiom_seq_update_len<A>(s: Seq<A>, i: int, a: A)
    requires
        0 <= i < s.len(),
    ensures
        #[trigger] s.update(i, a).len() == s.len(),
    decreases i,
{
    lemma_seq_inner_update_len(s.inner, i, a)
}

proof fn lemma_seq_inner_update_index_same<A>(s: SeqInner<A>, i: int, a: A)
    requires
        0 <= i < s.len(),
    ensures
        #[trigger] s.update(i, a)[i] == a,
    decreases s,
{
    match s {
        SeqInner::Nil => {},
        SeqInner::Cons { tail, .. } => {
            if i == 0 {
                assert(s.update(i, a)[i] == a)
            } else {
                lemma_seq_inner_update_index_same(*tail, i - 1, a);
            }
        },
    }
}

pub broadcast proof fn axiom_seq_update_same<A>(s: Seq<A>, i: int, a: A)
    requires
        0 <= i < s.len(),
    ensures
        #[trigger] s.update(i, a)[i] == a,
{
    lemma_seq_inner_update_index_same(s.inner, i, a);
}

// Expensive lemma; not in the default broadcast group
pub broadcast proof fn lemma_seq_update_same_alt<A>(s: Seq<A>, i: int, a: A)
    requires
        0 <= i < s.len(),
    ensures
        #![trigger s.update(i, a), s[i]]
        s.update(i, a)[i] == a,
{
    broadcast use axiom_seq_update_same;

}

proof fn lemma_seq_inner_update_index_different<A>(s: SeqInner<A>, i1: int, i2: int, a: A)
    requires
        0 <= i1 < s.len(),
        0 <= i2 < s.len(),
        i1 != i2,
    ensures
        #[trigger] s.update(i2, a)[i1] == s[i1],
    decreases s,
{
    match s {
        SeqInner::Nil => {},
        SeqInner::Cons { tail, .. } => {
            if i2 == 0 {
                assert(s.update(i2, a)[i1] == s[i1]);
            } else if i1 == 0 {
                assert(s.update(i2, a)[i1] == s[i1]);
            } else {
                lemma_seq_inner_update_index_different(*tail, i1 - 1, i2 - 1, a);
            }
        },
    }
}

pub broadcast proof fn axiom_seq_update_different<A>(s: Seq<A>, i1: int, i2: int, a: A)
    requires
        0 <= i1 < s.len(),
        0 <= i2 < s.len(),
        i1 != i2,
    ensures
        #[trigger] s.update(i2, a)[i1] == s[i1],
{
    lemma_seq_inner_update_index_different(s.inner, i1, i2, a);
}

// Expensive lemma; not in the default broadcast group
pub broadcast proof fn lemma_seq_update_different_alt<A>(s: Seq<A>, i1: int, i2: int, a: A)
    requires
        0 <= i1 < s.len(),
        0 <= i2 < s.len(),
        i1 != i2,
    ensures
        (#[trigger] s.update(i2, a))[i1] == #[trigger] s[i1],
{
    broadcast use axiom_seq_update_different;

}

pub broadcast proof fn axiom_seq_ext_equal<A>(s1: Seq<A>, s2: Seq<A>)
    ensures
        #[trigger] (s1 =~= s2) <==> {
            &&& s1.len() == s2.len()
            &&& forall|i: int| 0 <= i < s1.len() ==> s1[i] == s2[i]
        },
    decreases s1.len(),
{
    match s1.inner {
        SeqInner::Nil => {
            assert(s1.len() == s2.len() <==> s1 =~= s2);
        },
        SeqInner::Cons { head: head1, tail: tail1 } => {
            let seq_tail1 = Seq { inner: *tail1 };

            match s2.inner {
                SeqInner::Nil => {
                    assert(s1.len() != s2.len());
                },
                SeqInner::Cons { head: head2, tail: tail2 } => {
                    if head1 != head2 {
                        assert(s1[0] != s2[0]);
                    } else {
                        let seq_tail2 = Seq { inner: *tail2 };
                        axiom_seq_ext_equal(seq_tail1, seq_tail2);
                        if seq_tail1 =~= seq_tail2 {
                            assert(s1.len() == seq_tail1.len() + 1 == seq_tail2.len() + 1
                                == s2.len());
                            assert forall|i: int| 0 <= i < s1.len() implies s1[i] == s2[i] by {
                                if i == 0 {
                                    assert(s1[0] == s2[0]);
                                } else {
                                    assert(s1[i] == s2[i]);
                                }
                            }
                        } else if seq_tail1.len() == seq_tail2.len() {
                            assert(exists|i: int|
                                0 <= i < seq_tail1.len() && seq_tail1[i] != seq_tail2[i]);
                            let i = choose|i: int|
                                0 <= i < seq_tail1.len() && seq_tail1[i] != seq_tail2[i];
                            assert(s1[i + 1] != s2[i + 1]);
                        } else {
                            assert(s1.len() != s2.len());
                        }
                    }
                },
            }
        },
    }
}

pub broadcast proof fn axiom_seq_ext_equal_deep<A>(s1: Seq<A>, s2: Seq<A>)
    ensures
        #[trigger] (s1 =~~= s2) <==> {
            &&& s1.len() == s2.len()
            &&& forall|i: int| 0 <= i < s1.len() ==> s1[i] =~~= s2[i]
        },
{
    match s1.inner {
        SeqInner::Nil => {
            assert(s1.len() == s2.len() <==> s1 =~~= s2);
        },
        SeqInner::Cons { head: head1, tail: tail1 } => {
            let seq_tail1 = Seq { inner: *tail1 };

            match s2.inner {
                SeqInner::Nil => {
                    assert(s1.len() != s2.len());
                },
                SeqInner::Cons { head: head2, tail: tail2 } => {
                    if head1 != head2 {
                        assert(s1[0] != s2[0]);
                    } else {
                        let seq_tail2 = Seq { inner: *tail2 };
                        axiom_seq_ext_equal(seq_tail1, seq_tail2);
                        if seq_tail1 =~~= seq_tail2 {
                            assert(s1.len() == seq_tail1.len() + 1 == seq_tail2.len() + 1
                                == s2.len());
                            assert forall|i: int| 0 <= i < s1.len() implies s1[i] == s2[i] by {
                                if i == 0 {
                                    assert(s1[0] == s2[0]);
                                } else {
                                    assert(s1[i] == s2[i]);
                                }
                            }
                        } else if seq_tail1.len() == seq_tail2.len() {
                            assert(exists|i: int|
                                0 <= i < seq_tail1.len() && seq_tail1[i] != seq_tail2[i]);
                            let i = choose|i: int|
                                0 <= i < seq_tail1.len() && seq_tail1[i] != seq_tail2[i];
                            assert(s1[i + 1] != s2[i + 1]);
                        } else {
                            assert(s1.len() != s2.len());
                        }
                    }
                },
            }
        },
    }
}

proof fn lemma_seq_inner_subrange_len<A>(s: SeqInner<A>, j: int, k: int)
    requires
        0 <= j <= k <= s.len(),
    ensures
        s.subrange(j, k).len() == k - j,
    decreases j, k,
{
    match s {
        SeqInner::Nil => {},
        SeqInner::Cons { head, tail } => {
            if j > 0 {
                assert(s.subrange(j, k) == tail.subrange(j - 1, k - 1));
                lemma_seq_inner_subrange_len(*tail, j - 1, k - 1);
            } else if k > 0 {
                let new_tail = tail.subrange(j, k - 1);
                lemma_seq_inner_subrange_len(*tail, j, k - 1);
                assert(new_tail.len() == k - j - 1);
                let sub = SeqInner::Cons { head, tail: Box::new(new_tail) };
                assert(sub.len() == 1 + new_tail.len());
            } else {
                assert(j == k == 0);
                assert(s.subrange(j, k).len() == 0);
            }
        },
    }
}

pub broadcast proof fn axiom_seq_subrange_len<A>(s: Seq<A>, j: int, k: int)
    requires
        0 <= j <= k <= s.len(),
    ensures
        #[trigger] s.subrange(j, k).len() == k - j,
{
    lemma_seq_inner_subrange_len(s.inner, j, k)
}

proof fn lemma_seq_inner_subrange_index_aux<A>(s: SeqInner<A>, k: int, i: int)
    requires
        0 <= k <= s.len(),
        0 <= i < k,
    ensures
        s.subrange(0, k)[i] == s[i],
    decreases s,
{
    lemma_seq_inner_subrange_len(s, 0, k);
    // assert(s.subrange(0, k).len() == k);
    // assert(0 <= i < s.subrange(0, k).len());
    match s {
        SeqInner::Nil => {
            // assert(false);
        },
        SeqInner::Cons { head, tail } => {
            if i == 0 {
                // assert(s[0] == head);
                assert(s.subrange(0, k)[0] == head);
            } else {
                lemma_seq_inner_subrange_index_aux(*tail, k - 1, i - 1);
            }
        },
    }
}

proof fn lemma_seq_inner_subrange_index<A>(s: SeqInner<A>, j: int, k: int, i: int)
    requires
        0 <= j <= k <= s.len(),
        0 <= i < k - j,
    ensures
        s.subrange(j, k)[i] == s[i + j],
    decreases s,
{
    lemma_seq_inner_subrange_len(s, j, k);
    if j == 0 {
        lemma_seq_inner_subrange_index_aux(s, k, i);
    } else {
        match s {
            SeqInner::Nil => {
                assert(false);
            },
            SeqInner::Cons { head, tail } => {
                lemma_seq_inner_subrange_index(*tail, j - 1, k - 1, i);
            },
        }
    }
}

pub broadcast proof fn axiom_seq_subrange_index<A>(s: Seq<A>, j: int, k: int, i: int)
    requires
        0 <= j <= k <= s.len(),
        0 <= i < k - j,
    ensures
        #[trigger] s.subrange(j, k)[i] == s[i + j],
{
    lemma_seq_inner_subrange_index(s.inner, j, k, i);
}

// Expensive lemma; not in the default broadcast group
pub broadcast proof fn lemma_seq_subrange_index_alt<A>(s: Seq<A>, j: int, k: int, i: int)
    requires
        0 <= j <= k <= s.len(),
        0 <= i - j < k - j,
    ensures
        (#[trigger] s.subrange(j, k))[i - j] == #[trigger] s[i],
{
    broadcast use axiom_seq_subrange_index;

}

// Less expensive, more limited alternative to lemma_seq_subrange_index_alt
pub broadcast proof fn lemma_seq_two_subranges_index<A>(s: Seq<A>, j: int, k1: int, k2: int, i: int)
    requires
        0 <= j <= k1 <= s.len(),
        0 <= j <= k2 <= s.len(),
        0 <= i < k1 - j,
        0 <= i < k2 - j,
    ensures
        #[trigger] s.subrange(j, k1)[i] == (#[trigger] s.subrange(j, k2))[i],
{
    broadcast use axiom_seq_subrange_index;

}

proof fn lemma_seq_inner_add_len<A>(s1: SeqInner<A>, s2: SeqInner<A>)
    ensures
        s1.add(s2).len() == s1.len() + s2.len(),
    decreases s1.add(s2).len(),
{
    let sum = s1.add(s2);
    match s1 {
        SeqInner::Nil => {
            assert(sum == s2);
        },
        SeqInner::Cons { head, tail } => {
            let new_tail = tail.add(s2);
            lemma_seq_inner_add_len(*tail, s2);
            assert(new_tail.len() == (s1.len() - 1) + s2.len());
            assert(sum.len() == 1 + new_tail.len());
        },
    }
}

pub broadcast proof fn axiom_seq_add_len<A>(s1: Seq<A>, s2: Seq<A>)
    ensures
        #[trigger] s1.add(s2).len() == s1.len() + s2.len(),
{
    lemma_seq_inner_add_len(s1.inner, s2.inner);
}

proof fn lemma_seq_inner_add_index1<A>(s1: SeqInner<A>, s2: SeqInner<A>, i: int)
    requires
        0 <= i < s1.len(),
    ensures
        s1.add(s2)[i] == s1[i],
    decreases s1,
{
    match s1 {
        SeqInner::Nil => {
            assert(false);
        },
        SeqInner::Cons { head, tail } => {
            if i == 0 {
                assert(s1[i] == s1.add(s2)[i]);
            } else {
                lemma_seq_inner_add_index1(*tail, s2, i - 1);
            }
        },
    }
}

pub broadcast proof fn axiom_seq_add_index1<A>(s1: Seq<A>, s2: Seq<A>, i: int)
    requires
        0 <= i < s1.len(),
    ensures
        #[trigger] s1.add(s2)[i] == s1[i],
{
    lemma_seq_inner_add_index1(s1.inner, s2.inner, i)
}

proof fn lemma_seq_inner_add_index2<A>(s1: SeqInner<A>, s2: SeqInner<A>, i: int)
    requires
        s1.len() <= i < s1.len() + s2.len(),
    ensures
        s1.add(s2)[i] == s2[i - s1.len()],
    decreases s1,
{
    match s1 {
        SeqInner::Nil => {
            assert(s1.add(s2) == s2);
        },
        SeqInner::Cons { head, tail } => {
            if i == 0 {
                assert(false);
            } else {
                lemma_seq_inner_add_index2(*tail, s2, i - 1);
            }
        },
    }
}

pub broadcast proof fn axiom_seq_add_index2<A>(s1: Seq<A>, s2: Seq<A>, i: int)
    requires
        s1.len() <= i < s1.len() + s2.len(),
    ensures
        #[trigger] s1.add(s2)[i] == s2[i - s1.len()],
{
    lemma_seq_inner_add_index2(s1.inner, s2.inner, i);
}

// Expensive lemma; not in the default broadcast group
pub broadcast proof fn lemma_seq_add_index1_alt<A>(s1: Seq<A>, s2: Seq<A>, i: int)
    requires
        0 <= i < s1.len(),
    ensures
        (#[trigger] s1.add(s2))[i] == #[trigger] s1[i],
{
    broadcast use axiom_seq_add_index1;

}

// Expensive lemma; not in the default broadcast group
pub broadcast proof fn lemma_seq_add_index2_alt<A>(s1: Seq<A>, s2: Seq<A>, i: int)
    requires
        0 <= i < s2.len(),
    ensures
        (#[trigger] s1.add(s2))[i + s1.len()] == #[trigger] s2[i],
{
    broadcast use axiom_seq_add_index2;

}

pub broadcast group group_seq_axioms {
    axiom_seq_index_decreases,
    axiom_seq_subrange_decreases,
    axiom_seq_empty,
    axiom_seq_new_len,
    axiom_seq_new_index,
    axiom_seq_push_len,
    axiom_seq_push_index_same,
    axiom_seq_push_index_different,
    axiom_seq_update_len,
    axiom_seq_update_same,
    axiom_seq_update_different,
    axiom_seq_ext_equal,
    axiom_seq_ext_equal_deep,
    axiom_seq_subrange_len,
    axiom_seq_subrange_index,
    lemma_seq_two_subranges_index,
    axiom_seq_add_len,
    axiom_seq_add_index1,
    axiom_seq_add_index2,
}

// Expensive lemmas not in the default group (may slow down verification)
pub broadcast group group_seq_lemmas_expensive {
    lemma_seq_push_index_different_alt,
    lemma_seq_update_same_alt,
    lemma_seq_update_different_alt,
    lemma_seq_subrange_index_alt,
    lemma_seq_add_index1_alt,
    lemma_seq_add_index2_alt,
}

// ------------- Macros ---------------- //
#[doc(hidden)]
#[macro_export]
macro_rules! seq_internal {
    [] => {
        $crate::vstd::seq::Seq::empty()
    };
    [$elem:expr] => {
        $crate::vstd::seq::Seq::empty()
            .push($elem)
    };
    [$elem:expr,] => {
        $crate::vstd::seq::Seq::empty()
            .push($elem)
    };
    [$($elem:expr),* $(,)?] => {
        <_ as $crate::vstd::view::View>::view(&[$($elem),*])
    };
    [$elem:expr; $n:expr] => {
        $crate::vstd::seq::Seq::new(
            $n,
            $crate::vstd::prelude::closure_to_fn_spec(
                |_x: _| $elem
            ),
        )
    };
}

/// Creates a [`Seq`] containing the given elements.
///
/// ## Example
///
/// ```rust
/// let s = seq![11int, 12, 13];
///
/// assert(s.len() == 3);
/// assert(s[0] == 11);
/// assert(s[1] == 12);
/// assert(s[2] == 13);
/// ```
#[macro_export]
macro_rules! seq {
    [$($tail:tt)*] => {
        $crate::vstd::prelude::verus_proof_macro_exprs!($crate::vstd::seq::seq_internal!($($tail)*))
    };
}

#[doc(hidden)]
pub use seq_internal;
pub use seq;

} // verus!
