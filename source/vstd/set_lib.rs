#[allow(unused_imports)]
use super::multiset::Multiset;
#[allow(unused_imports)]
use super::pervasive::*;
use super::prelude::*;
#[allow(unused_imports)]
#[allow(unused_imports)]
use super::relations::*;
#[allow(unused_imports)]
use super::set::*;
#[allow(unused_imports)]
use super::gset::*;
#[allow(unused_imports)]
use super::iset::*;

verus! {

broadcast use {
    super::set::group_set_lemmas,
    GSet::congruent_infiniteness,
    GSet::congruent_len,
};

#[deprecated = "Use `Set::range` instead"]
#[verifier::inline]
pub open spec fn set_int_range(lo: int, hi: int) -> Set<int> {
    super::set::set_int_range(lo, hi)
}

pub trait SetLike<A> {
    type FiniteView: Finiteness;

    spec fn as_gset(self) -> GSet<A, Self::FiniteView>;
}

impl<A> SetLike<A> for Set<A> {
    type FiniteView = Finite;

    #[verifier::inline]
    open spec fn as_gset(self) -> GSet<A, Finite> {
        self.to_gset()
    }
}

impl<A> SetLike<A> for ISet<A> {
    type FiniteView = Infinite;

    #[verifier::inline]
    open spec fn as_gset(self) -> GSet<A, Infinite> {
        self.to_gset()
    }
}

impl<A, FINITE: Finiteness> SetLike<A> for GSet<A, FINITE> {
    type FiniteView = FINITE;

    #[verifier::inline]
    open spec fn as_gset(self) -> GSet<A, FINITE> {
        self
    }
}

//////////////////////////////////////////////////////////////////////////////
// Some general set properties
//////////////////////////////////////////////////////////////////////////////
impl<A, FINITE: Finiteness> GSet<A, FINITE> {
    /// Is `true` if called by a "full" set, i.e., a set containing every element of type `A`.
    pub open spec fn is_full(self) -> bool {
        self.to_infinite() == ISet::<A>::full().to_gset()
    }

    /// Is `true` if called by an "empty" set, i.e., a set containing no elements and has length 0
    pub open spec fn is_empty(self) -> (b: bool) {
        self =~= GSet::<A, FINITE>::empty()
    }

    /// Returns the set contains an element `f(x)` for every element `x` in `self`.
    pub open spec fn map<B>(self, f: spec_fn(A) -> B) -> Set<B> {
        Set::new(|a: B| exists|x: A| self.contains(x) && a == f(x))
    }

    /// `Set::map_by` is like `Set::map`, but `map` only takes a forward function `fwd: spec_fn(A) -> B`,
    /// while `map_by` also takes a reverse function `rev: spec_fn(B) -> A`
    /// such that `rev(fwd(a)) == a`.
    /// When `fwd` has such a reverse function, `Set::map_by` can make proofs easier
    /// by avoiding the "exists" that appears in lemmas about `Set::map`.
    /// Example: for a set `s: Set<int>`, to map each `i` in `s` to `(i, 10 * i)`,
    /// we can write either `s.map(|i: int| (i, 10 * i))`
    /// or `s.map_by(|i: int| (i, 10 * i), |p: (int, int)| p.0)`;
    /// the version with `map_by` is usually easier to use in proofs.
    /// If the recommendation `forall|a: A| self.contains(a) ==> rev(fwd(a)) == a` is satisfied,
    /// it is trivially guaranteed that `self.map_by(fwd, rev) == self.map(fwd)`.
    /// Also see the `set_build!` macro for a convenient interface to `map_by`.
    pub open spec fn map_by<B>(self, fwd: spec_fn(A) -> B, rev: spec_fn(B) -> A) -> Set<B>
        recommends
            forall|a: A| self.contains(a) ==> rev(fwd(a)) == a,
    {
        Set::new(|b: B| self.contains(rev(b)) && b == fwd(rev(b)))
    }

    /// Similar to `Set::map_by`, but the forward function returns `Set<B>` rather than `B`,
    /// and `map_flatten_by` flattens the final result from `Set<Set<B>>` to just `Set<B>`.
    /// This can be easier to work with in proofs than calling `map` and `flatten` separately,
    /// since `map` and `flatten` introduce "exists", while `map_flatten_by` does not.
    /// Also see the `set_build!` macro for a convenient interface to `map_flatten_by`.
    pub open spec fn map_flatten_by<B>(
        self,
        fwd: spec_fn(A) -> Set<B>,
        rev: spec_fn(B) -> A,
    ) -> Set<B>
        recommends
            forall|a: A, b: B| #[trigger]
                self.contains(a) && fwd(a).contains(b) ==> #[trigger] rev(b) == a,
    {
        Set::new(|b: B| self.contains(rev(b)) && fwd(rev(b)).contains(b))
    }

    pub proof fn map_flatten_by_is_map_flatten<B>(
        self,
        fwd: spec_fn(A) -> Set<B>,
        rev: spec_fn(B) -> A,
    )
        requires
            forall|a: A, b: B| #[trigger]
                self.contains(a) && fwd(a).contains(b) ==> #[trigger] rev(b) == a,
        ensures
            self.map_flatten_by(fwd, rev) == self.map(fwd).flatten(),
    {
        assert forall|b: B| self.map_flatten_by(fwd, rev).contains(b) implies #[trigger] self.map(
            fwd,
        ).flatten().contains(b) by {
            let bs = choose|bs: Set<B>|
                (exists|a: A| self.contains(a) && bs == fwd(a)) && bs.contains(b);
            assert(self.map(fwd).contains(bs) <==> (exists|a: A| self.contains(a) && bs == fwd(a)));
        }
    }

    /// Converts a set into a sequence with an arbitrary ordering.
    pub open spec fn to_seq(self) -> Seq<A>
        recommends
            self.finite(),
        decreases self.len(),
        when self.finite()
    {
        if self.len() == 0 {
            Seq::<A>::empty()
        } else {
            let x = self.choose();
            Seq::<A>::empty().push(x) + self.remove(x).to_seq()
        }
    }

    /// Converts a set into a sequence sorted by the given ordering function `leq`
    pub open spec fn to_sorted_seq(self, leq: spec_fn(A, A) -> bool) -> Seq<A> {
        self.to_seq().sort_by(leq)
    }

    /// A singleton set has at least one element and any two elements are equal.
    pub open spec fn is_singleton(self) -> bool {
        &&& self.len() > 0
        &&& (forall|x: A, y: A| self.contains(x) && self.contains(y) ==> x == y)
    }

    /// An element in an ordered set is called a least element (or a minimum), if it is less than
    /// or equal to every other element of the set.
    ///
    // change f to leq bc it is a relation. also these are an ordering relation
    pub open spec fn is_least(self, leq: spec_fn(A, A) -> bool, min: A) -> bool {
        self.contains(min) && forall|x: A| self.contains(x) ==> #[trigger] leq(min, x)
    }

    /// An element in an ordered set is called a minimal element, if no other element is less than it.
    pub open spec fn is_minimal(self, leq: spec_fn(A, A) -> bool, min: A) -> bool {
        self.contains(min) && forall|x: A|
            self.contains(x) && #[trigger] leq(x, min) ==> #[trigger] leq(min, x)
    }

    /// An element in an ordered set is called a greatest element (or a maximum), if it is greater than
    /// or equal to every other element of the set.
    pub open spec fn is_greatest(self, leq: spec_fn(A, A) -> bool, max: A) -> bool {
        self.contains(max) && forall|x: A| self.contains(x) ==> #[trigger] leq(x, max)
    }

    /// An element in an ordered set is called a maximal element, if no other element is greater than it.
    pub open spec fn is_maximal(self, leq: spec_fn(A, A) -> bool, max: A) -> bool {
        self.contains(max) && forall|x: A|
            self.contains(x) && #[trigger] leq(max, x) ==> #[trigger] leq(x, max)
    }

    /// Converts a set into a sequence with an arbitrary ordering.
    pub open spec fn to_seq(self) -> Seq<A>
        decreases self.len(),
        when self.finite()
    {
        if self.len() == 0 {
            Seq::<A>::empty()
        } else {
            let x = self.choose();
            proof {
                lemma_gset_choose_len(self);
                lemma_gset_remove_len(self, x);
            }
            Seq::<A>::empty().push(x) + self.remove(x).to_seq()
        }
    }
}

// Forwarding wrappers so GSet methods are available on Set<A> and ISet<A>
impl<A> Set<A> {
    #[verifier::inline]
    pub open spec fn is_full(self) -> bool { self.to_gset().is_full() }

    #[verifier::inline]
    pub open spec fn is_singleton(self) -> bool { self.to_gset().is_singleton() }

    #[verifier::inline]
    pub open spec fn is_least(self, leq: spec_fn(A, A) -> bool, min: A) -> bool {
        self.to_gset().is_least(leq, min)
    }

    #[verifier::inline]
    pub open spec fn is_minimal(self, leq: spec_fn(A, A) -> bool, min: A) -> bool {
        self.to_gset().is_minimal(leq, min)
    }

    #[verifier::inline]
    pub open spec fn is_greatest(self, leq: spec_fn(A, A) -> bool, max: A) -> bool {
        self.to_gset().is_greatest(leq, max)
    }

    #[verifier::inline]
    pub open spec fn is_maximal(self, leq: spec_fn(A, A) -> bool, max: A) -> bool {
        self.to_gset().is_maximal(leq, max)
    }

    #[verifier::inline]
    pub open spec fn to_seq(self) -> Seq<A> { self.to_gset().to_seq() }

    #[verifier::inline]
    pub open spec fn all(&self, pred: spec_fn(A) -> bool) -> bool { self.to_gset().all(pred) }

    #[verifier::inline]
    pub open spec fn any(&self, pred: spec_fn(A) -> bool) -> bool { self.to_gset().any(pred) }

    pub open spec fn apply_filter<B>(self, f: spec_fn(A) -> Option<B>) -> Set<Set<B>> {
        self.map(
            |elem: A|
                match f(elem) {
                    Option::Some(r) => Set::<B>::empty().insert(r),
                    Option::None => Set::<B>::empty(),
                },
        )
    }

    pub open spec fn filter_map<B>(self, f: spec_fn(A) -> Option<B>) -> Set<B> {
        self.apply_filter(f).flatten()
    }

    #[verifier::inline]
    pub open spec fn castable<NEWFINITE: Finiteness>(self) -> bool {
        self.to_gset().castable::<NEWFINITE>()
    }

    pub broadcast proof fn congruent_infiniteness<S2: SetLike<A>>(
        self,
        s2: S2,
    )
        requires
            #[trigger] self.to_gset().congruent(s2.as_gset()),
        ensures
            self.finite() <==> s2.as_gset().finite(),
    {
        self.to_gset().congruent_infiniteness(s2.as_gset());
    }

    pub broadcast proof fn congruent_len<S2: SetLike<A>>(
        self,
        s2: S2,
    )
        requires
            #[trigger] self.to_gset().congruent(s2.as_gset()),
            self.finite(),
        ensures
            self.len() == s2.as_gset().len(),
        decreases self.len(),
    {
        self.to_gset().congruent_len(s2.as_gset());
    }
}

impl<A> ISet<A> {
    #[verifier::inline]
    pub open spec fn is_full(self) -> bool { self.to_gset().is_full() }

    #[verifier::inline]
    pub open spec fn is_singleton(self) -> bool { self.to_gset().is_singleton() }

    #[verifier::inline]
    pub open spec fn is_least(self, leq: spec_fn(A, A) -> bool, min: A) -> bool {
        self.to_gset().is_least(leq, min)
    }

    #[verifier::inline]
    pub open spec fn is_minimal(self, leq: spec_fn(A, A) -> bool, min: A) -> bool {
        self.to_gset().is_minimal(leq, min)
    }

    #[verifier::inline]
    pub open spec fn is_greatest(self, leq: spec_fn(A, A) -> bool, max: A) -> bool {
        self.to_gset().is_greatest(leq, max)
    }

    #[verifier::inline]
    pub open spec fn is_maximal(self, leq: spec_fn(A, A) -> bool, max: A) -> bool {
        self.to_gset().is_maximal(leq, max)
    }

    #[verifier::inline]
    pub open spec fn to_seq(self) -> Seq<A> { self.to_gset().to_seq() }

    #[verifier::inline]
    pub open spec fn all(&self, pred: spec_fn(A) -> bool) -> bool { self.to_gset().all(pred) }

    #[verifier::inline]
    pub open spec fn any(&self, pred: spec_fn(A) -> bool) -> bool { self.to_gset().any(pred) }

    pub open spec fn apply_filter<B>(self, f: spec_fn(A) -> Option<B>) -> ISet<ISet<B>> {
        self.map(
            |elem: A|
                match f(elem) {
                    Option::Some(r) => ISet::<B>::empty().insert(r),
                    Option::None => ISet::<B>::empty(),
                },
        )
    }

    pub open spec fn filter_map<B>(self, f: spec_fn(A) -> Option<B>) -> ISet<B> {
        self.apply_filter(f).infinite_flatten()
    }

    #[verifier::inline]
    pub open spec fn castable<NEWFINITE: Finiteness>(self) -> bool {
        self.to_gset().castable::<NEWFINITE>()
    }

    pub broadcast proof fn congruent_infiniteness<S2: SetLike<A>>(
        self,
        s2: S2,
    )
        requires
            #[trigger] self.to_gset().congruent(s2.as_gset()),
        ensures
            self.finite() <==> s2.as_gset().finite(),
    {
        self.to_gset().congruent_infiniteness(s2.as_gset());
    }

    pub broadcast proof fn congruent_len<S2: SetLike<A>>(
        self,
        s2: S2,
    )
        requires
            #[trigger] self.to_gset().congruent(s2.as_gset()),
            self.finite(),
        ensures
            self.len() == s2.as_gset().len(),
        decreases self.len(),
    {
        self.to_gset().congruent_len(s2.as_gset());
    }
}

// Set<Set<A>> forwarding for nested set methods
impl<A> Set<Set<A>> {
    pub open spec fn deep_finite(self) -> bool {
        &&& self.finite()
        &&& forall|se| #![auto] self.contains(se) ==> se.finite()
    }

    pub open spec fn deep_castable<F2: Finiteness>(self) -> bool {
        self.deep_finite() || !F2::type_is_finite()
    }

    pub open spec fn to_infinite_deep(self) -> ISet<ISet<A>> {
        self.to_infinite().map(|e: Set<A>| e.to_infinite())
    }

    pub open spec fn flatten(self) -> Set<A> {
        self.to_infinite_deep().infinite_flatten().to_finite()
    }
}

impl<A> ISet<ISet<A>> {
    pub open spec fn deep_finite(self) -> bool {
        &&& self.finite()
        &&& forall|se| #![auto] self.contains(se) ==> se.finite()
    }

    pub open spec fn deep_castable<F2: Finiteness>(self) -> bool {
        self.deep_finite() || !F2::type_is_finite()
    }
}

//////////////////////////////////////////////////////////////////////////////
// FINITE set properties
//////////////////////////////////////////////////////////////////////////////
impl<A> Set<A> {
    /// Converts a set into a sequence sorted by the given ordering function `leq`
    pub open spec fn to_sorted_seq(self, leq: spec_fn(A, A) -> bool) -> Seq<A> {
        self.to_seq().sort_by(leq)
    }

    /// Any totally-ordered set contains a unique minimal (equivalently, least) element.
    /// Returns an arbitrary value if r is not a total ordering
    pub closed spec fn find_unique_minimal(self, r: spec_fn(A, A) -> bool) -> A
        recommends
            total_ordering(r),
            self.len() > 0,
        decreases self.len(),
        when self.finite()
    {
        proof {
            broadcast use group_set_properties;

        }
        if self.len() <= 1 {
            self.choose()
        } else {
            let x = self.choose();
            let min = self.remove(x).find_unique_minimal(r);
            if r(min, x) {
                min
            } else {
                x
            }
        }
    }

    /// Proof of correctness and expected behavior for `Set::find_unique_minimal`.
    pub proof fn find_unique_minimal_ensures(self, r: spec_fn(A, A) -> bool)
        requires
            self.len() > 0,
            total_ordering(r),
        ensures
            self.is_minimal(r, self.find_unique_minimal(r)) && (forall|min: A|
                self.is_minimal(r, min) ==> self.find_unique_minimal(r) == min),
        decreases self.len(),
    {
        broadcast use group_set_properties;
        reveal(Set::find_unique_minimal);

        if self.len() == 1 {
            lemma_set_choose_len(self);
            let x = self.choose();
            assert(self.contains(x));
            lemma_set_remove_insert(self, x);
            assert(self.find_unique_minimal(r) == x);
            assert forall|elt: A|
                self.contains(elt) && #[trigger] r(elt, self.find_unique_minimal(r)) implies #[trigger] r(
                    self.find_unique_minimal(r),
                    elt,
                ) by {
                if elt != x {
                    lemma_set_remove_different(self, elt, x);
                    assert(self.remove(x).contains(elt));
                    lemma_set_remove_len(self, x);
                    assert(self.remove(x).len() == 0);
                    lemma_set_contains_len(self.remove(x), elt);
                    assert(false);
                }
            }
            assert(self.is_minimal(r, self.find_unique_minimal(r)));
        } else {
            assert(self.len() > 1);
            let x = self.choose();
            assert(self.contains(x));
            self.remove(x).find_unique_minimal_ensures(r);
            assert(self.remove(x).is_minimal(r, self.remove(x).find_unique_minimal(r)));
            let y = self.remove(x).find_unique_minimal(r);
            assert(self.remove(x).contains(y));
            let min_updated = self.find_unique_minimal(r);
            assert(min_updated == if r(y, x) { y } else { x });
            assert(self.contains(min_updated));
            assert(!r(y, x) ==> min_updated == x);
            assert(forall|elt: A|
                self.remove(x).contains(elt) && #[trigger] r(elt, y) ==> #[trigger] r(y, elt));
            assert forall|elt: A|
                self.contains(elt) && #[trigger] r(elt, min_updated) implies #[trigger] r(
                min_updated,
                elt,
            ) by {
                assert(r(min_updated, x) || r(min_updated, y));
                if min_updated == y {  // Case where the new min is the old min
                    assert(self.is_minimal(r, self.find_unique_minimal(r)));
                } else {  //Case where the new min is the newest element
                    assert(self.remove(x).contains(elt) || elt == x);
                    assert(min_updated == x);
                    assert(r(x, y) || r(y, x));
                    assert(!r(x, y) || !r(y, x));
                    assert(!(min_updated == y) ==> !r(y, x));
                    assert(r(x, y));
                    if (self.remove(x).contains(elt)) {
                        assert(r(elt, y) && r(y, elt) ==> elt == y);
                    } else {
                    }
                }
            }
        }
        assert(self.is_minimal(r, self.find_unique_minimal(r)));
        assert forall|min_poss: A|
            self.is_minimal(r, min_poss) implies self.find_unique_minimal(r) == min_poss by {
            self.to_gset().lemma_minimal_is_unique(r);
        }
    }

    /// Any totally-ordered set contains a unique maximal (equivalently, greatest) element.
    /// Returns an arbitrary value if r is not a total ordering
    pub closed spec fn find_unique_maximal(self, r: spec_fn(A, A) -> bool) -> A
        recommends
            total_ordering(r),
            self.len() > 0,
        decreases self.len(),
        when self.finite()
    {
        proof {
            broadcast use group_set_properties;

        }
        if self.len() <= 1 {
            self.choose()
        } else {
            let x = self.choose();
            let max = self.remove(x).find_unique_maximal(r);
            if r(x, max) {
                max
            } else {
                x
            }
        }
    }

    /// Proof of correctness and expected behavior for `Set::find_unique_maximal`.
    pub proof fn find_unique_maximal_ensures(self, r: spec_fn(A, A) -> bool)
        requires
            self.len() > 0,
            total_ordering(r),
        ensures
            self.is_maximal(r, self.find_unique_maximal(r)) && (forall|max: A|
                self.is_maximal(r, max) ==> self.find_unique_maximal(r) == max),
        decreases self.len(),
    {
        broadcast use group_set_properties;
        reveal(Set::find_unique_maximal);

        if self.len() == 1 {
            lemma_set_choose_len(self);
            let x = self.choose();
            assert(self.remove(x) =~= Set::<A>::empty());
            assert(self.find_unique_maximal(r) == x);
            assert(self.contains(self.find_unique_maximal(r)));
            assert forall|elt: A|
                self.contains(elt) && #[trigger] r(self.find_unique_maximal(r), elt) implies #[trigger] r(
                    elt,
                    self.find_unique_maximal(r),
                ) by {
                if elt != x {
                    lemma_set_remove_different(self, elt, x);
                    assert(self.remove(x).contains(elt));
                    lemma_set_remove_len(self, x);
                    assert(self.remove(x).len() == 0);
                    lemma_set_contains_len(self.remove(x), elt);
                    assert(false);
                }
            }
        } else {
            assert(self.len() > 1);
            let x = self.choose();
            assert(self.contains(x));
            self.remove(x).find_unique_maximal_ensures(r);
            assert(self.remove(x).is_maximal(r, self.remove(x).find_unique_maximal(r)));
            lemma_set_remove_insert(self, x);
            let y = self.remove(x).find_unique_maximal(r);
            assert(self.remove(x).contains(y));
            let max_updated = self.find_unique_maximal(r);
            assert(max_updated == if r(x, y) { y } else { x });
            assert(self.contains(max_updated));
            assert(max_updated == x || max_updated == y);
            assert(!r(x, y) ==> max_updated == x);
            assert forall|elt: A|
                self.contains(elt) && #[trigger] r(max_updated, elt) implies #[trigger] r(
                elt,
                max_updated,
            ) by {
                assert(r(x, max_updated) || r(y, max_updated));
                if max_updated == y {  // Case where the new max is the old max
                    assert(r(elt, max_updated));
                    assert(r(x, max_updated));
                } else {  //Case where the new max is the newest element
                    assert(self.remove(x).contains(elt) || elt == x);
                    assert(max_updated == x);
                    assert(r(x, y) || r(y, x));
                    assert(!r(x, y) || !r(y, x));
                    assert(!(max_updated == y) ==> !r(x, y));
                    assert(r(y, x));
                    if (self.remove(x).contains(elt)) {
                        assert(r(y, elt) ==> r(elt, y));
                        assert(r(y, elt) && r(elt, y) ==> elt == y);
                        assert(r(elt, x));
                        assert(r(elt, max_updated))
                    } else {
                    }
                }
            }
        }
        assert(self.is_maximal(r, self.find_unique_maximal(r)));
        assert forall|max_poss: A|
            self.is_maximal(r, max_poss) implies self.find_unique_maximal(r) == max_poss by {
            self.to_gset().lemma_maximal_is_unique(r);
        }
    }

    /// Converts a set into a multiset where each element from the set has
    /// multiplicity 1 and any other element has multiplicity 0.
    // Multiset is restricted to finite, so this method is only available on finite Set.
    // (Honestly, it's weird to jonh that we have this method here; I'd rather see
    //     Multiset::from_set(foo)
    // than
    //     foo.to_multiset()
    // It makes more sense for Multiset to know how to construct itself from other types
    // than for every other type to know how to make multisets, doesn't it?)
    pub open spec fn to_multiset(self) -> Multiset<A>
        decreases self.len(),
        when self.finite()
    {
        if self.len() == 0 {
            Multiset::<A>::empty()
        } else {
            Multiset::<A>::empty().insert(self.choose()).add(
                self.remove(self.choose()).to_multiset(),
            )
        }
    }

    /// A finite set with length 0 is equivalent to the empty set.
    pub proof fn lemma_len0_is_empty(self)
        requires
            self.len() == 0,
        ensures
            self == Set::<A>::empty(),
    {
        if exists|a: A| self.contains(a) {
            // derive contradiction:
            assert(self.remove(self.choose()).len() + 1 == 0);
        }
        assert(self =~= Set::empty());
    }

    /// A singleton set has length 1.
    pub proof fn lemma_singleton_size(self)
        requires
            self.is_singleton(),
        ensures
            self.len() == 1,
    {
        broadcast use group_set_properties;

        assert(self.remove(self.choose()) =~= Set::empty());
    }

    /// A finite set has exactly one element, if and only if, it has at least one element and any two elements are equal.
    pub proof fn lemma_is_singleton(s: Set<A>)
        ensures
            s.is_singleton() == (s.len() == 1),
    {
        assert(s.is_singleton() ==> s.len() == 1) by {
            if s.is_singleton() {
                s.lemma_singleton_size();
            }
        };
        assert(s.len() == 1 ==> s.is_singleton()) by {
            if s.len() == 1 {
                let c = s.choose();
                lemma_set_choose_len(s);
                assert(s.contains(c));
                assert(s.len() > 0);
                lemma_set_remove_len(s, c);
                let r = s.remove(c);
                assert(r.len() == 0);
                r.lemma_len0_is_empty();
                assert forall|x: A, y: A| s.contains(x) && s.contains(y) implies x == y by {
                    if s.contains(x) && s.contains(y) {
                        if x != c {
                            lemma_set_remove_different(s, x, c);
                            assert(r.contains(x));
                            assert(Set::<A>::empty().contains(x));
                            assert(false);
                        }
                        if y != c {
                            lemma_set_remove_different(s, y, c);
                            assert(r.contains(y));
                            assert(Set::<A>::empty().contains(y));
                            assert(false);
                        }
                        assert(x == c);
                        assert(y == c);
                        assert(x == y);
                    }
                }
                assert forall|x: A, y: A| s.to_gset().contains(x) && s.to_gset().contains(y) implies x == y by {
                    assert(s.contains(x) == s.to_gset().contains(x));
                    assert(s.contains(y) == s.to_gset().contains(y));
                }
                assert(s.is_singleton());
            }
        };
        if s.len() == 1 {
            assert(s.contains(s.choose())) by {
                lemma_set_choose_len(s);
            }
        }
    }

    /// The result of filtering a finite set is finite and has size less than or equal to the original set.
    /// If you have an ISet inf that's finite and you'd like to use this property,
    /// let fin = inf.to_finite(); // requires inf.finite()
    /// fin.lemma_len_filter(f);   // proves fin.filter(f).len() <= fin.len()
    /// assert( inf.filter(f).equiv(fin.filter(f)) );   // spec fn giving extensionality analog
    /// across finite/infinite type variants
    /// assert( inf.filter(f).finite() );   // conclusion available from equiv
    /// assert( inf.filter(f).len() == fin.filter(f) );
    /// assert( fin.len() == inf.len() ); // we know this by to_finite
    pub proof fn lemma_len_filter(self, f: spec_fn(A) -> bool)
        ensures
            self.filter(f).finite(),
            self.filter(f).len() <= self.len(),
        decreases self.len(),
    {
        broadcast use {GSet::congruent_len};
        let x = self.to_gset();
        let fi = ISet::<A>::new(f).to_gset();
        lemma_set_filter_is_intersect(x, f);
        lemma_len_intersect(x, fi);
        reveal(Set::filter);
        lemma_set_to_from_gset(x.filter(f));
        assert(self.filter(f).to_gset() == x.filter(f));
        x.filter(f).congruent_len(x.generic_intersect(fi));
    }
}

//////////////////////////////////////////////////////////////////////////////
// Ordering properties (available on both flavors of set)
//////////////////////////////////////////////////////////////////////////////
impl<A, FINITE: Finiteness> GSet<A, FINITE> {
    /// In a pre-ordered set, a greatest element is necessarily maximal.
    pub proof fn lemma_greatest_implies_maximal(self, r: spec_fn(A, A) -> bool, max: A)
        requires
            pre_ordering(r),
        ensures
            self.is_greatest(r, max) ==> self.is_maximal(r, max),
    {
    }

    /// In a pre-ordered set, a least element is necessarily minimal.
    pub proof fn lemma_least_implies_minimal(self, r: spec_fn(A, A) -> bool, min: A)
        requires
            pre_ordering(r),
        ensures
            self.is_least(r, min) ==> self.is_minimal(r, min),
    {
    }

    /// In a totally-ordered set, an element is maximal if and only if it is a greatest element.
    pub proof fn lemma_maximal_equivalent_greatest(self, r: spec_fn(A, A) -> bool, max: A)
        requires
            total_ordering(r),
        ensures
            self.is_greatest(r, max) <==> self.is_maximal(r, max),
    {
        assert(self.is_maximal(r, max) ==> forall|x: A|
            !self.contains(x) || !r(max, x) || r(x, max));
    }

    /// In a totally-ordered set, an element is maximal if and only if it is a greatest element.
    pub proof fn lemma_minimal_equivalent_least(self, r: spec_fn(A, A) -> bool, min: A)
        requires
            total_ordering(r),
        ensures
            self.is_least(r, min) <==> self.is_minimal(r, min),
    {
        assert(self.is_minimal(r, min) ==> forall|x: A|
            !self.contains(x) || !r(x, min) || r(min, x));
    }

    /// In a partially-ordered set, there exists at most one least element.
    pub proof fn lemma_least_is_unique(self, r: spec_fn(A, A) -> bool)
        requires
            partial_ordering(r),
        ensures
            forall|min: A, min_prime: A|
                self.is_least(r, min) && self.is_least(r, min_prime) ==> min == min_prime,
    {
        assert forall|min: A, min_prime: A|
            self.is_least(r, min) && self.is_least(r, min_prime) implies min == min_prime by {
            assert(r(min, min_prime));
            assert(r(min_prime, min));
        }
    }

    /// In a partially-ordered set, there exists at most one greatest element.
    pub proof fn lemma_greatest_is_unique(self, r: spec_fn(A, A) -> bool)
        requires
            partial_ordering(r),
        ensures
            forall|max: A, max_prime: A|
                self.is_greatest(r, max) && self.is_greatest(r, max_prime) ==> max == max_prime,
    {
        assert forall|max: A, max_prime: A|
            self.is_greatest(r, max) && self.is_greatest(r, max_prime) implies max == max_prime by {
            assert(r(max_prime, max));
            assert(r(max, max_prime));
        }
    }

    /// In a totally-ordered set, there exists at most one minimal element.
    pub proof fn lemma_minimal_is_unique(self, r: spec_fn(A, A) -> bool)
        requires
            total_ordering(r),
        ensures
            forall|min: A, min_prime: A|
                self.is_minimal(r, min) && self.is_minimal(r, min_prime) ==> min == min_prime,
    {
        assert forall|min: A, min_prime: A|
            self.is_minimal(r, min) && self.is_minimal(r, min_prime) implies min == min_prime by {
            self.lemma_minimal_equivalent_least(r, min);
            self.lemma_minimal_equivalent_least(r, min_prime);
            self.lemma_least_is_unique(r);
        }
    }

    /// In a totally-ordered set, there exists at most one maximal element.
    pub proof fn lemma_maximal_is_unique(self, r: spec_fn(A, A) -> bool)
        requires
            self.finite(),
            total_ordering(r),
        ensures
            forall|max: A, max_prime: A|
                self.is_maximal(r, max) && self.is_maximal(r, max_prime) ==> max == max_prime,
    {
        assert forall|max: A, max_prime: A|
            self.is_maximal(r, max) && self.is_maximal(r, max_prime) implies max == max_prime by {
            self.lemma_maximal_equivalent_greatest(r, max);
            self.lemma_maximal_equivalent_greatest(r, max_prime);
            self.lemma_greatest_is_unique(r);
        }
    }

    /// Set difference with an additional element inserted decreases the size of
    /// the result. This can be useful for proving termination when traversing
    /// a set while tracking the elements that have already been handled.
    pub broadcast proof fn lemma_set_insert_diff_decreases(self, s: Set<A>, elt: A)
        requires
            self.contains(elt),
            !s.contains(elt),
            self.finite(),
        ensures
            #[trigger] self.generic_difference(s.to_gset().insert(elt)).len() < self.generic_difference(
                s.to_gset(),
            ).len(),
    {
        self.generic_difference(s.to_gset().insert(elt)).lemma_subset_not_in_lt(
            self.generic_difference(s.to_gset()),
            elt,
        );
    }

    // TODO(jonh): lemma_set_insert_diff_decreases trigger uses s.0 which is awkward for callers

    /// If there is an element not present in a subset, its length is stricly smaller.
    pub proof fn lemma_subset_not_in_lt(self: GSet<A, FINITE>, s2: GSet<A, FINITE>, elt: A)
        requires
            self.subset_of(s2),
            s2.finite(),
            !self.contains(elt),
            s2.contains(elt),
        ensures
            self.len() < s2.len(),
    {
        let s2_no_elt = s2.remove(elt);
        assert(self.subset_of(s2_no_elt)) by {
            assert forall|a: A| self.contains(a) implies s2_no_elt.contains(a) by {
                if a == elt {
                    assert(false);
                } else {
                    lemma_gset_remove_different(s2, a, elt);
                }
            }
        }
        assert(self.len() <= s2_no_elt.len()) by {
            lemma_len_subset(self, s2_no_elt);
        }
        lemma_gset_remove_len(s2, elt);
        assert(s2_no_elt.len() < s2.len());
    }

    /// Inserting an element and mapping a function over a set commute
    pub broadcast proof fn lemma_set_map_insert_commute<B>(self, elt: A, f: spec_fn(A) -> B)
        ensures
            #[trigger] self.insert(elt).map(f) =~= self.map(f).insert(f(elt)),
    {
        assert forall|x: B| self.map(f).insert(f(elt)).contains(x) implies self.insert(elt).map(
            f,
        ).contains(x) by {
            if x == f(elt) {
                assert(self.insert(elt).contains(elt));
            } else {
                let y = choose|y: A| self.contains(y) && f(y) == x;
                assert(self.insert(elt).contains(y));
            }
        }
    }

    /// `map` and `union` commute
    pub proof fn lemma_map_generic_union_commute<B>(self, t: GSet<A, FINITE>, f: spec_fn(A) -> B)
        ensures
            (self.generic_union(t)).map(f) =~= self.map(f).generic_union(t.map(f)),
    {
        broadcast use group_set_lemmas;

        let lhs = self.generic_union(t).map(f);
        let rhs = self.map(f).generic_union(t.map(f));

        assert forall|elem: B| rhs.contains(elem) implies lhs.contains(elem) by {
            if self.map(f).contains(elem) {
                let preimage = choose|preimage: A| self.contains(preimage) && f(preimage) == elem;
                assert(self.generic_union(t).contains(preimage));
            } else {
                assert(t.map(f).contains(elem));
                let preimage = choose|preimage: A| t.contains(preimage) && f(preimage) == elem;
                assert(self.generic_union(t).contains(preimage));
            }
        }
    }

    /// Utility function for more concise universal quantification over sets
    pub open spec fn all(&self, pred: spec_fn(A) -> bool) -> bool {
        forall|x: A| self.contains(x) ==> pred(x)
    }

    /// Utility function for more concise existential quantification over sets
    pub open spec fn any(&self, pred: spec_fn(A) -> bool) -> bool {
        exists|x: A| self.contains(x) && pred(x)
    }

    /// `any` is preserved between predicates `p` and `q` if `p` implies `q`.
    pub broadcast proof fn lemma_any_map_preserved_pred<B>(
        self,
        p: spec_fn(A) -> bool,
        q: spec_fn(B) -> bool,
        f: spec_fn(A) -> B,
    )
        requires
            #[trigger] self.any(p),
            forall|x: A| #[trigger] p(x) ==> q(f(x)),
        ensures
            #[trigger] self.map(f).any(q),
    {
        let x = choose|x: A| self.contains(x) && p(x);
        assert(self.map(f).contains(f(x)));
    }
}

impl<A, FINITE: Finiteness> GSet<GSet<A, FINITE>, FINITE> {
    pub open spec fn deep_finite(self) -> bool {
        &&& self.finite()
        &&& forall|se| #![auto] self.contains(se) ==> se.finite()
    }

    pub open spec fn deep_castable<F2: Finiteness>(self) -> bool {
        self.deep_finite() || !F2::type_is_finite()
    }
}

impl<A> ISet<A> {
    /// `map` and `union` commute
    pub proof fn lemma_map_union_commute<B>(self, t: ISet<A>, f: spec_fn(A) -> B)
        ensures
            (self.union(t)).map(f) =~= self.map(f).union(t.map(f)),
    {
        lemma_iset_map_contains(self.union(t), f);
        lemma_iset_map_contains(self, f);
        lemma_iset_map_contains(t, f);
        assert forall|y: B| self.union(t).map(f).contains(y) == self.map(f).union(t.map(f)).contains(y) by {
            lemma_iset_union(self.map(f), t.map(f), y);
            if self.union(t).map(f).contains(y) {
                let a = choose|a: A| self.union(t).contains(a) && f(a) == y;
                lemma_iset_union(self, t, a);
                if self.contains(a) {
                    assert(self.map(f).contains(y));
                } else {
                    assert(t.contains(a));
                    assert(t.map(f).contains(y));
                }
            }
            if self.map(f).union(t.map(f)).contains(y) {
                lemma_iset_union(self.map(f), t.map(f), y);
                if self.map(f).contains(y) {
                    let a = choose|a: A| self.contains(a) && f(a) == y;
                    lemma_iset_union(self, t, a);
                    assert(self.union(t).contains(a));
                } else {
                    assert(t.map(f).contains(y));
                    let a = choose|a: A| t.contains(a) && f(a) == y;
                    lemma_iset_union(self, t, a);
                    assert(self.union(t).contains(a));
                }
                assert(self.union(t).map(f).contains(y));
            }
        }
        lemma_iset_ext_equal(self.union(t).map(f), self.map(f).union(t.map(f)));
    }

    pub broadcast proof fn lemma_filter_map_union<B>(self, f: spec_fn(A) -> Option<B>, t: Self)
        ensures
            #[trigger] self.union(t).filter_map(f) == self.filter_map(f).union(t.filter_map(f)),
    {
        self.lemma_infinite_filter_map_union(f, t);
    }
}

// Define flatten and prove properties about it, for ISets specifically.  Later, we'll use
// Finiteness-castability lemmas to extend these definitions and lemmas to be generic over
// Finiteness.
impl<A> ISet<ISet<A>> {
    pub open spec fn infinite_flatten(self) -> ISet<A> {
        ISet::new(
            |elem|
                exists|elem_s: ISet<A>| #[trigger] self.contains(elem_s) && elem_s.contains(elem),
        )
    }

    pub proof fn infinite_flatten_preserves_finite_singleton(self)
        requires
            self.deep_finite(),
            self.len() == 1,
        ensures
            self.infinite_flatten().finite(),
    {
        self.infinite_flatten_preserves_finite();
    }

    pub proof fn infinite_flatten_preserves_finite(self)
        requires
            self.deep_finite(),
        ensures
            self.infinite_flatten().finite(),
        decreases self.len(),
    {
        if self != Self::empty() {
            let se = self.choose();
            assert(self.len() != 0) by {
                if self.len() == 0 {
                    lemma_iset_len_empty(self);
                    assert(self == Self::empty());
                    assert(false);
                }
            }
            assert(self.contains(se)) by {
                lemma_iset_choose_len(self);
            }
            assert(se.finite());
            lemma_iset_remove_len(self, se);
            let rself = self.remove(se);
            let singleton = ISet::empty().insert(se);
            lemma_set_insert_finite(ISet::<ISet<A>>::empty(), se);
            broadcast use lemma_iset_empty_len;
            assert(ISet::<ISet<A>>::empty().len() == 0);
            lemma_iset_insert_len(ISet::<ISet<A>>::empty(), se);
            assert(singleton.len() == 1);
            assert(singleton.deep_finite()) by {
                assert forall|sse: ISet<A>| singleton.contains(sse) implies sse.finite() by {
                    if sse != se {
                        lemma_iset_insert_different(ISet::<ISet<A>>::empty(), sse, se);
                        assert(ISet::<ISet<A>>::empty().contains(sse));
                        assert(false);
                    }
                }
            }
            assert forall|e: A| singleton.infinite_flatten().contains(e) == se.contains(e) by {
                if singleton.infinite_flatten().contains(e) {
                    let w = choose|w: ISet<A>| singleton.contains(w) && w.contains(e);
                    assert(w == se) by {
                        if w != se {
                            lemma_iset_insert_different(ISet::<ISet<A>>::empty(), w, se);
                            assert(ISet::<ISet<A>>::empty().contains(w));
                            assert(false);
                        }
                    }
                } else {
                    assert(singleton.contains(se));
                }
            }
            lemma_iset_ext_equal(singleton.infinite_flatten(), se);
            assert(rself.len() < self.len());
            rself.infinite_flatten_preserves_finite();
            assert(singleton.infinite_flatten() =~= se);
            lemma_set_union_finite(rself.infinite_flatten(), se);
            assert(rself.infinite_flatten().union(se).finite());
            rself.infinite_flatten_insert_union_commute(se);
            lemma_iset_remove_insert(self, se);
            assert(rself.insert(se) == self);
            assert(rself.insert(se).infinite_flatten() =~= self.infinite_flatten());
            assert(rself.infinite_flatten().union(se).congruent(self.infinite_flatten()));
            rself.infinite_flatten().union(se).0.congruent_infiniteness(self.infinite_flatten().0);
            assert(self.infinite_flatten().finite());
        } else {
            // the outer set is empty, so the flattened set is empty
            assert(self.infinite_flatten() =~= ISet::<A>::empty()) by {
                assert forall|a: A| self.infinite_flatten().contains(a) == ISet::<A>::empty().contains(a) by {
                    super::iset::lemma_iset_empty(a);
                    if self.infinite_flatten().contains(a) {
                        let s = choose|s: ISet<A>| self.contains(s) && s.contains(a);
                        assert(self.contains(s));
                        assert(false);
                    }
                }
                lemma_iset_ext_equal(self.infinite_flatten(), ISet::<A>::empty());
            }
        }
    }

    pub proof fn infinite_flatten_ensures<FINITE: Finiteness>(self)
        requires
            self.deep_castable::<FINITE>(),
        ensures
            self.infinite_flatten().castable::<FINITE>(),
    {
        // castable isn't strong enough. self can be a finite set of infinite sets;
        // that's castable (to a (finite) Set of ISet), but infinite_flatten won't
        // be finite, because of those inner ISets.
        // Hence deep_castable, a flatten-specific notion of castability.
        // If self is deep_finite, then infinite_flatten will be finite.
        if self.deep_finite() {
            self.infinite_flatten_preserves_finite();
        }
    }

    pub broadcast proof fn infinite_flatten_insert_union_commute(self, other: ISet<A>)
        ensures
            self.infinite_flatten().union(other) =~= #[trigger] self.insert(
                other,
            ).infinite_flatten(),
    {
        broadcast use group_set_lemmas;

        let lhs = self.infinite_flatten().union(other);
        let rhs = self.insert(other).infinite_flatten();
        lemma_iset_union_eq(self.infinite_flatten(), other);

        assert forall|elem: A| lhs.contains(elem) implies rhs.contains(elem) by {
            lemma_gset_generic_union(self.infinite_flatten().0, other.0, elem);
            if exists|s: ISet<A>| self.contains(s) && s.contains(elem) {
                let s = choose|s: ISet<A>| self.contains(s) && s.contains(elem);
                assert(self.insert(other).contains(s));
                assert(s.contains(elem));
            } else {
                assert(!self.infinite_flatten().contains(elem));
                assert(other.contains(elem));
                assert(self.insert(other).contains(other));
                assert(rhs.contains(elem));
            }
        }
        assert forall|elem: A| rhs.contains(elem) implies lhs.contains(elem) by {
            let s = choose|s: ISet<A>| self.insert(other).contains(s) && s.contains(elem);
            lemma_gset_generic_union(self.infinite_flatten().0, other.0, elem);
            if s == other {
                assert(other.contains(elem));
                assert(lhs.contains(elem));
            } else {
                lemma_iset_insert_different(self, s, other);
                assert(self.contains(s));
                assert(self.infinite_flatten().contains(elem));
                assert(lhs.contains(elem));
            }
        }
        assert forall|elem: A| lhs.contains(elem) == rhs.contains(elem) by {
            if lhs.contains(elem) {
            } else {
            }
        }
        lemma_iset_ext_equal(lhs, rhs);
    }
}

impl<A, FINITE: Finiteness> GSet<GSet<A, FINITE>, FINITE> {
    // Well, only two layers deep.
    pub open spec fn to_infinite_deep(self) -> GSet<GSet<A, Infinite>, Infinite> {
        self.to_infinite().map(|e: GSet<A, FINITE>| e.to_infinite())
    }

    pub open spec fn to_iset_deep(self) -> ISet<ISet<A>> {
        ISet::from_gset(self.to_infinite_deep().map(|e: GSet<A, Infinite>| ISet::from_gset(e)))
    }

    pub open spec fn flatten(self) -> GSet<A, FINITE> {
        self.to_iset_deep().infinite_flatten().to_gset().cast_finiteness::<FINITE>()
    }
}

impl<A, FINITE: Finiteness> GSet<A, FINITE> {
    pub open spec fn apply_filter<B>(self, f: spec_fn(A) -> Option<B>) -> GSet<
        GSet<B, FINITE>,
        FINITE,
    > {
        self.map(
            |elem: A|
                match f(elem) {
                    Option::Some(r) => GSet::empty().insert(r),
                    Option::None => GSet::empty(),
                },
        )
    }
}

// Prove it first in the infinite case
impl<A> ISet<A> {
    /// Collecting all elements `b` where `f` returns `Some(b)`
    pub open spec fn infinite_filter_map<B>(self, f: spec_fn(A) -> Option<B>) -> ISet<B> {
        self.apply_filter(f).infinite_flatten()
    }

    /// Inserting commutes with `infinite_filter_map`
    pub broadcast proof fn lemma_infinite_filter_map_insert<B>(
        s: ISet<A>,
        f: spec_fn(A) -> Option<B>,
        elem: A,
    )
        ensures
            #[trigger] s.insert(elem).infinite_filter_map(f) == (match f(elem) {
                Some(res) => s.infinite_filter_map(f).insert(res),
                None => s.infinite_filter_map(f),
            }),
    {
        broadcast use group_set_lemmas;
        broadcast use GSet::lemma_set_map_insert_commute;

        let lhs = s.insert(elem).infinite_filter_map(f);
        let rhs = match f(elem) {
            Some(res) => s.infinite_filter_map(f).insert(res),
            None => s.infinite_filter_map(f),
        };
        let to_set = |elem: A|
            match f(elem) {
                Option::Some(r) => iset!{r},
                Option::None => iset!{},
            };
        assert forall|r: B| #[trigger] lhs.contains(r) implies rhs.contains(r) by {
            if f(elem) != Some(r) {
                let orig = choose|orig: A| #[trigger]
                    s.insert(elem).contains(orig) && f(orig) == Option::Some(r);
                if orig == elem {
                    assert(f(elem) == Option::Some(r));
                    assert(false);
                }
                lemma_iset_insert_different(s, orig, elem);
                assert(s.contains(orig));
                assert(s.map(to_set).contains(to_set(orig)));
            }
        }
        assert forall|r: B| #[trigger] rhs.contains(r) implies lhs.contains(r) by {
            if Some(r) == f(elem) {
                assert(s.insert(elem).map(to_set).contains(to_set(elem)));
                assert(lhs.contains(r));
            } else {
                let orig = choose|orig: A| #[trigger]
                    s.contains(orig) && f(orig) == Option::Some(r);
                assert(s.insert(elem).map(to_set).contains(to_set(orig)));
            }
        }
        assert forall|r: B| lhs.contains(r) == rhs.contains(r) by {
            if lhs.contains(r) {
            } else {
            }
        }
        lemma_iset_ext_equal(lhs, rhs);
    }

    /// `infinite_filter_map` and `union` commute.
    pub broadcast proof fn lemma_infinite_filter_map_union<B>(
        self,
        f: spec_fn(A) -> Option<B>,
        t: ISet<A>,
    )
        ensures
            #[trigger] self.union(t).infinite_filter_map(f) == self.infinite_filter_map(f).union(
                t.infinite_filter_map(f),
            ),
    {
        let lhs = self.union(t).infinite_filter_map(f);
        let rhs = self.infinite_filter_map(f).union(t.infinite_filter_map(f));
        let to_set = |elem: A|
            match f(elem) {
                Option::Some(r) => iset!{r},
                Option::None => iset!{},
            };
        let to_fset = |elem: A|
            match f(elem) {
                Option::Some(r) => set!{r},
                Option::None => set!{},
            };

        assert forall|elem: B| rhs.contains(elem) implies lhs.contains(elem) by {
            if self.infinite_filter_map(f).contains(elem) {
                let x = choose|x: A| self.contains(x) && f(x) == Option::Some(elem);
                assert(self.union(t).contains(x));
                assert(self.union(t).map(to_set).contains(to_set(x)));
            }
            if t.infinite_filter_map(f).contains(elem) {
                let x = choose|x: A| t.contains(x) && f(x) == Option::Some(elem);
                assert(self.union(t).contains(x));
                assert(self.union(t).map(to_set).contains(to_set(x)));
            }
        }
        assert forall|elem: B| lhs.contains(elem) implies rhs.contains(elem) by {
            let x = choose|x: A| self.union(t).contains(x) && f(x) == Option::Some(elem);
            if self.contains(x) {
                assert(self.map(to_set).contains(to_set(x)));
                assert(self.infinite_filter_map(f).contains(elem));
            } else {
                assert(t.contains(x));
                assert(t.map(to_set).contains(to_set(x)));
                assert(t.infinite_filter_map(f).contains(elem));
            }
        }
        lemma_iset_ext_equal(lhs, rhs);
    }

    /// `infinite_filter_map` preserves finiteness.
    pub broadcast proof fn lemma_infinite_filter_map_finite<B>(self, f: spec_fn(A) -> Option<B>)
        requires
            self.finite(),
        ensures
            #[trigger] self.infinite_filter_map(f).finite(),
        decreases self.len(),
    {
        broadcast use group_set_lemmas;
        broadcast use ISet::lemma_infinite_filter_map_insert;

        let mapped = self.infinite_filter_map(f);
        if self.len() == 0 {
            lemma_iset_len_empty(self);
            assert(self == ISet::<A>::empty());
            assert(self.infinite_filter_map(f) =~= ISet::<B>::empty()) by {
                assert forall|b: B| self.infinite_filter_map(f).contains(b) == ISet::<B>::empty().contains(b) by {
                    super::iset::lemma_iset_empty(b);
                    if self.infinite_filter_map(f).contains(b) {
                        let x = choose|x: A| self.contains(x) && f(x) == Option::Some(b);
                        assert(self.contains(x));
                        assert(false);
                    }
                }
                lemma_iset_ext_equal(self.infinite_filter_map(f), ISet::<B>::empty());
            }
        } else {
            let elem = self.choose();
            lemma_iset_choose_len(self);
            lemma_iset_remove_len(self, elem);
            assert(self.remove(elem).len() < self.len());
            self.remove(elem).lemma_infinite_filter_map_finite(f);
            lemma_iset_remove_insert(self, elem);
            assert(self =~= self.remove(elem).insert(elem));
        }
    }
}

impl<A, FINITE: Finiteness> GSet<A, FINITE> {
    /// Collecting all elements `b` where `f` returns `Some(b)`
    pub open spec fn filter_map<B>(self, f: spec_fn(A) -> Option<B>) -> GSet<B, FINITE> {
        self.apply_filter(f).flatten()
    }

    pub proof fn filter_map_congruence<B>(self, f: spec_fn(A) -> Option<B>)
        ensures
            self.filter_map(f).congruent(
                ISet::from_gset(self.to_infinite()).infinite_filter_map(f).to_gset(),
            ),
    {
        let lhs = self.filter_map(f);
        let mid = self.apply_filter(f).to_iset_deep().infinite_flatten();
        let rhs = ISet::from_gset(self.to_infinite()).infinite_filter_map(f);
        let to_g = |elem: A|
            match f(elem) {
                Option::Some(r) => GSet::empty().insert(r),
                Option::None => GSet::empty(),
            };
        let to_i = |elem: A|
            match f(elem) {
                Option::Some(r) => ISet::empty().insert(r),
                Option::None => ISet::empty(),
            };

        assert forall|b: B| #[trigger] mid.contains(b) == rhs.contains(b) by {
            reveal(ISet::infinite_flatten);
            reveal(GSet::to_iset_deep);
            reveal(GSet::to_infinite_deep);
            reveal(GSet::apply_filter);
            reveal(ISet::infinite_filter_map);
            reveal(ISet::apply_filter);

            self.cast_finiteness_properties::<Infinite>();
            self.apply_filter(f).cast_finiteness_properties::<Infinite>();
            lemma_iset_map_contains(ISet::from_gset(self.to_infinite()), to_i);
            lemma_gset_map_contains(self, to_g);
            lemma_gset_map_contains(
                self.apply_filter(f).to_infinite(),
                |e: GSet<B, FINITE>| e.to_infinite(),
            );
            lemma_iset_map_contains(
                ISet::from_gset(self.apply_filter(f).to_infinite_deep()),
                |e: GSet<B, Infinite>| ISet::from_gset(e),
            );

            if rhs.contains(b) {
                let a = choose|a: A| self.to_infinite().contains(a) && to_i(a).contains(b);
                assert(self.contains(a));
                assert(to_g(a).contains(b));
                assert(self.apply_filter(f).contains(to_g(a)));
                assert(self.apply_filter(f).to_infinite().contains(to_g(a)));
                assert(self.apply_filter(f).to_infinite_deep().contains(to_g(a).to_infinite()));
                assert(self.apply_filter(f).to_iset_deep().contains(ISet::from_gset(to_g(a).to_infinite())));
                assert(ISet::from_gset(to_g(a).to_infinite()).contains(b));
                assert(mid.contains(b));
            }
            if mid.contains(b) {
                let se = choose|se: ISet<B>|
                    self.apply_filter(f).to_iset_deep().contains(se) && se.contains(b);
                let einf = choose|einf: GSet<B, Infinite>|
                    self.apply_filter(f).to_infinite_deep().contains(einf)
                        && ISet::from_gset(einf) == se;
                let efin = choose|efin: GSet<B, FINITE>|
                    self.apply_filter(f).to_infinite().contains(efin) && efin.to_infinite() == einf;
                assert(self.apply_filter(f).to_infinite().contains(efin) == self.apply_filter(f).contains(efin));
                assert(self.apply_filter(f).contains(efin));
                let a = choose|a: A| self.contains(a) && to_g(a) == efin;
                assert(se.contains(b));
                assert(ISet::from_gset(einf) == se);
                assert(einf.contains(b));
                efin.cast_finiteness_properties::<Infinite>();
                assert(efin.contains(b));
                assert(to_g(a).contains(b));
                match f(a) {
                    Option::None => {
                        assert(to_g(a) == GSet::<B, FINITE>::empty());
                        assert(false);
                    }
                    Option::Some(r) => {
                        if b != r {
                            lemma_gset_insert_different(GSet::<B, FINITE>::empty(), b, r);
                            assert(to_g(a).contains(b) == GSet::<B, FINITE>::empty().contains(b));
                            assert(false);
                        }
                        assert(to_i(a).contains(b));
                    }
                }
                assert(self.to_infinite().contains(a));
                assert(ISet::from_gset(self.to_infinite()).map(to_i).contains(to_i(a)));
                assert(rhs.contains(b)) by {
                    reveal(ISet::infinite_filter_map);
                    reveal(ISet::apply_filter);
                    reveal(ISet::infinite_flatten);
                    assert(ISet::from_gset(self.to_infinite()).map(to_i).contains(to_i(a)) && to_i(a).contains(b));
                }
            }
        }
        lemma_iset_ext_equal(mid, rhs);
        assert(mid == rhs) by {
            lemma_iset_ext_equal_eq(mid, rhs);
        }

        if FINITE::type_is_finite() {
            axiom_gset_finite_from_trait(self);
            self.cast_finiteness_properties::<Infinite>();
            assert(self.to_infinite().finite()) by {
                self.to_infinite().congruent_infiniteness(self);
            }
            ISet::from_gset(self.to_infinite()).lemma_infinite_filter_map_finite(f);
            assert(rhs.finite());
            assert(mid.finite());
        }
        reveal(GSet::filter_map);
        reveal(GSet::flatten);
        assert(lhs == mid.to_gset().cast_finiteness::<FINITE>());
        assert(mid.to_gset().castable::<FINITE>()) by {
            if FINITE::type_is_finite() {
                assert(mid.to_gset().finite());
            }
        }
        mid.to_gset().cast_finiteness_properties::<FINITE>();
        assert(lhs.congruent(mid.to_gset()));
        assert(mid.to_gset().congruent(rhs.to_gset()));
    }

    // Can't broadcast because there's no trigger that covers variable FINITE. :v/
    pub  /*broadcast*/
     proof fn lemma_filter_map_insert<B>(s: Self, f: spec_fn(A) -> Option<B>, elem: A)
        ensures
            #[trigger] s.insert(elem).filter_map(f) == (match f(elem) {
                Some(res) => s.filter_map(f).insert(res),
                None => s.filter_map(f),
            }),
    {
        //         broadcast use GSet::flatten_finite;
        assert(s.congruent(s.to_infinite()));
        ISet::lemma_infinite_filter_map_insert(ISet::from_gset(s.to_infinite()), f, elem);
        assert(s.insert(elem).congruent(s.to_infinite().insert(elem)));
        assert(s.insert(elem).to_infinite() == s.to_infinite().insert(elem)) by {
            assert forall|a: A|
                #[trigger] s.insert(elem).to_infinite().contains(a)
                    == s.to_infinite().insert(elem).contains(a) by {
                s.cast_finiteness_properties::<Infinite>();
                s.insert(elem).cast_finiteness_properties::<Infinite>();
                if a == elem {
                    assert(s.insert(elem).contains(a));
                    assert(s.insert(elem).to_infinite().contains(a));
                    assert(s.to_infinite().insert(elem).contains(a));
                } else {
                    assert(s.insert(elem).contains(a) == s.contains(a)) by {
                        lemma_gset_insert_different(s, a, elem);
                    }
                    assert(s.to_infinite().insert(elem).contains(a) == s.to_infinite().contains(a)) by {
                        lemma_gset_insert_different(s.to_infinite(), a, elem);
                    }
                }
            }
            lemma_gset_ext_equal_eq(s.insert(elem).to_infinite(), s.to_infinite().insert(elem));
        }
        s.filter_map_congruence(f);
        s.insert(elem).filter_map_congruence(f);
        assert(s.insert(elem).filter_map(f).congruent(
            ISet::from_gset(s.to_infinite()).insert(elem).infinite_filter_map(f).to_gset(),
        ));
        assert(s.filter_map(f).congruent(ISet::from_gset(s.to_infinite()).infinite_filter_map(f).to_gset()));

    }

    pub broadcast proof fn lemma_filter_map_generic_union<B>(
        self,
        f: spec_fn(A) -> Option<B>,
        t: Self,
    )
        ensures
            #[trigger] self.generic_union(t).filter_map(f) == self.filter_map(f).generic_union(
                t.filter_map(f),
            ),
    {
        let lhs = self.generic_union(t).filter_map(f);
        let rhs = self.filter_map(f).generic_union(t.filter_map(f));
        let iself = ISet::from_gset(self.to_infinite());
        let it = ISet::from_gset(t.to_infinite());
        let iunion = ISet::from_gset(self.generic_union(t).to_infinite());
        let ilhs = iunion.infinite_filter_map(f);
        let irhs = iself.infinite_filter_map(f).union(it.infinite_filter_map(f));

        self.generic_union(t).filter_map_congruence(f);
        self.filter_map_congruence(f);
        t.filter_map_congruence(f);
        iself.lemma_infinite_filter_map_union(f, it);
        assert(iunion == iself.union(it)) by {
            assert forall|a: A| #[trigger] iunion.contains(a) == iself.union(it).contains(a) by {
                self.cast_finiteness_properties::<Infinite>();
                t.cast_finiteness_properties::<Infinite>();
                self.generic_union(t).cast_finiteness_properties::<Infinite>();
                lemma_iset_to_from_gset(self.to_infinite());
                lemma_iset_to_from_gset(t.to_infinite());
                lemma_iset_to_from_gset(self.generic_union(t).to_infinite());
                lemma_set_generic_union(self, t, a);
                assert(self.to_infinite().contains(a) == self.contains(a));
                assert(t.to_infinite().contains(a) == t.contains(a));
                assert(self.generic_union(t).to_infinite().contains(a) == self.generic_union(t).contains(a));
                assert(iself.contains(a) == self.to_infinite().contains(a));
                assert(it.contains(a) == t.to_infinite().contains(a));
                assert(iself.union(it).contains(a) == (iself.contains(a) || it.contains(a)));
            }
            lemma_iset_ext_equal(iunion, iself.union(it));
            lemma_iset_ext_equal_eq(iunion, iself.union(it));
        }

        assert forall|b: B| #[trigger] lhs.contains(b) == rhs.contains(b) by {
            assert(lhs.contains(b) == iunion.infinite_filter_map(f).contains(b));
            assert(iunion.infinite_filter_map(f) == ilhs);
            assert(lhs.contains(b) == ilhs.contains(b));
            assert(rhs.contains(b) == (self.filter_map(f).contains(b) || t.filter_map(f).contains(b)));
            assert(irhs.contains(b) == (
                iself.infinite_filter_map(f).contains(b) || it.infinite_filter_map(f).contains(b)
            ));
            assert(self.filter_map(f).contains(b) == iself.infinite_filter_map(f).contains(b));
            assert(t.filter_map(f).contains(b) == it.infinite_filter_map(f).contains(b));
            iself.lemma_infinite_filter_map_union(f, it);
            assert(iself.union(it).infinite_filter_map(f) == irhs);
            assert(ilhs == iself.union(it).infinite_filter_map(f));
            assert(ilhs == irhs);
        }
        lemma_gset_ext_equal_eq(lhs, rhs);
        assert(lhs == rhs);
    }
}

impl<A, FINITE: Finiteness> GSet<A, FINITE> {
    /// `map` preserves finiteness
    pub proof fn lemma_map_finite<B>(self, f: spec_fn(A) -> B)
        requires
            self.finite(),
        ensures
            self.map(f).finite(),
    {
        lemma_set_map_finite(self, f);
    }

    pub broadcast proof fn lemma_map_by_finite<B>(self, fwd: spec_fn(A) -> B, rev: spec_fn(B) -> A)
        requires
            self.finite(),
        ensures
            #[trigger] self.map_by(fwd, rev).finite(),
    {
        broadcast use lemma_set_subset_finite;

        assert(self.map_by(fwd, rev).subset_of(self.map(fwd)));
        self.lemma_map_finite(fwd);
    }

    pub broadcast proof fn lemma_map_flatten_by_finite<B>(
        self,
        fwd: spec_fn(A) -> Set<B>,
        rev: spec_fn(B) -> A,
    )
        requires
            self.finite(),
            forall|a: A| self.contains(a) ==> fwd(a).finite(),
        ensures
            #[trigger] self.map_flatten_by(fwd, rev).finite(),
    {
        broadcast use lemma_set_subset_finite;

        let s1 = self.map_flatten_by(fwd, rev);
        let s2 = self.map(fwd).flatten();
        assert forall|b: B| s1.contains(b) implies s2.contains(b) by {
            assert(self.map(fwd).contains(fwd(rev(b))));
        }
        assert(s1.subset_of(s2));
        self.lemma_map_finite(fwd);
        self.map(fwd).lemma_flatten_finite();
    }

    pub broadcast proof fn lemma_set_all_subset(self, s2: Set<A>, p: spec_fn(A) -> bool)
        requires
            #[trigger] self.subset_of(s2.to_gset()),
            s2.all(p),
        ensures
            #[trigger] self.all(p),
    {
        broadcast use group_set_lemmas;

    }
}

impl<A, FINITE: Finiteness> GSet<A, FINITE> {
    proof fn lemma_to_seq_to_set_id_recursive(set: Self, elem: A)
        requires
            set.finite(),
        ensures
            set.contains(elem) <==> set.to_seq().contains(elem),
        decreases set.len(),
    {
        broadcast use {super::seq::group_seq_axioms, super::seq_lib::group_seq_properties};
        broadcast use {lemma_set_empty_equivalency_len, lemma_gset_choose_len, lemma_gset_remove_len};

        if set.len() == 0 {
            assert(set =~= GSet::<A, FINITE>::empty());
            assert(!set.contains(elem));
            assert(set.to_seq() == Seq::<A>::empty());
            assert(!set.to_seq().contains(elem));
        } else {
            let c = set.choose();
            lemma_gset_choose_len(set);
            assert(set.contains(c));
            lemma_gset_remove_len(set, c);
            assert(set.remove(c).len() < set.len());

            if elem == c {
                reveal(GSet::to_seq);
                super::seq_lib::lemma_seq_contains_after_push(set.remove(c).to_seq(), c, elem);
                assert(set.to_seq().contains(elem));
            } else {
                Self::lemma_to_seq_to_set_id_recursive(set.remove(c), elem);
                lemma_gset_remove_different(set, elem, c);
                assert(set.contains(elem) == set.remove(c).contains(elem));
                reveal(GSet::to_seq);
                super::seq_lib::lemma_seq_contains_after_push(set.remove(c).to_seq(), c, elem);
                assert(set.to_seq().contains(elem) == set.remove(c).to_seq().contains(elem));
            }
        }
    }
}

impl<A> Set<A> {
    /// Conversion to a sequence and back to a set is the identity function.
    pub broadcast proof fn lemma_to_seq_to_set_id(self)
        ensures
            #[trigger] self.to_seq().to_set() =~= self,
        decreases self.len(),
    {
        broadcast use group_set_lemmas;
        broadcast use lemma_set_empty_equivalency_len;
        broadcast use super::seq::group_seq_axioms;
        broadcast use super::seq_lib::group_seq_properties;
        broadcast use lemma_set_empty_len;

        if self.len() == 0 {
            assert(self.to_seq().to_set() =~= Set::<A>::empty());
        } else {
            let elem = self.choose();
            self.remove(elem).lemma_to_seq_to_set_id();
            let outer = self.to_seq().to_set();
            let inner = self.remove(elem).to_seq().to_set().insert(elem);
            self.to_seq().to_set_ensures();
            self.remove(elem).to_seq().to_set_ensures();

            assert forall|x| #![auto] outer.contains(x) implies inner.contains(x) by {
                GSet::lemma_to_seq_to_set_id_recursive(self.to_gset(), x);
                GSet::lemma_to_seq_to_set_id_recursive(self.to_gset().remove(elem), x);
                if x != elem {
                    lemma_set_remove_different(self, x, elem);
                    assert(self.contains(x) == self.remove(elem).contains(x));
                }
            }
            assert forall|x| #![auto] inner.contains(x) implies outer.contains(x) by {
                GSet::lemma_to_seq_to_set_id_recursive(self.to_gset(), x);
                GSet::lemma_to_seq_to_set_id_recursive(self.to_gset().remove(elem), x);
                if x != elem {
                    lemma_set_remove_different(self, x, elem);
                    assert(self.contains(x) == self.remove(elem).contains(x));
                }
            }
            assert(self.to_seq().to_set() =~= self.remove(elem).to_seq().to_set().insert(elem));
        }
    }
}

impl<A> ISet<A> {
    pub broadcast proof fn lemma_to_seq_to_iset_id(self)
        requires
            self.finite(),
        ensures
            #[trigger] self.to_seq().to_iset() =~= self,
        decreases self.len(),
    {
        broadcast use super::seq::axiom_seq_empty;

        if self.len() == 0 {
            assert(self.to_seq() == Seq::<A>::empty());
            assert(forall|e| !self.to_seq().contains(e));
            assert(self.to_seq().to_iset() =~= ISet::<A>::empty()) by {
                self.to_seq().to_iset_ensures();
                assert forall|e: A| self.to_seq().to_iset().contains(e) == ISet::<A>::empty().contains(e) by {
                    super::iset::lemma_iset_empty(e);
                    assert(!self.to_seq().contains(e));
                }
                lemma_iset_ext_equal(self.to_seq().to_iset(), ISet::<A>::empty());
            }
            lemma_iset_len_empty(self);
            assert(self =~= ISet::<A>::empty());
            assert(self.to_seq().to_iset() =~= self);
        } else {
            let elem = self.choose();
            lemma_iset_choose_len(self);
            lemma_iset_remove_len(self, elem);
            assert(self.remove(elem).len() < self.len());
            self.remove(elem).lemma_to_seq_to_iset_id();
            let outer = self.to_seq().to_iset();
            let inner = self.remove(elem).to_seq().to_iset().insert(elem);

            assert forall|x| #![auto] outer.contains(x) implies inner.contains(x) by {
                GSet::lemma_to_seq_to_set_id_recursive(self.to_gset(), x);
                GSet::lemma_to_seq_to_set_id_recursive(self.to_gset().remove(elem), x);
            }
            assert forall|x| #![auto] inner.contains(x) implies outer.contains(x) by {
                GSet::lemma_to_seq_to_set_id_recursive(self.to_gset(), x);
            }
            lemma_iset_ext_equal(outer, inner);
            assert forall|x: A| inner.contains(x) == self.remove(elem).insert(elem).contains(x) by {
                if x == elem {
                    assert(inner.contains(x));
                    assert(self.remove(elem).insert(elem).contains(x));
                } else {
                    lemma_iset_insert_different(self.remove(elem).to_seq().to_iset(), x, elem);
                    lemma_iset_insert_different(self, x, elem);
                    lemma_iset_insert_different(self.remove(elem), x, elem);
                }
            }
            lemma_iset_ext_equal(inner, self.remove(elem).insert(elem));
            lemma_iset_remove_insert(self, elem);
            assert(inner =~= self);
            assert(outer =~= self);
        }
    }

    pub proof fn lemma_flatten_finite(self)
        requires
            self.finite(),
            forall|s: Set<A>| self.contains(s) ==> #[trigger] s.finite(),
        ensures
            self.flatten().finite(),
        decreases self.len(),
    {
        broadcast use group_set_axioms;

        if self.len() == 0 {
            assert(self.flatten() =~= Set::<A>::empty());
        } else {
            let s = self.choose();
            let self2 = self.remove(s);
            self2.lemma_flatten_finite();
            self2.flatten_insert_union_commute(s);
        }
    }
}

pub trait FiniteRange: Sized {
    spec fn range_set(lo: Self, hi: Self) -> Set<Self>;

    spec fn range_len(lo: Self, hi: Self) -> nat;

    proof fn range_properties(lo: Self, hi: Self)
        ensures
            Self::range_set(lo, hi).finite(),
            Self::range_set(lo, hi).len() == Self::range_len(lo, hi),
    ;
}

pub broadcast proof fn range_set_properties<A: FiniteRange>(lo: A, hi: A)
    ensures
        (#[trigger] A::range_set(lo, hi)).finite(),
        A::range_set(lo, hi).len() == A::range_len(lo, hi),
{
    A::range_properties(lo, hi);
}

pub trait FiniteFull: Sized {
    proof fn full_properties()
        ensures
            Set::<Self>::full().finite(),
    ;
}

pub broadcast proof fn full_set_properties<A: FiniteFull>()
    ensures
        #![trigger Set::<A>::full()]
        (Set::<A>::full()).finite(),
{
    A::full_properties();
}

impl<A: FiniteRange> Set<A> {
    #[verifier::inline]
    pub open spec fn range(lo: A, hi: A) -> Set<A> {
        A::range_set(lo, hi)
    }

    #[verifier::inline]
    pub open spec fn range_inclusive(lo: A, hi: A) -> Set<A> {
        A::range_set(lo, hi).insert(hi)
    }
}

impl<A: FiniteFull> Set<A> {
    #[verifier::inline]
    pub open spec fn from_finite_type(f: spec_fn(A) -> bool) -> Set<A> {
        Set::<A>::full().filter(f)
    }
}

// Macro to implement the trait for every numeric type. We need a macro here
// because 'as nat' can't be written as a type generic.
macro_rules! range_impls {
    ([$($t:ty)*]) => {
        $(
            verus! {
                impl FiniteRange for $t {
                    open spec fn range_set(lo: Self, hi: Self) -> Set<Self> {
                        Set::new(|i: Self| lo <= i < hi)
                    }
                    open spec fn range_len(lo: Self, hi: Self) -> nat {
                        if lo <= hi { (hi - lo) as nat } else { 0 }
                    }
                    proof fn range_properties(lo: Self, hi: Self)
                        decreases hi - lo
                    {
                        broadcast use axiom_set_empty_finite;
                        broadcast use axiom_set_empty_len;
                        broadcast use axiom_set_insert_finite;

                        if hi <= lo {
                            assert(Self::range_set(lo, hi).is_empty());
                        } else {
                            let hi1 = (hi - 1) as $t;
                            Self::range_properties(lo, hi1);
                            assert(Self::range_set(lo, hi) == Self::range_set(lo, hi1).insert(hi1));
                            axiom_set_insert_finite(Self::range_set(lo, hi1), hi1);
                        }
                    }
                }
            } // verus!
        )*
    }
}

macro_rules! full_impls {
    ([$($t:ty)*]) => {
        $(
            verus! {
                impl FiniteFull for $t {
                    proof fn full_properties() {
                        broadcast use axiom_set_insert_finite;

                        assert(Set::<$t>::full() == Set::range_inclusive($t::MIN, $t::MAX));
                        <$t as FiniteRange>::range_properties($t::MIN, $t::MAX);
                    }
                }
            } // verus!
        )*
    }
}

// Make Set::range available for all of the Verus numeric types
range_impls!([
    int nat
    usize u8 u16 u32 u64 u128
    isize i8 i16 i32 i64 i128
]);

// Make Set::full available for all of the Verus numeric types
full_impls!([
    usize u8 u16 u32 u64 u128
    isize i8 i16 i32 i64 i128
]);

/// Two sets are equal iff mapping `f` results in equal sets, if `f` is injective.
pub proof fn lemma_sets_eq_iff_injective_map_eq<T, S>(s1: Set<T>, s2: Set<T>, f: spec_fn(T) -> S)
    requires
        super::relations::injective(f),
    ensures
        (s1 == s2) <==> (s1.map(f) == s2.map(f)),
{
    broadcast use group_set_lemmas;
    broadcast use lemma_set_map_contains;

    if (s1.map(f) == s2.map(f)) {
        assert forall|x: T| s1.contains(x) implies s2.contains(x) by {
            assert(s1.map(f).contains(f(x)));
            assert(s2.map(f).contains(f(x)));
            let y = choose|y: T| s2.contains(y) && f(y) == f(x);
            assert(y == x);
            assert(s2.contains(x));
        }
        assert forall|x: T| s2.contains(x) implies s1.contains(x) by {
            assert(s2.map(f).contains(f(x)));
            assert(s1.map(f).contains(f(x)));
            let y = choose|y: T| s1.contains(y) && f(y) == f(x);
            assert(y == x);
            assert(s1.contains(x));
        }
        lemma_set_ext_equal_eq(s1, s2);
    }
}

/// Two sets are equal iff applying an injective (in the union of the sets) function `f` to each set produces equal sets.
pub proof fn lemma_sets_eq_iff_injective_map_on_eq<T, S>(s1: Set<T>, s2: Set<T>, f: spec_fn(T) -> S)
    requires
        super::relations::injective_on(f, s1 + s2),
    ensures
        (s1 == s2) <==> (s1.map(f) == s2.map(f)),
{
    broadcast use group_set_axioms;

    if (s1.map(f) == s2.map(f)) {
        assert(s1.map(f).len() == s2.map(f).len());
        if !s1.subset_of(s2) {
            let x = choose|x: T| s1.contains(x) && !s2.contains(x);
            assert(s1.map(f).contains(f(x)));
        } else if !s2.subset_of(s1) {
            let x = choose|x: T| s2.contains(x) && !s1.contains(x);
            assert(s2.map(f).contains(f(x)));
        }
        assert(s1 =~= s2);
    }
}

/// The result of inserting an element `a` into a set `s` is finite iff `s` is finite.
pub broadcast proof fn lemma_set_insert_finite_iff<A>(s: ISet<A>, a: A)
    ensures
        #[trigger] s.insert(a).finite() <==> s.finite(),
{
    broadcast use GSet::congruent_infiniteness;
    // apppeal to finite-typed versions

    if s.insert(a).finite() {
        if s.contains(a) {
            assert forall|x: A| s.insert(a).contains(x) == s.contains(x) by {
                lemma_iset_insert_same(s, a);
                if x != a {
                    lemma_iset_insert_different(s, x, a);
                }
            }
            lemma_iset_ext_equal_eq(s.insert(a), s);
            assert(s.subset_of(s.insert(a))) by {
                assert forall|x: A| s.contains(x) implies s.insert(a).contains(x) by {
                    if x != a {
                        lemma_iset_insert_different(s, x, a);
                    } else {
                        lemma_iset_insert_same(s, a);
                    }
                }
            }
            lemma_set_subset_finite(s.insert(a), s);
        } else {
            assert(s.subset_of(s.insert(a))) by {
                assert forall|x: A| s.contains(x) implies s.insert(a).contains(x) by {
                    if x == a {
                        assert(false);
                    } else {
                        lemma_iset_insert_different(s, x, a);
                    }
                }
            }
            lemma_set_subset_finite(s.insert(a), s);
        }
    }
}

/// The result of removing an element `a` into a set `s` is finite iff `s` is finite.
pub broadcast proof fn lemma_set_remove_finite_iff<A>(s: Set<A>, a: A)
    ensures
        #[trigger] s.remove(a).finite() <==> s.finite(),
{
    if s.remove(a).finite() {
        if s.contains(a) {
            assert(s == s.remove(a).insert(a));
        } else {
            assert(s == s.remove(a));
        }
    }
}

/// The union of two sets is finite iff both sets are finite.
pub broadcast proof fn lemma_set_union_finite_iff<A>(s1: ISet<A>, s2: ISet<A>)
    ensures
        (#[trigger] s1.generic_union(s2.to_gset())).finite() <==> s1.finite() && s2.finite(),
        (#[trigger] s1.union(s2)).finite() <==> s1.finite() && s2.finite(),
{
    assert(s1.union(s2) == s1.generic_union(s2.to_gset()));  // extn
    if s1.generic_union(s2.to_gset()).finite() {
        lemma_set_generic_union_finite_implies_sets_finite(s1, s2);
    }
}

pub proof fn lemma_set_generic_union_finite_implies_sets_finite<A>(s1: ISet<A>, s2: ISet<A>)
    requires
        s1.generic_union(s2.to_gset()).finite(),
    ensures
        s1.finite(),
        s2.finite(),
    decreases 0nat,
{
    let u = s1.generic_union(s2.to_gset());
    assert(s1.subset_of(u)) by {
        assert forall|x: A| s1.contains(x) implies u.contains(x) by {
            lemma_iset_union(s1, s2, x);
        }
    }
    assert(s2.subset_of(u)) by {
        assert forall|x: A| s2.contains(x) implies u.contains(x) by {
            lemma_iset_union(s1, s2, x);
        }
    }
    lemma_set_subset_finite(u, s1);
    lemma_set_subset_finite(u, s2);
}

/// The size of a union of two sets is less than or equal to the size of
/// both individual sets combined.
pub proof fn lemma_len_union<A>(s1: Set<A>, s2: Set<A>)
    requires
        s1.finite(),
        s2.finite(),
    ensures
        s1.generic_union(s2.to_gset()).len() <= s1.len() + s2.len(),
{
    lemma_set_intersect_union_lens(s1.to_gset(), s2.to_gset());
    assert(s1.generic_union(s2.to_gset()).len() + s1.generic_intersect(s2.to_gset()).len() == s1.len() + s2.len());
    assert(s1.generic_union(s2.to_gset()).len() <= s1.len() + s2.len());
}

/// The size of a union of two sets is greater than or equal to the size of
/// both individual sets.
pub proof fn lemma_len_union_ind<A>(s1: Set<A>, s2: Set<A>)
    requires
        s1.finite(),
        s2.finite(),
    ensures
        s1.generic_union(s2.to_gset()).len() >= s1.len(),
        s1.generic_union(s2.to_gset()).len() >= s2.len(),
{
    let u = s1.generic_union(s2.to_gset()).to_gset();
    lemma_set_generic_union_finite(s1.to_gset(), s2.to_gset());
    assert(s1.to_gset().subset_of(u)) by {
        assert forall|x: A| s1.contains(x) implies u.contains(x) by {
            lemma_set_generic_union(s1.to_gset(), s2.to_gset(), x);
        }
    }
    assert(s2.to_gset().subset_of(u)) by {
        assert forall|x: A| s2.contains(x) implies u.contains(x) by {
            lemma_set_generic_union(s1.to_gset(), s2.to_gset(), x);
        }
    }
    lemma_len_subset(s1.to_gset(), u);
    lemma_len_subset(s2.to_gset(), u);
}

/// The size of the intersection of finite set `s1` and set `s2` is less than or equal to the size of `s1`.
pub proof fn lemma_len_intersect<A, FINITE: Finiteness, FINITE2: Finiteness>(
    s1: GSet<A, FINITE>,
    s2: GSet<A, FINITE2>,
)
    requires
        s1.finite(),
    ensures
        s1.generic_intersect(s2).len() <= s1.len(),
    decreases s1.len(),
{
    if s1.len() == 0 {
        lemma_set_empty_equivalency_len(s1);
        assert(s1 =~= GSet::empty());
        let inter = s1.generic_intersect(s2);
        lemma_gset_generic_intersect_finite(s1, s2);
        assert(inter =~= GSet::empty()) by {
            assert forall|a: A| inter.contains(a) == GSet::<A, Infinite>::empty().contains(a) by {
                lemma_gset_generic_intersect(s1, s2, a);
            }
            lemma_gset_ext_equal(inter, GSet::empty());
        }
        lemma_set_empty_equivalency_len(inter);
        assert(inter.len() == 0);
        assert(s1.len() == 0);
    } else {
        let a = s1.choose();
        lemma_gset_choose_len(s1);
        lemma_gset_remove_len(s1, a);
        assert(s1.remove(a).len() < s1.len());
        let inter = s1.generic_intersect(s2);
        assert(inter.remove(a) =~= s1.remove(a).generic_intersect(s2));
        lemma_len_intersect::<A, FINITE, FINITE2>(s1.remove(a), s2);
        lemma_gset_remove_len(inter, a);
        assert(inter.remove(a).len() <= s1.remove(a).len());
        assert(inter.len() <= inter.remove(a).len() + 1) by {
            if inter.contains(a) {
                assert(inter.len() == inter.remove(a).len() + 1);
            } else {
                assert(inter.len() == inter.remove(a).len());
            }
        }
        assert(inter.remove(a).len() + 1 <= s1.remove(a).len() + 1);
        assert(inter.len() <= s1.remove(a).len() + 1);
        assert(s1.len() == s1.remove(a).len() + 1);
        assert(inter.len() <= s1.len());
    }
}

/// If `s1` is a subset of finite set `s2`, then the size of `s1` is less than or equal to
/// the size of `s2` and `s1` must be finite.
pub proof fn lemma_len_subset<A, FINITE: Finiteness, FINITE2: Finiteness>(
    s1: GSet<A, FINITE>,
    s2: GSet<A, FINITE2>,
)
    requires
        s2.finite(),
        s1.subset_of(s2),
    ensures
        s1.len() <= s2.len(),
        s1.finite(),
{
    lemma_len_intersect::<A, FINITE2, FINITE>(s2, s1);
    assert(s2.generic_intersect(s1).congruent(s1));
}

/// A subset of a finite set `s` is finite.
pub broadcast proof fn lemma_set_subset_finite<A>(s: ISet<A>, sub: ISet<A>)
    requires
        s.finite(),
        sub.subset_of(s),
    ensures
        #![trigger sub.subset_of(s)]
        sub.finite(),
{
    let complement = s.generic_difference(sub.to_gset());
    assert forall|a: A| sub.contains(a) == s.generic_difference(complement.to_gset()).contains(a) by {
        lemma_iset_difference(s, complement, a);
        lemma_iset_difference(s, sub, a);
        if sub.contains(a) {
            assert(!complement.contains(a));
        }
        if s.generic_difference(complement.to_gset()).contains(a) {
            assert(s.contains(a) && !complement.contains(a));
            assert(sub.contains(a));
        }
    }
    lemma_iset_ext_equal(sub, s.generic_difference(complement.to_gset()));
    lemma_iset_ext_equal_eq(sub, s.generic_difference(complement.to_gset()));
}

/// The size of the difference of finite set `s1` and set `s2` is less than or equal to the size of `s1`.
pub proof fn lemma_len_difference<A>(s1: ISet<A>, s2: ISet<A>)
    requires
        s1.finite(),
    ensures
        s1.generic_difference(s2.to_gset()).len() <= s1.len(),
{
    let d = s1.generic_difference(s2.to_gset());
    assert(d.subset_of(s1)) by {
        assert forall|a: A| d.contains(a) implies s1.contains(a) by {
            lemma_iset_difference(s1, s2, a);
        }
    }
    lemma_len_subset(d.to_gset(), s1.to_gset());
}

/// If x is a subset of y and the size of x is equal to the size of y, x is equal to y.
pub proof fn lemma_subset_equality<A>(x: Set<A>, y: Set<A>)
    requires
        x.subset_of(y),
        x.finite(),
        y.finite(),
        x.len() == y.len(),
    ensures
        x =~= y,
{
    assert forall|e: A| y.contains(e) implies x.contains(e) by {
        if y.contains(e) && !x.contains(e) {
            x.to_gset().lemma_subset_not_in_lt(y.to_gset(), e);
            assert(x.len() < y.len());
            assert(false);
        }
    }
    lemma_set_ext_equal(x, y);
}

/// If an injective function is applied to each element of a set to construct
/// another set, the two sets have the same size.
pub proof fn lemma_map_size<A, B>(x: Set<A>, y: Set<B>, f: spec_fn(A) -> B)
    requires
        x.finite(),
        injective_on(f, x),
        x.map(f) == y,
    ensures
        y.finite(),
        x.len() == y.len(),
    decreases x.len(),
{
    broadcast use group_set_properties;

    if x.len() == 0 {
        if !y.is_empty() {
            let e = y.choose();
        }
    } else {
        let a = x.choose();
        assert(x.remove(a).map(f) == y.remove(f(a)));
        lemma_map_size(x.remove(a), y.remove(f(a)), f);
        assert(y == y.remove(f(a)).insert(f(a)));
    }
}

/// If any function is applied to each element of a set to construct
/// another set, the constructed set's length is at most the original's
pub proof fn lemma_map_size_bound<A, B>(x: Set<A>, y: Set<B>, f: spec_fn(A) -> B)
    requires
        x.finite(),
        x.map(f) == y,
    ensures
        y.finite(),
        y.len() <= x.len(),
    decreases x.len(),
{
    broadcast use group_set_properties;

    if x.is_empty() {
        if !y.is_empty() {
            let e = y.choose();
        }
    } else {
        let xx = x.choose();
        let img = f(xx);
        let pre = x.filter(|a: A| f(a) == f(xx));
        x.lemma_len_filter(|a: A| f(a) == f(xx));
        let wit = choose|a: A| x.contains(a) && f(a) == f(xx);
        assert forall|b: B| (#[trigger] y.remove(f(xx)).contains(b)) implies exists|a: A|
            x.difference(pre).contains(a) && f(a) == b by {
            let pre_wit = choose|a: A| x.contains(a) && f(a) == b;
            assert(x.difference(pre).contains(pre_wit));
        }

        assert(x == x.difference(pre).union(pre));
        assert(y == y.remove(f(xx)).insert(f(xx)));
        assert(x.difference(pre).map(f) == y.remove(f(xx)));
        lemma_map_size_bound(x.difference(pre), y.remove(f(xx)), f);
    }
}

// This verified lemma used to be an axiom in the Dafny prelude
/// Taking the union of sets `a` and `b` and then taking the union of the result with `b`
/// is the same as taking the union of `a` and `b` once.
pub broadcast proof fn lemma_set_union_again1<A>(a: Set<A>, b: Set<A>)
    ensures
        #[trigger] a.generic_union(b.to_gset()).generic_union(b.to_gset()) =~= a.generic_union(b.to_gset()),
{
    assert forall|x: A|
        a.generic_union(b.to_gset()).generic_union(b.to_gset()).contains(x)
            == a.generic_union(b.to_gset()).contains(x) by {
        lemma_gset_generic_union(a.to_gset(), b.to_gset(), x);
        lemma_gset_generic_union(a.generic_union(b.to_gset()).to_gset(), b.to_gset(), x);
    }
    lemma_iset_ext_equal(
        a.generic_union(b.to_gset()).generic_union(b.to_gset()),
        a.generic_union(b.to_gset()),
    );
}

// This verified lemma used to be an axiom in the Dafny prelude
/// Taking the union of sets `a` and `b` and then taking the union of the result with `a`
/// is the same as taking the union of `a` and `b` once.
pub broadcast proof fn lemma_set_union_again2<A>(a: Set<A>, b: Set<A>)
    ensures
        #[trigger] a.generic_union(b.to_gset()).generic_union(a.to_gset()) =~= a.generic_union(b.to_gset()),
{
    assert forall|x: A|
        a.generic_union(b.to_gset()).generic_union(a.to_gset()).contains(x)
            == a.generic_union(b.to_gset()).contains(x) by {
        lemma_gset_generic_union(a.to_gset(), b.to_gset(), x);
        lemma_gset_generic_union(a.generic_union(b.to_gset()).to_gset(), a.to_gset(), x);
    }
    lemma_iset_ext_equal(
        a.generic_union(b.to_gset()).generic_union(a.to_gset()),
        a.generic_union(b.to_gset()),
    );
}

// This verified lemma used to be an axiom in the Dafny prelude
/// Taking the intersection of sets `a` and `b` and then taking the intersection of the result with `b`
/// is the same as taking the intersection of `a` and `b` once.
pub broadcast proof fn lemma_set_intersect_again1<A>(a: Set<A>, b: Set<A>)
    ensures
        #![trigger (a.generic_intersect(b.to_gset())).generic_intersect(b.to_gset())]
        (a.generic_intersect(b.to_gset())).generic_intersect(b.to_gset()) =~= a.generic_intersect(b.to_gset()),
{
    assert forall|x: A|
        a.generic_intersect(b.to_gset()).generic_intersect(b.to_gset()).contains(x)
            == a.generic_intersect(b.to_gset()).contains(x) by {
        lemma_gset_generic_intersect(a.to_gset(), b.to_gset(), x);
        lemma_gset_generic_intersect(a.generic_intersect(b.to_gset()).to_gset(), b.to_gset(), x);
    }
    lemma_iset_ext_equal(
        a.generic_intersect(b.to_gset()).generic_intersect(b.to_gset()),
        a.generic_intersect(b.to_gset()),
    );
}

// This verified lemma used to be an axiom in the Dafny prelude
/// Taking the intersection of sets `a` and `b` and then taking the intersection of the result with `a`
/// is the same as taking the intersection of `a` and `b` once.
pub broadcast proof fn lemma_set_intersect_again2<A>(a: Set<A>, b: Set<A>)
    ensures
        #![trigger (a.generic_intersect(b.to_gset())).generic_intersect(a.to_gset())]
        (a.generic_intersect(b.to_gset())).generic_intersect(a.to_gset()) =~= a.generic_intersect(b.to_gset()),
{
    assert forall|x: A|
        a.generic_intersect(b.to_gset()).generic_intersect(a.to_gset()).contains(x)
            == a.generic_intersect(b.to_gset()).contains(x) by {
        lemma_gset_generic_intersect(a.to_gset(), b.to_gset(), x);
        lemma_gset_generic_intersect(a.generic_intersect(b.to_gset()).to_gset(), a.to_gset(), x);
    }
    lemma_iset_ext_equal(
        a.generic_intersect(b.to_gset()).generic_intersect(a.to_gset()),
        a.generic_intersect(b.to_gset()),
    );
}

// This verified lemma used to be an axiom in the Dafny prelude
/// If set `s2` contains element `a`, then the set difference of `s1` and `s2` does not contain `a`.
pub broadcast proof fn lemma_set_difference2<A, FINITE1: Finiteness, FINITE2: Finiteness>(
    s1: GSet<A, FINITE1>,
    s2: GSet<A, FINITE2>,
    a: A,
)
    ensures
        #![trigger s1.generic_difference(s2).contains(a)]
        s2.contains(a) ==> !s1.generic_difference(s2).contains(a),
{
}

// This verified lemma used to be an axiom in the Dafny prelude
/// If sets `a` and `b` are disjoint, meaning they have no elements in common, then the set difference
/// of `a.union(b)` and `b` is equal to `a` and the set difference of `a.union(b)` and `a` is equal to `b`.
pub broadcast proof fn lemma_gset_disjoint<A, FINITE: Finiteness, FINITE2: Finiteness>(
    a: GSet<A, FINITE>,
    b: GSet<A, FINITE2>,
)
    ensures
        #![trigger a.generic_union(b).generic_difference(a)]
        a.disjoint(b) ==> (a.generic_union(b).generic_difference(a) =~= b.to_infinite()
            && a.generic_union(b).generic_difference(b) =~= a.to_infinite()),
{
}

pub broadcast proof fn lemma_set_disjoint<A>(a: Set<A>, b: Set<A>)
    ensures
        #![trigger a.union(b).difference(a)]
        a.disjoint(b) ==> (a.union(b).difference(a) =~= b && a.union(b).difference(b) =~= a),
{
}

pub broadcast proof fn lemma_iset_disjoint<A>(a: ISet<A>, b: ISet<A>)
    ensures
        #![trigger a.union(b).difference(a)]
        a.disjoint(b) ==> (a.union(b).difference(a) =~= b.to_infinite() && a.union(b).difference(b)
            =~= a.to_infinite()),
{
    lemma_gset_disjoint(a.to_gset(), b.to_gset());
    if a.disjoint(b) {
        assert(a.union(b).difference(a) =~= b.to_infinite());
        assert(a.union(b).difference(b) =~= a.to_infinite());
    }
}

// This verified lemma used to be an axiom in the Dafny prelude
// Dafny encodes the second clause with a single directional, although
// it should be fine with both directions?
// REVIEW: excluded from broadcast group if trigger is too free
//         also not that some proofs in seq_lib requires this lemma
/// Set `s` has length 0 if and only if it is equal to the empty set. If `s` has length greater than 0,
/// Then there must exist an element `x` such that `s` contains `x`.
pub broadcast proof fn lemma_set_empty_equivalency_len<A, FINITE: Finiteness>(s: GSet<A, FINITE>)
    requires
        s.finite(),
    ensures
        #![trigger s.len()]
        (s.len() == 0 <==> s =~= GSet::<A, FINITE>::empty()) && (s.len() != 0 ==> exists|x: A|
            s.contains(x)),
{
    assert(s.len() == 0 ==> s =~= GSet::empty()) by {
        if s.len() == 0 {
            assert forall|a: A| s.contains(a) == GSet::<A, FINITE>::empty().contains(a) by {
                if s.contains(a) {
                    lemma_gset_contains_len(s.to_finite(), a);
                    assert(false);
                }
            }
            lemma_gset_ext_equal(s, GSet::empty());
        }
    };
    assert(s =~= GSet::empty() ==> s.len() == 0) by {
        if s =~= GSet::empty() {
            if s.len() != 0 {
                lemma_gset_choose_len(s);
                assert(s.contains(s.choose()));
                lemma_gset_ext_equal(s, GSet::empty());
                assert(GSet::<A, FINITE>::empty().contains(s.choose()));
                assert(false);
            }
        }
    };
    assert(s.len() != 0 ==> exists|x: A| s.contains(x)) by {
        if s.len() != 0 {
            lemma_gset_choose_len(s);
            assert(s.contains(s.choose()));  // witness
        }
    };
}

// This verified lemma used to be an axiom in the Dafny prelude
/// If sets `a` and `b` are disjoint, meaning they share no elements in common, then the length
/// of the union `a.union(b)` is equal to the sum of the lengths of `a` and `b`.
/// ("lens" here refers to the shape of the intersection in the classic two-circle Venn diagram.)
pub broadcast proof fn lemma_gset_disjoint_lens<A, FINITE1: Finiteness, FINITE2: Finiteness>(
    a: GSet<A, FINITE1>,
    b: GSet<A, FINITE2>,
)
    requires
        a.finite(),
        b.finite(),
    ensures
        a.disjoint(b) ==> #[trigger] a.generic_union(b).len() == a.len() + b.len(),
    decreases a.len(),
    {
    if a.len() == 0 {
        lemma_set_empty_equivalency_len(a);
        assert(a.generic_union(b) =~= b.to_infinite());
        b.congruent_len(b.to_infinite());
    } else {
        if a.disjoint(b) {
            let x = a.choose();
            lemma_gset_choose_len(a);
            lemma_gset_remove_len(a, x);
            assert(a.remove(x).len() < a.len());
            assert(!b.contains(x));
            assert forall|aa: A|
                a.remove(x).generic_union(b).contains(aa) == a.generic_union(b).remove(x).contains(
                    aa,
                ) by {
                if aa == x {
                    lemma_gset_remove_same(a.generic_union(b), x);
                    lemma_gset_remove_same(a, x);
                    lemma_gset_generic_union(a.remove(x), b, x);
                } else {
                    lemma_gset_remove_different(a, aa, x);
                    lemma_gset_remove_different(a.generic_union(b), aa, x);
                    lemma_gset_generic_union(a.remove(x), b, aa);
                    lemma_gset_generic_union(a, b, aa);
                }
            }
            lemma_gset_ext_equal(a.remove(x).generic_union(b), a.generic_union(b).remove(x));
            lemma_gset_disjoint_lens(a.remove(x), b);
            let u = a.generic_union(b);
            let ur = a.remove(x).generic_union(b);
            lemma_gset_generic_union_finite(a, b);
            lemma_gset_generic_union_finite(a.remove(x), b);
            ur.congruent_len(u.remove(x));
            lemma_gset_generic_union(a, b, x);
            assert(u.contains(x));
            lemma_gset_remove_len(u, x);
            assert(ur.len() == a.remove(x).len() + b.len());
            assert(u.len() == ur.len() + 1);
            assert(a.len() == a.remove(x).len() + 1);
            assert(u.len() == a.len() + b.len());
        }
    }
}

/// Two sets are disjoint iff their intersection is empty
pub proof fn lemma_disjoint_iff_empty_intersection<T>(a: Set<T>, b: Set<T>)
    ensures
        a.disjoint(b) <==> a.intersect(b).is_empty(),
{
    broadcast use group_set_properties;

    if a.disjoint(b) {
        assert(b.disjoint(a));
        assert(forall|x: T| a.contains(x) ==> !(a.contains(x) && b.contains(x)));
        assert(forall|x: T| b.contains(x) ==> !(a.contains(x) && b.contains(x)));
        assert(forall|x: T| !a.intersect(b).contains(x));
    }
    if a.intersect(b).is_empty() {
        assert(forall|x: T| !a.intersect(b).contains(x));
        if !a.disjoint(b) {
            assert(exists|x: T| a.contains(x) && b.contains(x));
            let x = choose|x: T| a.contains(x) && b.contains(x);
            assert(a.intersect(b).contains(x));
            assert(!a.intersect(b).is_empty());
        }
    }
}

pub broadcast proof fn lemma_set_disjoint_lens<A>(a: Set<A>, b: Set<A>)
    ensures
        a.disjoint(b) ==> #[trigger] a.union(b).len() == a.len() + b.len(),
    decreases a.len(),
{
    lemma_gset_disjoint_lens(a.to_gset(), b.to_gset());
    reveal(Set::spec_add);
    reveal(Set::union);
    assert forall|x: A| (a + b).to_infinite().contains(x) == a.generic_union(b.to_gset()).contains(x) by {
        super::set::lemma_set_to_infinite_contains(a + b, x);
        lemma_set_union(a, b, x);
        lemma_gset_generic_union(a.to_gset(), b.to_gset(), x);
        assert(a.contains(x) == a.to_gset().contains(x));
        assert(b.contains(x) == b.to_gset().contains(x));
    }
    lemma_iset_ext_equal((a + b).to_infinite(), a.generic_union(b.to_gset()));
    assert((a + b).to_infinite() =~= a.generic_union(b.to_gset()));
    if a.disjoint(b) {
        lemma_set_finite_from_type(a + b);
        lemma_set_generic_union_finite(a.to_gset(), b.to_gset());
        lemma_iset_ext_equal_eq((a + b).to_infinite(), a.generic_union(b.to_gset()));
        assert((a + b).to_infinite() == a.generic_union(b.to_gset()));
        assert(a.to_gset().disjoint(b.to_gset()));
        assert(a.generic_union(b.to_gset()).len() == a.len() + b.len());
        (a + b).to_gset().to_infinite_ensures();
        lemma_iset_to_from_gset((a + b).to_gset().to_infinite());
        assert((a + b).to_infinite().to_gset() == (a + b).to_gset().to_infinite());
        assert((a + b).to_infinite().len() == (a + b).len());
        assert((a + b).len() == a.len() + b.len());
    }
}

pub broadcast proof fn lemma_iset_disjoint_lens<A>(a: ISet<A>, b: ISet<A>)
    requires
        a.finite(),
        b.finite(),
    ensures
        a.disjoint(b) ==> #[trigger] a.union(b).len() == a.len() + b.len(),
    decreases a.len(),
{
    lemma_set_union_finite_iff(a, b);
    lemma_gset_disjoint_lens(a.to_gset(), b.to_gset());
    reveal(ISet::spec_add);
    lemma_iset_union_eq(a, b);
    assert((a + b) =~= a.generic_union(b.to_gset()));
}

pub broadcast proof fn lemma_set_disjoint_lens_finite<A>(a: Set<A>, b: Set<A>)
    ensures
        a.disjoint(b) ==> #[trigger] a.union(b).len() == a.len() + b.len(),
{
    lemma_gset_disjoint_lens(a.to_gset(), b.to_gset());
    reveal(Set::spec_add);
    reveal(Set::union);
    assert forall|x: A| (a + b).to_infinite().contains(x) == a.generic_union(b.to_gset()).contains(x) by {
        super::set::lemma_set_to_infinite_contains(a + b, x);
        lemma_set_union(a, b, x);
        lemma_gset_generic_union(a.to_gset(), b.to_gset(), x);
        assert(a.contains(x) == a.to_gset().contains(x));
        assert(b.contains(x) == b.to_gset().contains(x));
    }
    lemma_iset_ext_equal((a + b).to_infinite(), a.generic_union(b.to_gset()));
    assert((a + b).to_infinite() =~= a.generic_union(b.to_gset()));
    if a.disjoint(b) {
        lemma_set_finite_from_type(a + b);
        lemma_set_generic_union_finite(a.to_gset(), b.to_gset());
        lemma_iset_ext_equal_eq((a + b).to_infinite(), a.generic_union(b.to_gset()));
        assert((a + b).to_infinite() == a.generic_union(b.to_gset()));
        assert(a.to_gset().disjoint(b.to_gset()));
        assert(a.generic_union(b.to_gset()).len() == a.len() + b.len());
        (a + b).to_gset().to_infinite_ensures();
        lemma_iset_to_from_gset((a + b).to_gset().to_infinite());
        assert((a + b).to_infinite().to_gset() == (a + b).to_gset().to_infinite());
        assert((a + b).to_infinite().len() == (a + b).len());
        assert((a + b).len() == a.len() + b.len());
    }
}

// This verified lemma used to be an axiom in the Dafny prelude
/// The length of the union between two sets added to the length of the intersection between the
/// two sets is equal to the sum of the lengths of the two sets.
pub broadcast proof fn lemma_set_intersect_union_lens<A, FINITE1: Finiteness, FINITE2: Finiteness>(
    a: GSet<A, FINITE1>,
    b: GSet<A, FINITE2>,
)
    requires
        a.finite(),
        b.finite(),
    ensures
        #[trigger] a.generic_union(b).len() + #[trigger] a.generic_intersect(b).len() == a.len()
            + b.len(),
    decreases a.len(),
{
    if a.len() == 0 {
        lemma_set_empty_equivalency_len(a);
        assert(a.generic_union(b) =~= b.to_infinite());
        assert(a.generic_intersect(b) =~= GSet::empty());
        lemma_gset_generic_union_finite(a, b);
        lemma_gset_generic_intersect_finite(a, b);
        b.congruent_len(b.to_infinite());
        a.generic_union(b).congruent_len(b.to_infinite());
        assert(a.generic_intersect(b).len() == 0) by {
            lemma_set_empty_equivalency_len(a.generic_intersect(b));
        }
        assert(a.len() == 0);
        assert(a.generic_union(b).len() + a.generic_intersect(b).len() == a.len() + b.len());
    } else {
        let x = a.choose();
        lemma_gset_choose_len(a);
        lemma_gset_remove_len(a, x);
        assert(a.remove(x).len() < a.len());
        lemma_set_intersect_union_lens(a.remove(x), b);
        if (b.contains(x)) {
            assert(a.remove(x).generic_union(b) =~= a.generic_union(b));
            assert(a.generic_intersect(b).remove(x) =~= a.remove(x).generic_intersect(b));
            let u = a.generic_union(b);
            let ur = a.remove(x).generic_union(b);
            let i = a.generic_intersect(b);
            let ir = a.remove(x).generic_intersect(b);
            lemma_gset_generic_union_finite(a, b);
            lemma_gset_generic_union_finite(a.remove(x), b);
            lemma_gset_generic_intersect_finite(a, b);
            lemma_gset_generic_intersect_finite(a.remove(x), b);
            ur.congruent_len(u);
            ir.congruent_len(i.remove(x));
            lemma_gset_generic_intersect(a, b, x);
            assert(i.contains(x));
            lemma_gset_remove_len(i, x);
            assert(ur.len() + ir.len() == a.remove(x).len() + b.len());
            assert(i.len() == ir.len() + 1);
            assert(a.len() == a.remove(x).len() + 1);
            assert(u.len() + i.len() == a.len() + b.len());
        } else {
            // b does not contain x
            assert(a.remove(x).generic_union(b) =~= a.generic_union(b).remove(x));
            // some trigger needed to reduce flakiness
            assert(a.generic_intersect(b) == a.remove(x).generic_intersect(b));
            let u = a.generic_union(b);
            let ur = a.remove(x).generic_union(b);
            let i = a.generic_intersect(b);
            lemma_gset_generic_union_finite(a, b);
            lemma_gset_generic_union_finite(a.remove(x), b);
            ur.congruent_len(u.remove(x));
            lemma_gset_generic_union(a, b, x);
            assert(u.contains(x));
            lemma_gset_remove_len(u, x);
            assert(ur.len() + i.len() == a.remove(x).len() + b.len());
            assert(u.len() == ur.len() + 1);
            assert(a.len() == a.remove(x).len() + 1);
            assert(u.len() + i.len() == a.len() + b.len());
        }
    }
}

// This verified lemma used to be an axiom in the Dafny prelude
/// The length of the set difference `A \ B` added to the length of the set difference `B \ A` added to
/// the length of the intersection `A ∩ B` is equal to the length of the union `A + B`.
///
/// The length of the set difference `A \ B` is equal to the length of `A` minus the length of the
/// intersection `A ∩ B`.
pub broadcast proof fn lemma_set_difference_len<A, FINITE1: Finiteness, FINITE2: Finiteness>(
    a: GSet<A, FINITE1>,
    b: GSet<A, FINITE2>,
)
    requires
        a.finite(),
        b.finite(),
    ensures
        (#[trigger] a.generic_difference(b).len() + b.generic_difference(a).len()
            + a.generic_intersect(b).len() == a.generic_union(b).len()) && (a.generic_difference(
            b,
        ).len() == a.len() - a.generic_intersect(b).len()),
    decreases 0nat,
{
    let d1 = a.generic_difference(b);
    let d2 = b.generic_difference(a);
    let i = a.generic_intersect(b);
    let u = a.generic_union(b);
    lemma_gset_generic_difference_finite(a, b);
    lemma_gset_generic_difference_finite(b, a);
    lemma_gset_generic_intersect_finite(a, b);
    lemma_gset_generic_union_finite(a, b);

    assert(d1.generic_union(i) =~= a.to_infinite()) by {
        assert forall|e: A| d1.generic_union(i).contains(e) == a.to_infinite().contains(e) by {
            lemma_gset_generic_union(d1, i, e);
            lemma_gset_generic_difference(a, b, e);
            lemma_gset_generic_intersect(a, b, e);
        }
        lemma_gset_ext_equal(d1.generic_union(i), a.to_infinite());
    }
    assert(d2.generic_union(i) =~= b.to_infinite()) by {
        assert forall|e: A| d2.generic_union(i).contains(e) == b.to_infinite().contains(e) by {
            lemma_gset_generic_union(d2, i, e);
            lemma_gset_generic_difference(b, a, e);
            lemma_gset_generic_intersect(a, b, e);
        }
        lemma_gset_ext_equal(d2.generic_union(i), b.to_infinite());
    }
    assert(d1.disjoint(i)) by {
        assert forall|e: A| d1.contains(e) implies !i.contains(e) by {
            lemma_gset_generic_difference(a, b, e);
            lemma_gset_generic_intersect(a, b, e);
        }
    }
    assert(d2.disjoint(i)) by {
        assert forall|e: A| d2.contains(e) implies !i.contains(e) by {
            lemma_gset_generic_difference(b, a, e);
            lemma_gset_generic_intersect(a, b, e);
        }
    }
    lemma_gset_disjoint_lens(d1, i);
    lemma_gset_disjoint_lens(d2, i);
    d1.generic_union(i).congruent_len(a.to_infinite());
    d2.generic_union(i).congruent_len(b.to_infinite());
    assert(d1.len() + i.len() == a.len());
    assert(d2.len() + i.len() == b.len());
    assert(d1.len() == a.len() - i.len());

    lemma_set_intersect_union_lens(a, b);
    assert(u.len() + i.len() == a.len() + b.len());
    assert(d1.len() + d2.len() + i.len() + i.len() == a.len() + b.len());
    assert(d1.len() + d2.len() + i.len() + i.len() == u.len() + i.len());
    assert(d1.len() + d2.len() + i.len() == u.len());
}

/// Properties of sets from the Dafny prelude (which were axioms in Dafny, but proven here in Verus)
#[deprecated = "Use `broadcast use group_set_properties` instead"]
pub proof fn lemma_set_properties<A, FINITE1: Finiteness, FINITE2: Finiteness>()
    ensures
        forall|a: GSet<A, FINITE1>, b: GSet<A, FINITE2>| #[trigger]
            a.generic_union(b).generic_union(b) == a.generic_union(b),  //from lemma_set_union_again1
        forall|a: GSet<A, FINITE1>, b: GSet<A, FINITE2>| #[trigger]
            a.generic_union(b).generic_union(a) == a.generic_union(b),  //from lemma_set_union_again2
        forall|a: GSet<A, FINITE1>, b: GSet<A, FINITE2>| #[trigger]
            (a.generic_intersect(b)).generic_intersect(b) == a.generic_intersect(b),  //from lemma_set_intersect_again1
        forall|a: GSet<A, FINITE1>, b: GSet<A, FINITE2>| #[trigger]
            (a.generic_intersect(b)).generic_intersect(a) == a.generic_intersect(b),  //from lemma_set_intersect_again2
        forall|s1: GSet<A, FINITE1>, s2: GSet<A, FINITE2>, a: A|
            s2.contains(a) ==> !s1.generic_difference(s2).contains(a),  //from lemma_set_difference2
        forall|a: GSet<A, FINITE1>, b: GSet<A, FINITE2>|
            #![trigger a.generic_union(b).generic_difference(a)]
            a.disjoint(b) ==> (a.generic_union(b).generic_difference(a) =~= b.to_infinite()
                && a.generic_union(b).generic_difference(b) =~= a.to_infinite()),  //from lemma_set_disjoint
        forall|s: GSet<A, FINITE1>| #[trigger]
            s.len() != 0 && s.finite() ==> exists|a: A| s.contains(a),  // half of lemma_set_empty_equivalency_len
        forall|a: GSet<A, FINITE1>, b: GSet<A, FINITE2>|
            (a.finite() && b.finite() && a.disjoint(b)) ==> #[trigger] a.generic_union(b).len()
                == a.len() + b.len(),  //from lemma_gset_disjoint_lens
        forall|a: GSet<A, FINITE1>, b: GSet<A, FINITE2>|
            (a.finite() && b.finite()) ==> #[trigger] a.generic_union(b).len()
                + #[trigger] a.generic_intersect(b).len() == a.len() + b.len(),  //from lemma_set_intersect_union_lens
        forall|a: GSet<A, FINITE1>, b: GSet<A, FINITE2>|
            (a.finite() && b.finite()) ==> ((#[trigger] a.generic_difference(b).len()
                + b.generic_difference(a).len() + a.generic_intersect(b).len() == a.generic_union(
                b,
            ).len()) && (a.generic_difference(b).len() == a.len() - a.generic_intersect(
                b,
            ).len())),  //from lemma_set_difference_len
{
    broadcast use group_set_properties;

    assert(forall|a: GSet<A, FINITE1>, b: GSet<A, FINITE2>| #[trigger]
        a.generic_union(b).generic_union(b) == a.generic_union(b));
    assert(forall|a: GSet<A, FINITE1>, b: GSet<A, FINITE2>| #[trigger]
        a.generic_union(b).generic_union(a) == a.generic_union(b));
    assert(forall|a: GSet<A, FINITE1>, b: GSet<A, FINITE2>| #[trigger]
        (a.generic_intersect(b)).generic_intersect(b) == a.generic_intersect(b));
    assert(forall|a: GSet<A, FINITE1>, b: GSet<A, FINITE2>| #[trigger]
        (a.generic_intersect(b)).generic_intersect(a) == a.generic_intersect(b));
}

pub broadcast group group_set_properties {
    lemma_set_union_again1,
    lemma_set_union_again2,
    lemma_set_intersect_again1,
    lemma_set_intersect_again2,
    lemma_set_difference2,
    lemma_gset_disjoint,
    lemma_set_disjoint,
    lemma_iset_disjoint,
    lemma_gset_disjoint_lens,
    lemma_set_disjoint_lens,
    lemma_iset_disjoint_lens,
    lemma_set_disjoint_lens_finite,
    lemma_set_intersect_union_lens,
    lemma_set_difference_len,
    // REVIEW: exclude from broadcast group if trigger is too free
    //         also note that some proofs in seq_lib requires this lemma
    lemma_set_empty_equivalency_len,
    lemma_set_union_finite_iff,
}

pub broadcast proof fn lemma_is_empty<A>(s: Set<A>)
    requires
        !(#[trigger] s.is_empty()),
    ensures
        exists|a: A| s.contains(a),
{
    assert(s.contains(s.choose()));
}

pub broadcast proof fn lemma_iset_not_empty<A>(s: ISet<A>)
    requires
        !(#[trigger] s.is_empty()),
    ensures
        exists|a: A| s.contains(a),
{
    if !(exists|a: A| s.contains(a)) {
        assert forall|a: A| #[trigger] s.contains(a) == ISet::<A>::empty().contains(a) by {
            if s.contains(a) {
                assert(false);
            }
            super::iset::lemma_iset_empty(a);
        }
        super::iset::lemma_iset_ext_equal(s, ISet::empty());
        assert(s =~= ISet::empty());
        assert(false);
    }
}

pub broadcast proof fn lemma_iset_strict_subset_witness<A>(sub: ISet<A>, sup: ISet<A>)
    requires
        #[trigger] sub.subset_of(sup),
        !(#[trigger] (sub =~= sup)),
    ensures
        exists|a: A| sup.contains(a) && !sub.contains(a),
{
    if !(exists|a: A| sup.contains(a) && !sub.contains(a)) {
        assert forall|a: A| #[trigger] sup.contains(a) == sub.contains(a) by {
            if sup.contains(a) {
                if !sub.contains(a) {
                    assert(exists|x: A| sup.contains(x) && !sub.contains(x));
                    assert(false);
                }
            } else {
                assert(!sub.contains(a)) by {
                    if sub.contains(a) {
                        assert(sub.subset_of(sup));
                        assert(sup.contains(a));
                        assert(false);
                    }
                }
            }
        }
        super::iset::lemma_iset_ext_equal(sub, sup);
        assert(sub =~= sup);
        assert(false);
    }
}

pub broadcast proof fn lemma_is_empty_len0<A>(s: Set<A>)
    ensures
        #[trigger] s.is_empty() <==> (s.finite() && s.len() == 0),
{
}

#[doc(hidden)]
#[verifier::inline]
pub open spec fn check_argument_is_set<A, S: SetLike<A>>(s: S) -> S {
    s
}

pub proof fn lemma_set_argument_ext_equal_eq<A, S: SetLike<A>>(
    s1: S,
    s2: S,
)
    ensures
        #[trigger] (s1 =~= s2) ==> s1 == s2,
{
    if s1 =~= s2 {
        assert(s1.as_gset() =~= s2.as_gset());
        super::gset::lemma_gset_ext_equal_eq(s1.as_gset(), s2.as_gset());
        assert(s1.as_gset() == s2.as_gset());
    }
}


/// Prove two sets equal by extensionality. Usage is:
///
/// ```rust
/// assert_sets_equal!(set1 == set2);
/// ```
///
/// or,
///
/// ```rust
/// assert_sets_equal!(set1 == set2, elem => {
///     // prove that set1.contains(elem) iff set2.contains(elem)
/// });
/// ```
#[macro_export]
macro_rules! assert_sets_equal {
    [$($tail:tt)*] => {
        $crate::vstd::prelude::verus_proof_macro_exprs!($crate::vstd::set_lib::assert_sets_equal_internal!($($tail)*))
    };
}

#[macro_export]
#[doc(hidden)]
macro_rules! assert_sets_equal_internal {
    (::vstd::prelude::spec_eq($s1:expr, $s2:expr)) => {
        $crate::vstd::set_lib::assert_sets_equal_internal!($s1, $s2)
    };
    (::vstd::prelude::spec_eq($s1:expr, $s2:expr), $elem:ident $( : $t:ty )? => $bblock:block) => {
        $crate::vstd::set_lib::assert_sets_equal_internal!($s1, $s2, $elem $( : $t )? => $bblock)
    };
    (crate::prelude::spec_eq($s1:expr, $s2:expr)) => {
        $crate::vstd::set_lib::assert_sets_equal_internal!($s1, $s2)
    };
    (crate::prelude::spec_eq($s1:expr, $s2:expr), $elem:ident $( : $t:ty )? => $bblock:block) => {
        $crate::vstd::set_lib::assert_sets_equal_internal!($s1, $s2, $elem $( : $t )? => $bblock)
    };
    (crate::verus_builtin::spec_eq($s1:expr, $s2:expr)) => {
        $crate::vstd::set_lib::assert_sets_equal_internal!($s1, $s2)
    };
    (crate::verus_builtin::spec_eq($s1:expr, $s2:expr), $elem:ident $( : $t:ty )? => $bblock:block) => {
        $crate::vstd::set_lib::assert_sets_equal_internal!($s1, $s2, $elem $( : $t )? => $bblock)
    };
    ($s1:expr, $s2:expr $(,)?) => {
        $crate::vstd::set_lib::assert_sets_equal_internal!($s1, $s2, elem => { })
    };
    ($s1:expr, $s2:expr, $elem:ident $( : $t:ty )? => $bblock:block) => {
        #[verifier::spec] let s1 = $crate::vstd::set_lib::check_argument_is_set($s1);
        #[verifier::spec] let s2 = $crate::vstd::set_lib::check_argument_is_set($s2);
        $crate::vstd::prelude::assert_by($crate::vstd::prelude::equal(s1, s2), {
            $crate::vstd::prelude::assert_forall_by(|$elem $( : $t )?| {
                $crate::vstd::prelude::ensures(
                    $crate::vstd::prelude::imply(s1.contains($elem), s2.contains($elem))
                    &&
                    $crate::vstd::prelude::imply(s2.contains($elem), s1.contains($elem))
                );
                { $bblock }
            });
            $crate::vstd::prelude::assert_($crate::vstd::prelude::ext_equal(s1, s2));
            $crate::vstd::set_lib::lemma_set_argument_ext_equal_eq(s1, s2);
        });
    }
}

impl<A> Set<A> {
    /// An automation-friendly way to construct finite sets.
    /// Start with a finite set and apply a mapping function:
    ///   Set::range(0, 10).map_flatten_by(/*fwd*/ |e| set!(e*3, e*5), /*rev*/ |b| )
    ///   actually I have no idea how this is supposed to work.
    pub open spec fn map_flatten_by<B>(
        self,
        fwd: spec_fn(A) -> Set<B>,
        rev: spec_fn(B) -> A,
    ) -> Set<B> {
        ISet::new(|b: B| self.contains(rev(b)) && fwd(rev(b)).contains(b)).to_finite()
    }
}

pub broadcast proof fn lemma_map_flatten_by<A, B>(
    sa: Set<A>,
    fwd: spec_fn(A) -> Set<B>,
    rev: spec_fn(B) -> A,
)
    ensures
        #![trigger sa.map_flatten_by(fwd, rev)]
        forall|b: B| #[trigger]
            sa.map_flatten_by(fwd, rev).contains(b) <==> sa.contains(rev(b)) && fwd(
                rev(b),
            ).contains(b),
{
    reveal(Set::map_flatten_by);
    reveal(ISet::infinite_flatten);
    let ib1 = ISet::new(|b: B| sa.contains(rev(b)) && fwd(rev(b)).contains(b));
    let ib2 = sa.map(fwd).to_infinite_deep().infinite_flatten();
    assert(ib2.finite()) by {
        sa.map(fwd).to_infinite_deep().infinite_flatten_preserves_finite();
    }
    assert(ib1.subset_of(ib2)) by {
        assert forall|b: B| ib1.to_gset().contains(b) implies ib2.to_gset().contains(b) by {
            assert(ib1.contains(b) == ib1.to_gset().contains(b));
            assert(ib2.contains(b) == ib2.to_gset().contains(b));
            if ib1.to_gset().contains(b) {
                let a = rev(b);
                lemma_iset_new(|bb: B| sa.contains(rev(bb)) && fwd(rev(bb)).contains(bb), b);
                assert(sa.contains(a) && fwd(a).contains(b));
                assert(sa.contains(a));
                lemma_set_map_contains(sa, fwd);
                assert(sa.map(fwd).contains(fwd(a)));
                assert(sa.map(fwd).to_infinite().contains(fwd(a)));
                lemma_iset_map_contains(sa.map(fwd).to_infinite(), |e: Set<B>| e.to_infinite());
                assert(sa.map(fwd).to_infinite_deep().contains(fwd(a).to_infinite()));
                assert(fwd(a).to_infinite().contains(b));
                assert(ib2.contains(b)) by {
                    reveal(ISet::infinite_flatten);
                    let s = fwd(a).to_infinite();
                    assert(sa.map(fwd).to_infinite_deep().contains(s) && s.contains(b));  // witness
                }
                assert(ib2.to_gset().contains(b));
            }
        }
    }
    lemma_set_subset_finite(ib2, ib1);
    assert(ib1.finite());
    lemma_set_finite_from_type(ib1.to_finite());
    assert forall|b: B| #[trigger] ib1.to_finite().contains(b) == ib1.contains(b) by {
        lemma_iset_to_finite_contains(ib1, b);
    }
}

pub broadcast group group_set_lib_default {
    lemma_is_empty,
    lemma_iset_not_empty,
    lemma_iset_strict_subset_witness,
    lemma_is_empty_len0,
    lemma_set_subset_finite,
    Set::lemma_map_by_finite,
    Set::lemma_map_flatten_by_finite,
    range_set_properties,
    full_set_properties,
    lemma_map_flatten_by,
}

pub use assert_sets_equal_internal;
pub use assert_sets_equal;

} // verus!
