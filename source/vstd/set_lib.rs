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

verus! {

broadcast use {
    super::set::group_set_lemmas,
    super::set::GSet::congruent_infiniteness,
    super::set::GSet::congruent_len,
};

//////////////////////////////////////////////////////////////////////////////
// Some general set properties
//////////////////////////////////////////////////////////////////////////////
impl<A, FINITE: Finiteness> GSet<A, FINITE> {
    /// Is `true` if called by a "full" set, i.e., a set containing every element of type `A`.
    pub open spec fn is_full(self) -> bool {
        self.to_infinite() == ISet::<A>::full()
    }

    /// Is `true` if called by an "empty" set, i.e., a set containing no elements and has length 0
    pub open spec fn is_empty(self) -> (b: bool) {
        self =~= GSet::<A, FINITE>::empty()
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
}

//////////////////////////////////////////////////////////////////////////////
// FINITE set properties
//////////////////////////////////////////////////////////////////////////////
impl<A> Set<A> {
    /// Converts a set into a sequence with an arbitrary ordering.
    pub open spec fn to_seq(self) -> Seq<A>
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
            let x = choose|x: A| self.contains(x);
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

        if self.len() == 1 {
            let x = choose|x: A| self.contains(x);
            assert(self.remove(x).insert(x) =~= self);
            assert(self.is_minimal(r, self.find_unique_minimal(r)));
        } else {
            let x = choose|x: A| self.contains(x);
            self.remove(x).find_unique_minimal_ensures(r);
            assert(self.remove(x).is_minimal(r, self.remove(x).find_unique_minimal(r)));
            let y = self.remove(x).find_unique_minimal(r);
            let min_updated = self.find_unique_minimal(r);
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
            assert forall|min_poss: A|
                self.is_minimal(r, min_poss) implies self.find_unique_minimal(r) == min_poss by {
                assert(self.remove(x).is_minimal(r, min_poss) || x == min_poss);
                assert(r(min_poss, self.find_unique_minimal(r))) by {}
            }
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
            let x = choose|x: A| self.contains(x);
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

        if self.len() == 1 {
            let x = choose|x: A| self.contains(x);
            assert(self.remove(x) =~= Set::<A>::empty());
            assert(self.contains(self.find_unique_maximal(r)));
        } else {
            let x = choose|x: A| self.contains(x);
            self.remove(x).find_unique_maximal_ensures(r);
            assert(self.remove(x).is_maximal(r, self.remove(x).find_unique_maximal(r)));
            assert(self.remove(x).insert(x) =~= self);
            let y = self.remove(x).find_unique_maximal(r);
            let max_updated = self.find_unique_maximal(r);
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
                    assert(self.is_maximal(r, self.find_unique_maximal(r)));
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
            assert forall|max_poss: A|
                self.is_maximal(r, max_poss) implies self.find_unique_maximal(r) == max_poss by {
                assert(self.remove(x).is_maximal(r, max_poss) || x == max_poss);
                assert(r(max_poss, self.find_unique_maximal(r)));
                assert(r(self.find_unique_maximal(r), max_poss));
            }
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
        if s.is_singleton() {
            s.lemma_singleton_size();
        }
        if s.len() == 1 {
            assert forall|x: A, y: A| s.contains(x) && s.contains(y) implies x == y by {
                let x = choose|x: A| s.contains(x);
                broadcast use group_set_properties;

                assert(s.remove(x).len() == 0);
                assert(s.insert(x) =~= s);
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
        broadcast use {GSet::congruent_infiniteness, GSet::congruent_len};

        let x: Set<A> = self;
        let xi = x.to_infinite();
        let fi = ISet::<A>::new(f);

        assert(x.congruent(xi));
        lemma_len_intersect(xi, fi);
        assert(xi.generic_intersect(fi) == xi.filter(f));  // trigger lemma_set_filter_is_intersect
        assert(x.filter(f).congruent(xi.filter(f)));
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
            #[trigger] self.generic_difference(s.insert(elt)).len() < self.generic_difference(
                s,
            ).len(),
    {
        self.generic_difference(s.insert(elt)).lemma_subset_not_in_lt(
            self.generic_difference(s),
            elt,
        );
    }

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
        assert(self.len() <= s2_no_elt.len()) by {
            lemma_len_subset(self, s2_no_elt);
        }
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
    pub proof fn lemma_map_union_commute<B>(self, t: Set<A>, f: spec_fn(A) -> B)
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
        let se = self.choose();
        assert forall|e| #![auto] self.infinite_flatten().contains(e) implies se.contains(e) by {
            let ce = choose|ce| self.contains(ce) && ce.contains(e);
            if ce != se {
                lemma_len_subset(iset![ce, se], self);
                assert(false);
            }
        }
        assert forall|e| #![auto] se.contains(e) implies self.infinite_flatten().contains(e) by {
            assert(self.contains(se) && se.contains(e));  // witness to infinite_flatten.contains
        }
        self.infinite_flatten().congruent_infiniteness(se);
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
            let rself = self.remove(se);
            let singleton = GSet::empty().insert(se);
            rself.infinite_flatten_preserves_finite();
            singleton.infinite_flatten_preserves_finite_singleton();

            // Dig up the existential witnesses for infinite_flatten(). (SMT found three of four
            // cases by itself.)
            assert(self.infinite_flatten() == rself.infinite_flatten().generic_union(
                singleton.infinite_flatten(),
            )) by {
                assert forall|e|
                    #![auto]
                    self.infinite_flatten().contains(
                        e,
                    ) implies rself.infinite_flatten().generic_union(
                    singleton.infinite_flatten(),
                ).contains(e) by {
                    let w = choose|w: ISet<A>| self.contains(w) && w.contains(e);
                    if w == se {
                        assert(singleton.contains(w));  // witness
                    }
                }
            }

            lemma_set_generic_union_finite(rself.infinite_flatten(), singleton.infinite_flatten());
            assert(self.infinite_flatten().finite());
        } else {
            // the outer set is empty, so the flattened set is empty
            assert(self.infinite_flatten() == GSet::<A, Infinite>::empty());  // trigger lemma_set_empty_finite
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

        assert forall|elem: A| lhs.contains(elem) implies rhs.contains(elem) by {
            if exists|s: ISet<A>| self.contains(s) && s.contains(elem) {
                let s = choose|s: ISet<A>| self.contains(s) && s.contains(elem);
                assert(self.insert(other).contains(s));
                assert(s.contains(elem));
            } else {
                assert(self.insert(other).contains(other));
            }
        }
    }
}

impl<A, FINITE: Finiteness> GSet<GSet<A, FINITE>, FINITE> {
    pub open spec fn to_infinite_deep(self) -> GSet<GSet<A, Infinite>, Infinite> {
        self.to_infinite().map(|e: GSet<A, FINITE>| e.to_infinite())
    }

    pub open spec fn flatten(self) -> GSet<A, FINITE> {
        self.to_infinite_deep().infinite_flatten().cast_finiteness::<FINITE>()
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
                    s.contains(orig) && f(orig) == Option::Some(r);
                assert(to_set(orig) == iset!{r});
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
        assert(lhs =~= rhs);
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
        broadcast use group_set_lemmas;

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
        assert(lhs =~= rhs);
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
        broadcast use GSet::lemma_infinite_filter_map_insert;

        let mapped = self.infinite_filter_map(f);
        if self.len() == 0 {
            assert(self.infinite_filter_map(f) =~= ISet::<B>::empty());
        } else {
            let elem = self.choose();
            self.remove(elem).lemma_infinite_filter_map_finite(f);
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
            self.filter_map(f).congruent(self.to_infinite().infinite_filter_map(f)),
    {
        assert(self.castable::<FINITE>());  // trigger lemma_self_castable
        self.apply_filter(f).to_infinite_deep().infinite_flatten_ensures::<FINITE>();
        self.apply_filter(f).to_infinite_deep().infinite_flatten().cast_finiteness_properties::<
            FINITE,
        >();

        self.to_infinite().apply_filter(f).to_infinite_deep().infinite_flatten_ensures::<FINITE>();

        assert forall|b: B|
            #![auto]
            self.filter_map(f).contains(b) implies self.to_infinite().infinite_filter_map(
            f,
        ).contains(b) by {
            let a = choose|a: A| self.contains(a) && f(a) == Some(b);
            assert(self.to_infinite().contains(a));  // witness

            let sb = GSet::<B, Infinite>::empty().insert(b);
            assert(self.to_infinite().apply_filter(f).contains(sb));  // witness
        }
        assert forall|b: B|
            #![auto]
            self.to_infinite().infinite_filter_map(f).contains(b) implies self.filter_map(
            f,
        ).contains(b) by {
            let ss = choose|ss|
                #![auto]
                self.to_infinite().apply_filter(f).contains(ss) && ss.contains(b);  // one of the infinite sets of Bs
            //
            let thingy6 = self.apply_filter(f);  // a FINITE set of FINITE sets of Bs
            let thingy7 = thingy6.to_infinite_deep();  // an infinite set of infinite sets of Bs
            let gs = GSet::empty().insert(b);
            assert(ss == gs.to_infinite());  // extn
            // witness to map inside to_infinite_deep
            assert(thingy6.to_infinite().contains(gs));
            assert(thingy7.contains(ss));  // trigger for infinite_flatten
        }
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
        GSet::lemma_infinite_filter_map_insert(s.to_infinite(), f, elem);
        assert(s.insert(elem).congruent(s.to_infinite().insert(elem)));
        s.filter_map_congruence(f);
        s.insert(elem).filter_map_congruence(f);
        assert(s.insert(elem).filter_map(f).congruent(
            s.to_infinite().insert(elem).infinite_filter_map(f),
        ));
        assert(s.filter_map(f).congruent(s.to_infinite().infinite_filter_map(f)));

    }

    pub broadcast proof fn lemma_filter_map_union<B>(self, f: spec_fn(A) -> Option<B>, t: Self)
        ensures
            #[trigger] self.generic_union(t).filter_map(f) == self.filter_map(f).generic_union(
                t.filter_map(f),
            ),
    {
        let iself = self.to_infinite();
        let it = t.to_infinite();

        self.generic_union(t).filter_map_congruence(f);
        self.filter_map_congruence(f);
        t.filter_map_congruence(f);

        // not sure what we're triggering here, but it's needed to finish the proof
        assert(self.filter_map(f).generic_union(t.filter_map(f)).congruent(
            iself.infinite_filter_map(f).union(it.infinite_filter_map(f)),
        ));

        iself.lemma_infinite_filter_map_union(f, it);  // the underlying lemma we're trying to generalize
    }
}

impl<A, FINITE: Finiteness> GSet<A, FINITE> {
    /// `map` preserves finiteness
    pub proof fn lemma_map_finite<B>(self, f: spec_fn(A) -> B)
        requires
            self.finite(),
        ensures
            self.map(f).finite(),
        decreases self.len(),
    {
        broadcast use group_set_lemmas;
        broadcast use lemma_set_empty_equivalency_len;

        if self.len() == 0 {
            assert(forall|elem: A| !(#[trigger] self.contains(elem)));
            assert forall|res: B| #[trigger] self.map(f).contains(res) implies false by {
                let x = choose|x: A| self.contains(x) && f(x) == res;
            }
            assert(self.map(f) =~= GSet::<B, FINITE>::empty());
        } else {
            let x = choose|x: A| self.contains(x);
            assert(self.map(f).contains(f(x)));
            self.remove(x).lemma_map_finite(f);
            assert(self.remove(x).insert(x) == self);
            assert(self.map(f) == self.remove(x).map(f).insert(f(x)));
        }
    }

    pub broadcast proof fn lemma_set_all_subset(self, s2: Set<A>, p: spec_fn(A) -> bool)
        requires
            #[trigger] self.subset_of(s2),
            s2.all(p),
        ensures
            #[trigger] self.all(p),
    {
        broadcast use group_set_lemmas;

    }
}

proof fn lemma_to_seq_to_set_id_recursive<A>(set: Set<A>, elem: A)
    requires
        set.finite(),
    ensures
        set.contains(elem) <==> set.to_seq().contains(elem),
    decreases set.len(),
{
    broadcast use {super::seq::group_seq_axioms, super::seq_lib::group_seq_properties};

    let c = set.choose();
    if elem != c {
        if set.contains(elem) || set.to_seq().contains(elem) {
            lemma_to_seq_to_set_id_recursive(set.remove(c), elem);
        }
    }
}

impl<A> Set<A> {
    /// Conversion to a sequence and back to a set is the identity function.
    pub broadcast proof fn lemma_to_seq_to_set_id(self)
        requires
            self.finite(),
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

            assert forall|x| #![auto] outer.contains(x) implies inner.contains(x) by {
                lemma_to_seq_to_set_id_recursive(self.remove(elem), x);
            }
            assert forall|x| #![auto] inner.contains(x) implies outer.contains(x) by {
                lemma_to_seq_to_set_id_recursive(self, x);
                assert(exists|i|
                    #![auto]
                    Set::int_range(0, self.to_seq().len() as int).contains(i) && self.to_seq()[i]
                        == x);  // witness
            }
            assert(self.to_seq().to_set() =~= self.remove(elem).to_seq().to_set().insert(elem));
        }
    }
}

/// Two sets are equal iff mapping `f` results in equal sets, if `f` is injective.
pub proof fn lemma_sets_eq_iff_injective_map_eq<T, S>(s1: Set<T>, s2: Set<T>, f: spec_fn(T) -> S)
    requires
        super::relations::injective(f),
    ensures
        (s1 == s2) <==> (s1.map(f) == s2.map(f)),
{
    broadcast use group_set_lemmas;

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
            assert(s.insert(a) == s);
        } else {
            assert(s.congruent(s.insert(a).to_finite().remove(a)));
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
        #[trigger] s1.generic_union(s2).finite() <==> s1.finite() && s2.finite(),
{
    if s1.generic_union(s2).finite() {
        lemma_set_union_finite_implies_sets_finite(s1, s2);
    }
}

pub proof fn lemma_set_union_finite_implies_sets_finite<A>(s1: ISet<A>, s2: ISet<A>)
    requires
        s1.generic_union(s2).finite(),
    ensures
        s1.finite(),
        s2.finite(),
    decreases s1.generic_union(s2).len(),
{
    broadcast use lemma_set_insert_finite;

    if s1.generic_union(s2) =~= iset![] {
        assert(s1 =~= iset![]);
        assert(s2 =~= iset![]);
    } else {
        let a = s1.generic_union(s2).choose();
        assert(s1.remove(a).generic_union(s2.remove(a)) == s1.generic_union(s2).remove(a));
        lemma_set_remove_len(s1.generic_union(s2), a);
        lemma_set_union_finite_implies_sets_finite(s1.remove(a), s2.remove(a));
        assert(forall|s: Set<A>|
            #![auto]
            s.remove(a).insert(a) == if s.contains(a) {
                s
            } else {
                s.insert(a)
            });
        if !s1.contains(a) {
            assert(s1.remove(a) == s1);
        }
        if !s2.contains(a) {
            assert(s2.remove(a) == s2);
        }
        lemma_set_insert_finite_iff(s1, a);
        lemma_set_insert_finite_iff(s2, a);
    }
}

/// The size of a union of two sets is less than or equal to the size of
/// both individual sets combined.
pub proof fn lemma_len_union<A>(s1: Set<A>, s2: Set<A>)
    requires
        s1.finite(),
        s2.finite(),
    ensures
        s1.generic_union(s2).len() <= s1.len() + s2.len(),
    decreases s1.len(),
{
    if s1.is_empty() {
        s1.generic_union(s2).congruent_len(s2);
    } else {
        let a = s1.choose();
        if s2.contains(a) {
            assert(s1.generic_union(s2) =~= s1.remove(a).generic_union(s2));
        } else {
            assert(s1.generic_union(s2).remove(a) =~= s1.remove(a).generic_union(s2));
        }
        lemma_len_union::<A>(s1.remove(a), s2);
    }
}

/// The size of a union of two sets is greater than or equal to the size of
/// both individual sets.
pub proof fn lemma_len_union_ind<A>(s1: Set<A>, s2: Set<A>)
    requires
        s1.finite(),
        s2.finite(),
    ensures
        s1.generic_union(s2).len() >= s1.len(),
        s1.generic_union(s2).len() >= s2.len(),
    decreases s2.len(),
{
    broadcast use group_set_properties;

    if s2.len() == 0 {
    } else {
        let y = choose|y: A| s2.contains(y);
        if s1.contains(y) {
            assert(s1.remove(y).generic_union(s2.remove(y)) =~= s1.generic_union(s2).remove(y));
            lemma_len_union_ind(s1.remove(y), s2.remove(y))
        } else {
            assert(s1.generic_union(s2.remove(y)) =~= s1.generic_union(s2).remove(y));
            lemma_len_union_ind(s1, s2.remove(y))
        }
    }
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
    if s1.is_empty() {
        assert(s1.generic_intersect(s2).congruent(s1));
    } else {
        let a = s1.choose();
        assert(s1.generic_intersect(s2).remove(a) =~= s1.remove(a).generic_intersect(s2));
        lemma_len_intersect::<A, FINITE, FINITE2>(s1.remove(a), s2);
        assert(s1.generic_intersect(s2).len() <= s1.len());
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
    let complement = s.generic_difference(sub);
    assert(sub =~= s.generic_difference(complement));
}

/// The size of the difference of finite set `s1` and set `s2` is less than or equal to the size of `s1`.
pub proof fn lemma_len_difference<A>(s1: ISet<A>, s2: ISet<A>)
    requires
        s1.finite(),
    ensures
        s1.generic_difference(s2).len() <= s1.len(),
    decreases s1.len(),
{
    if s1.is_empty() {
        assert(s1.generic_difference(s2) =~= s1);
    } else {
        let a = s1.choose();
        assert(s1.generic_difference(s2).remove(a) =~= s1.remove(a).generic_difference(s2));
        lemma_len_difference::<A>(s1.remove(a), s2);
    }
}

/// If a set solely contains integers in the range [a, b), then its size is
/// bounded by b - a.
pub proof fn lemma_int_range(lo: int, hi: int)
    requires
        lo <= hi,
    ensures
        Set::int_range(lo, hi).finite(),
        Set::int_range(lo, hi).len() == hi - lo,
    decreases hi - lo,
{
    if lo == hi {
        assert(Set::int_range(lo, hi) =~= Set::empty());
    } else {
        lemma_int_range(lo, hi - 1);
        assert(Set::int_range(lo, hi - 1).insert(hi - 1) =~= Set::int_range(lo, hi));
    }
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
    decreases x.len(),
{
    broadcast use group_set_properties;

    if x =~= Set::<A>::empty() {
    } else {
        let e = x.choose();
        lemma_subset_equality(x.remove(e), y.remove(e));
    }
}

/// If an injective function is applied to each element of a set to construct
/// another set, the two sets have the same size.
// the dafny original lemma reasons with partial function f
pub proof fn lemma_map_size<A, B>(x: Set<A>, y: Set<B>, f: spec_fn(A) -> B)
    requires
        injective(f),
        forall|a: A| x.contains(a) ==> y.contains(#[trigger] f(a)),
        forall|b: B| (#[trigger] y.contains(b)) ==> exists|a: A| x.contains(a) && f(a) == b,
        x.finite(),
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
        lemma_map_size(x.remove(a), y.remove(f(a)), f);
        assert(y == y.remove(f(a)).insert(f(a)));
    }
}

// This verified lemma used to be an axiom in the Dafny prelude
/// Taking the union of sets `a` and `b` and then taking the union of the result with `b`
/// is the same as taking the union of `a` and `b` once.
pub broadcast proof fn lemma_set_union_again1<A>(a: Set<A>, b: Set<A>)
    ensures
        #[trigger] a.generic_union(b).generic_union(b) =~= a.generic_union(b),
{
}

// This verified lemma used to be an axiom in the Dafny prelude
/// Taking the union of sets `a` and `b` and then taking the union of the result with `a`
/// is the same as taking the union of `a` and `b` once.
pub broadcast proof fn lemma_set_union_again2<A>(a: Set<A>, b: Set<A>)
    ensures
        #[trigger] a.generic_union(b).generic_union(a) =~= a.generic_union(b),
{
}

// This verified lemma used to be an axiom in the Dafny prelude
/// Taking the intersection of sets `a` and `b` and then taking the intersection of the result with `b`
/// is the same as taking the intersection of `a` and `b` once.
pub broadcast proof fn lemma_set_intersect_again1<A>(a: Set<A>, b: Set<A>)
    ensures
        #![trigger (a.generic_intersect(b)).generic_intersect(b)]
        (a.generic_intersect(b)).generic_intersect(b) =~= a.generic_intersect(b),
{
}

// This verified lemma used to be an axiom in the Dafny prelude
/// Taking the intersection of sets `a` and `b` and then taking the intersection of the result with `a`
/// is the same as taking the intersection of `a` and `b` once.
pub broadcast proof fn lemma_set_intersect_again2<A>(a: Set<A>, b: Set<A>)
    ensures
        #![trigger (a.generic_intersect(b)).generic_intersect(a)]
        (a.generic_intersect(b)).generic_intersect(a) =~= a.generic_intersect(b),
{
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
pub broadcast proof fn lemma_set_disjoint<A, FINITE: Finiteness, FINITE2: Finiteness>(
    a: GSet<A, FINITE>,
    b: GSet<A, FINITE2>,
)
    ensures
        #![trigger a.generic_union(b).generic_difference(a)]  //TODO: this might be too free
        a.disjoint(b) ==> (a.generic_union(b).generic_difference(a) =~= b.to_infinite()
            && a.generic_union(b).generic_difference(b) =~= a.to_infinite()),
{
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
        (s.len() == 0 <==> s == GSet::<A, FINITE>::empty()) && (s.len() != 0 ==> exists|x: A|
            s.contains(x)),
{
    assert(s.len() == 0 ==> s =~= GSet::empty()) by {
        if s.len() == 0 {
            assert(forall|a: A| !(GSet::<A, FINITE>::empty().contains(a)));
            assert(Set::<A>::empty().len() == 0);
            assert(Set::<A>::empty().len() == s.len());
            assert((exists|a: A| s.contains(a)) || (forall|a: A| !s.contains(a)));
            if exists|a: A| s.contains(a) {
                let a = s.choose();
                assert(s.remove(a).len() == s.len() - 1) by {
                    lemma_set_remove_len(s, a);
                }
            }
        }
    }
    assert(s.len() == 0 <== s =~= GSet::empty());
}

// This verified lemma used to be an axiom in the Dafny prelude
/// If sets `a` and `b` are disjoint, meaning they share no elements in common, then the length
/// of the union `a.union(b)` is equal to the sum of the lengths of `a` and `b`.
pub broadcast proof fn lemma_set_disjoint_lens<A, FINITE1: Finiteness, FINITE2: Finiteness>(
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
            assert(a.remove(x).generic_union(b) =~= a.generic_union(b).remove(x));
            lemma_set_disjoint_lens(a.remove(x), b);
        }
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
        assert(a.generic_union(b) =~= b.to_infinite());
        assert(a.generic_intersect(b) =~= GSet::empty());
        b.congruent_len(b.to_infinite());
    } else {
        let x = a.choose();
        lemma_set_intersect_union_lens(a.remove(x), b);
        if (b.contains(x)) {
            assert(a.remove(x).generic_union(b) =~= a.generic_union(b));
            assert(a.generic_intersect(b).remove(x) =~= a.remove(x).generic_intersect(b));
        } else {
            // b does not contain x
            assert(a.remove(x).generic_union(b) =~= a.generic_union(b).remove(x));
            // some trigger needed to reduce flakiness
            assert(a.generic_intersect(b) == a.remove(x).generic_intersect(b));
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
    decreases a.len(),
{
    if a.len() == 0 {
        lemma_set_empty_equivalency_len(a);
        assert(a.generic_difference(b) =~= GSet::empty());
        assert(b.generic_difference(a) =~= b.to_infinite());
        assert(a.generic_intersect(b) =~= GSet::empty());
        assert(a.generic_union(b) =~= b.to_infinite());
    } else {
        let x = a.choose();
        lemma_set_difference_len(a.remove(x), b);
        if b.contains(x) {
            assert(a.generic_intersect(b).remove(x) =~= a.remove(x).generic_intersect(b));
            assert(a.remove(x).generic_difference(b) =~= a.generic_difference(b));
            assert(b.generic_difference(a.remove(x)).remove(x) =~= b.generic_difference(a));
            assert(a.remove(x).generic_union(b) =~= a.generic_union(b));
        } else {
            assert(a.remove(x).generic_union(b) =~= a.generic_union(b).remove(x));
            assert(a.remove(x).generic_difference(b) =~= a.generic_difference(b).remove(x));
            assert(b.generic_difference(a.remove(x)) =~= b.generic_difference(a));
            assert(a.remove(x).generic_intersect(b) =~= a.generic_intersect(b));
        }
    }
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
                == a.len() + b.len(),  //from lemma_set_disjoint_lens
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
    lemma_set_disjoint,
    lemma_set_disjoint_lens,
    lemma_set_intersect_union_lens,
    lemma_set_difference_len,
    // REVIEW: exclude from broadcast group if trigger is too free
    //         also note that some proofs in seq_lib requires this lemma
    lemma_set_empty_equivalency_len,
}

pub broadcast proof fn lemma_is_empty<A>(s: Set<A>)
    requires
        !(#[trigger] s.is_empty()),
    ensures
        exists|a: A| s.contains(a),
{
    assert(s.contains(s.choose()));
}

pub broadcast proof fn lemma_is_empty_len0<A>(s: Set<A>)
    ensures
        #[trigger] s.is_empty() <==> (s.finite() && s.len() == 0),
{
}

#[doc(hidden)]
#[verifier::inline]
pub open spec fn check_argument_is_set<A, FINITE: Finiteness>(s: GSet<A, FINITE>) -> GSet<
    A,
    FINITE,
> {
    s
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
        });
    }
}

pub broadcast group group_set_lib_default {
    lemma_is_empty,
    lemma_is_empty_len0,
    lemma_set_subset_finite,
}

pub use assert_sets_equal_internal;
pub use assert_sets_equal;

} // verus!
