#[allow(unused_imports)]
use super::multiset::Multiset;
#[allow(unused_imports)]
use super::pervasive::*;
use super::prelude::Seq;
#[allow(unused_imports)]
// use super::prelude::*;
use builtin_macros::verus;
use builtin::int;
use builtin::admit;
use builtin::SpecOrd;
use builtin::SpecAdd;
use builtin::SpecSub;

#[allow(unused_imports)]
use super::relations::*;
#[allow(unused_imports)]
use super::set::*;

verus! {

broadcast use super::set::group_set_lemmas;

//////////////////////////////////////////////////////////////////////////////
// Some general set properties
//////////////////////////////////////////////////////////////////////////////

impl<A, const Finite:bool> GSet<A, Finite> {
    /// Is `true` if called by a "full" set, i.e., a set containing every element of type `A`.
    pub open spec fn is_full(self) -> bool {
        self.to_infinite() == ISet::<A>::full()
    }

    /// Is `true` if called by an "empty" set, i.e., a set containing no elements and has length 0
    pub open spec fn is_empty(self) -> (b: bool) {
        self =~= GSet::<A, Finite>::empty()
    }

    /// A singleton set has at least one element and any two elements are equal.
    pub open spec fn is_singleton(self) -> bool {
        &&& self.len() > 0
        &&& (forall|x: A, y: A| self.contains(x) && self.contains(y) ==> x == y)
    }

    /// An element in an ordered set is called a least element (or a minimum), if it is less than
    /// every other element of the set.
    ///
    /// change f to leq bc it is a relation. also these are an ordering relation
    pub open spec fn is_least(self, leq: spec_fn(A, A) -> bool, min: A) -> bool {
        self.contains(min) && forall|x: A| self.contains(x) ==> #[trigger] leq(min, x)
    }

    /// An element in an ordered set is called a minimal element, if no other element is less than it.
    pub open spec fn is_minimal(self, leq: spec_fn(A, A) -> bool, min: A) -> bool {
        self.contains(min) && forall|x: A|
            self.contains(x) && #[trigger] leq(x, min) ==> #[trigger] leq(min, x)
    }

    /// An element in an ordered set is called a greatest element (or a maximum), if it is greater than
    ///every other element of the set.
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
// Finite set properties
//////////////////////////////////////////////////////////////////////////////

impl<A> Set<A> {
    /// Converts a set into a sequence with an arbitrary ordering.
    pub open spec fn to_seq(self) -> Seq<A>
        decreases self.len(),
        via Self::decreases_proof
    {
        if self.len() == 0 {
            Seq::<A>::empty()
        } else {
            let x = self.choose();
            Seq::<A>::empty().push(x) + self.remove(x).to_seq()
        }
    }

    // Helper function to prove termination of function to_seq
    #[via_fn]
    proof fn decreases_proof(self) {
        broadcast use group_set_properties;

        if self.len() > 0 {
            let x = self.choose();
            assert(self.contains(x));
            assert(self.remove(x).len() < self.len());
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
        via Self::prove_decrease_min_unique
    {
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

    #[via_fn]
    proof fn prove_decrease_min_unique(self, r: spec_fn(A, A) -> bool) {
        broadcast use group_set_properties;

        if self.len() > 0 {
            let x = self.choose();
            assert(self.contains(x));
            assert(self.remove(x).len() < self.len());
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
                assert(r(min_poss, self.find_unique_minimal(r)));
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
        via Self::prove_decrease_max_unique
    {
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

    #[via_fn]
    proof fn prove_decrease_max_unique(self, r: spec_fn(A, A) -> bool) {
        broadcast use group_set_properties;

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
    // TODO(jonh): why should this be limited to finite sets? Are Multisets finite by type?
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
        let x: Set<A> = self;
        let xi = x.to_infinite();
        let fi = ISet::<A>::new(f);
        
        congruent_infiniteness(x, x.to_infinite());
        lemma_len_intersect(xi, fi);
        congruent_len(x, xi);
        assert( xi.intersect(fi) == xi.filter(f) ); // trigger lemma_set_filter_is_intersect
        congruent_len(x.filter(f), xi.filter(f));
    }
}

//////////////////////////////////////////////////////////////////////////////
// Ordering properties (available on both flavors of set)
//////////////////////////////////////////////////////////////////////////////

impl<A, const Finite:bool> GSet<A, Finite> {
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
            self.is_greatest(r, max) && self.is_greatest(r, max_prime) implies max
            == max_prime by {
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
}

/// The result of inserting an element `a` into a set `s` is finite iff `s` is finite.
pub broadcast proof fn lemma_set_insert_finite_iff<A>(s: ISet<A>, a: A)
    ensures
        #[trigger] s.insert(a).finite() <==> s.finite(),
{
    // apppeal to finite-typed versions
    if s.insert(a).finite() {
        if s.contains(a) {
            assert( s.insert(a) == s );
        } else {
            congruent_infiniteness( s.insert(a).to_finite().remove(a), s );
        }
    }
    if s.finite() {
        congruent_infiniteness( s.to_finite().insert(a), s.insert(a) );
    }

    // Original proof appeals to finite-preservation lemmas on infinite sets
//     if s.insert(a).finite() {
//         if s.contains(a) {
//             assert(s == s.insert(a));
//         } else {
//             assert(s == s.insert(a).remove(a));
//         }
//     }
//     assert(s.insert(a).finite() ==> s.finite());
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
        #[trigger] s1.union(s2).finite() <==> s1.finite() && s2.finite(),
{
    if s1.union(s2).finite() {
        lemma_set_union_finite_implies_sets_finite(s1, s2);
    }
}

pub proof fn lemma_set_union_finite_implies_sets_finite<A>(s1: ISet<A>, s2: ISet<A>)
    requires
        s1.union(s2).finite(),
    ensures
        s1.finite(),
        s2.finite(),
    decreases s1.union(s2).len(),
{
    broadcast use lemma_set_insert_finite;
    if s1.union(s2) =~= set![] {
        assert(s1 =~= set![]);
        assert(s2 =~= set![]);
    } else {
        let a = s1.union(s2).choose();
        assert(s1.remove(a).union(s2.remove(a)) == s1.union(s2).remove(a));
        lemma_set_remove_len(s1.union(s2), a);
        lemma_set_union_finite_implies_sets_finite(s1.remove(a), s2.remove(a));
        assert(forall|s: Set<A>|
            #![auto]
            s.remove(a).insert(a) == if s.contains(a) {
                s
            } else {
                s.insert(a)
            });
        if !s1.contains(a) { assert( s1.remove(a) == s1 ); }
        if !s2.contains(a) { assert( s2.remove(a) == s2 ); }
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
        s1.union(s2).len() <= s1.len() + s2.len(),
    decreases s1.len(),
{
    if s1.is_empty() {
       congruent_len(s1.union(s2), s2);
    } else {
        let a = s1.choose();
        if s2.contains(a) {
            assert(s1.union(s2) =~= s1.remove(a).union(s2));
        } else {
            assert(s1.union(s2).remove(a) =~= s1.remove(a).union(s2));
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
        s1.union(s2).len() >= s1.len(),
        s1.union(s2).len() >= s2.len(),
    decreases s2.len(),
{
    broadcast use group_set_properties;

    if s2.len() == 0 {
    } else {
        let y = choose|y: A| s2.contains(y);
        if s1.contains(y) {
            assert(s1.remove(y).union(s2.remove(y)) =~= s1.union(s2).remove(y));
            lemma_len_union_ind(s1.remove(y), s2.remove(y))
        } else {
            assert(s1.union(s2.remove(y)) =~= s1.union(s2).remove(y));
            lemma_len_union_ind(s1, s2.remove(y))
        }
    }
}

/// The size of the intersection of finite set `s1` and set `s2` is less than or equal to the size of `s1`.
pub proof fn lemma_len_intersect<A>(s1: ISet<A>, s2: ISet<A>)
    requires
        s1.finite(),
    ensures
        s1.intersect(s2).len() <= s1.len(),
    decreases s1.len(),
{
    if s1.is_empty() {
        assert(s1.intersect(s2) =~= s1);
    } else {
        let a = s1.choose();
        assert(s1.intersect(s2).remove(a) =~= s1.remove(a).intersect(s2));
        lemma_len_intersect::<A>(s1.remove(a), s2);
    }
}

/// If `s1` is a subset of finite set `s2`, then the size of `s1` is less than or equal to
/// the size of `s2` and `s1` must be finite.
pub proof fn lemma_len_subset<A>(s1: ISet<A>, s2: ISet<A>)
    requires
        s2.finite(),
        s1.subset_of(s2),
    ensures
        s1.len() <= s2.len(),
        s1.finite(),
{
    lemma_len_intersect::<A>(s2, s1);
    assert(s2.intersect(s1) =~= s1);
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
    let complement = s.difference(sub);
    assert(sub =~= s.difference(complement));
}

/// The size of the difference of finite set `s1` and set `s2` is less than or equal to the size of `s1`.
pub proof fn lemma_len_difference<A>(s1: ISet<A>, s2: ISet<A>)
    requires
        s1.finite(),
    ensures
        s1.difference(s2).len() <= s1.len(),
    decreases s1.len(),
{
    if s1.is_empty() {
        assert(s1.difference(s2) =~= s1);
    } else {
        let a = s1.choose();
        assert(s1.difference(s2).remove(a) =~= s1.remove(a).difference(s2));
        lemma_len_difference::<A>(s1.remove(a), s2);
    }
}

/// If a set solely contains integers in the range [a, b), then its size is
/// bounded by b - a.
pub proof fn lemma_int_range(lo: int, hi: int)
    requires
        lo <= hi,
    ensures
        set_int_range(lo, hi).finite(),
        set_int_range(lo, hi).len() == hi - lo,
    decreases hi - lo,
{
    if lo == hi {
        assert(set_int_range(lo, hi) =~= Set::empty());
    } else {
        lemma_int_range(lo, hi - 1);
        assert(set_int_range(lo, hi - 1).insert(hi - 1) =~= set_int_range(lo, hi));
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
        y.finite(),
    ensures
        x.len() == y.len(),
    decreases x.len(),
{
    broadcast use group_set_properties;

    if x.len() != 0 {
        let a = x.choose();
        lemma_map_size(x.remove(a), y.remove(f(a)), f);
    }
}

// This verified lemma used to be an axiom in the Dafny prelude
/// Taking the union of sets `a` and `b` and then taking the union of the result with `b`
/// is the same as taking the union of `a` and `b` once.
pub broadcast proof fn lemma_set_union_again1<A>(a: Set<A>, b: Set<A>)
    ensures
        #[trigger] a.union(b).union(b) =~= a.union(b),
{
}

// This verified lemma used to be an axiom in the Dafny prelude
/// Taking the union of sets `a` and `b` and then taking the union of the result with `a`
/// is the same as taking the union of `a` and `b` once.
pub broadcast proof fn lemma_set_union_again2<A>(a: Set<A>, b: Set<A>)
    ensures
        #[trigger] a.union(b).union(a) =~= a.union(b),
{
}

// This verified lemma used to be an axiom in the Dafny prelude
/// Taking the intersection of sets `a` and `b` and then taking the intersection of the result with `b`
/// is the same as taking the intersection of `a` and `b` once.
pub broadcast proof fn lemma_set_intersect_again1<A>(a: Set<A>, b: Set<A>)
    ensures
        #![trigger (a.intersect(b)).intersect(b)]
        (a.intersect(b)).intersect(b) =~= a.intersect(b),
{
}

// This verified lemma used to be an axiom in the Dafny prelude
/// Taking the intersection of sets `a` and `b` and then taking the intersection of the result with `a`
/// is the same as taking the intersection of `a` and `b` once.
pub broadcast proof fn lemma_set_intersect_again2<A>(a: Set<A>, b: Set<A>)
    ensures
        #![trigger (a.intersect(b)).intersect(a)]
        (a.intersect(b)).intersect(a) =~= a.intersect(b),
{
}

// This verified lemma used to be an axiom in the Dafny prelude
/// If set `s2` contains element `a`, then the set difference of `s1` and `s2` does not contain `a`.
pub broadcast proof fn lemma_set_difference2<A, const Finite1: bool, const Finite2: bool>(s1: GSet<A, Finite1>, s2: GSet<A, Finite2>, a: A)
    ensures
        #![trigger s1.difference(s2).contains(a)]
        s2.contains(a) ==> !s1.difference(s2).contains(a),
{
}

// This verified lemma used to be an axiom in the Dafny prelude
/// If sets `a` and `b` are disjoint, meaning they have no elements in common, then the set difference
/// of `a.union(b)` and `b` is equal to `a` and the set difference of `a.union(b)` and `a` is equal to `b`.
pub broadcast proof fn lemma_set_disjoint<A, const Finite: bool, const Finite2: bool>(a: GSet<A, Finite>, b: GSet<A, Finite2>)
    ensures
        #![trigger a.union(b).difference(a)]  //TODO: this might be too free
        a.disjoint(b) ==> (a.union(b).difference(a) =~= b.to_infinite() && a.union(b).difference(b) =~= a.to_infinite()),
{
}

// This verified lemma used to be an axiom in the Dafny prelude
// Dafny encodes the second clause with a single directional, although
// it should be fine with both directions?
// REVIEW: excluded from broadcast group if trigger is too free
//         also not that some proofs in seq_lib requires this lemma
/// Set `s` has length 0 if and only if it is equal to the empty set. If `s` has length greater than 0,
/// Then there must exist an element `x` such that `s` contains `x`.
pub broadcast proof fn lemma_set_empty_equivalency_len<A, const Finite: bool>(s: GSet<A, Finite>)
    requires
        s.finite(),
    ensures
        #![trigger s.len()]
        (s.len() == 0 <==> s == GSet::<A, Finite>::empty()) && (s.len() != 0 ==> exists|x: A| s.contains(x)),
{
    assert(s.len() == 0 ==> s =~= GSet::empty()) by {
        if s.len() == 0 {
            assert(forall|a: A| !(GSet::<A, Finite>::empty().contains(a)));
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
pub broadcast proof fn lemma_set_disjoint_lens<A, const Finite1: bool, const Finite2: bool>(a: GSet<A, Finite1>, b: GSet<A, Finite2>)
    requires
        a.finite(),
        b.finite(),
    ensures
        a.disjoint(b) ==> #[trigger] a.union(b).len() == a.len() + b.len(),
    decreases a.len(),
{
    if a.len() == 0 {
        lemma_set_empty_equivalency_len(a);
        assert(a.union(b) =~= b.to_infinite());
        congruent_len(b, b.to_infinite());
    } else {
        if a.disjoint(b) {
            let x = a.choose();
            assert(a.remove(x).union(b) =~= a.union(b).remove(x));
            // TODO(jonh): Ask verus folks why I need these when we have a group use above
            broadcast use lemma_set_remove_finite;
            broadcast use lemma_set_remove_len;
            broadcast use lemma_set_union_finite;
            lemma_set_disjoint_lens(a.remove(x), b);
        }
    }
}

// This verified lemma used to be an axiom in the Dafny prelude
/// The length of the union between two sets added to the length of the intersection between the
/// two sets is equal to the sum of the lengths of the two sets.
pub broadcast proof fn lemma_set_intersect_union_lens<A, const Finite1: bool, const Finite2: bool>(a: GSet<A, Finite1>, b: GSet<A, Finite2>)
    requires
        a.finite(),
        b.finite(),
    ensures
        #[trigger] a.union(b).len() + #[trigger] a.intersect(b).len() == a.len() + b.len(),
    decreases a.len(),
{
    if a.len() == 0 {
        assert(a.union(b) =~= b.to_infinite());
        assert(a.intersect(b) =~= GSet::empty());
        congruent_len(b, b.to_infinite());
    } else {
        let x = a.choose();
        lemma_set_intersect_union_lens(a.remove(x), b);
        if (b.contains(x)) {
            assert(a.remove(x).union(b) =~= a.union(b));
            assert(a.intersect(b).remove(x) =~= a.remove(x).intersect(b));
        } else {
            // b does not contain x
            assert(a.remove(x).union(b) =~= a.union(b).remove(x));
            // some trigger needed to reduce flakiness
            assert( a.intersect(b) == a.remove(x).intersect(b) );
        }
    }
}

// This verified lemma used to be an axiom in the Dafny prelude
/// The length of the set difference `A \ B` added to the length of the set difference `B \ A` added to
/// the length of the intersection `A ∩ B` is equal to the length of the union `A + B`.
///
/// The length of the set difference `A \ B` is equal to the length of `A` minus the length of the
/// intersection `A ∩ B`.
pub broadcast proof fn lemma_set_difference_len<A, const Finite1: bool, const Finite2: bool>(a: GSet<A, Finite1>, b: GSet<A, Finite2>)
    requires
        a.finite(),
        b.finite(),
    ensures
        (#[trigger] a.difference(b).len() + b.difference(a).len() + a.intersect(b).len() == a.union(b).len()) && (a.difference(b).len() == a.len() - a.intersect(b).len()),
    decreases a.len(),
{
    if a.len() == 0 {
        lemma_set_empty_equivalency_len(a);
        assert(a.difference(b) =~= GSet::empty());
        assert(b.difference(a) =~= b.to_infinite());
        assert(a.intersect(b) =~= GSet::empty());
        assert(a.union(b) =~= b.to_infinite());
    } else {
        let x = a.choose();
        lemma_set_difference_len(a.remove(x), b);
        if b.contains(x) {
            assert(a.intersect(b).remove(x) =~= a.remove(x).intersect(b));
            assert(a.remove(x).difference(b) =~= a.difference(b));
            assert(b.difference(a.remove(x)).remove(x) =~= b.difference(a));
            assert(a.remove(x).union(b) =~= a.union(b));
        } else {
            assert(a.remove(x).union(b) =~= a.union(b).remove(x));
            assert(a.remove(x).difference(b) =~= a.difference(b).remove(x));
            assert(b.difference(a.remove(x)) =~= b.difference(a));
            assert(a.remove(x).intersect(b) =~= a.intersect(b));
        }
    }
}

/// Properties of sets from the Dafny prelude (which were axioms in Dafny, but proven here in Verus)
#[deprecated = "Use `broadcast use group_set_properties` instead"]
pub proof fn lemma_set_properties<A, const Finite1: bool, const Finite2: bool>()
    ensures
        forall|a: GSet<A, Finite1>, b: GSet<A, Finite2>| #[trigger] a.union(b).union(b) == a.union(b),  //from lemma_set_union_again1
        forall|a: GSet<A, Finite1>, b: GSet<A, Finite2>| #[trigger] a.union(b).union(a) == a.union(b),  //from lemma_set_union_again2
        forall|a: GSet<A, Finite1>, b: GSet<A, Finite2>| #[trigger] (a.intersect(b)).intersect(b) == a.intersect(b),  //from lemma_set_intersect_again1
        forall|a: GSet<A, Finite1>, b: GSet<A, Finite2>| #[trigger] (a.intersect(b)).intersect(a) == a.intersect(b),  //from lemma_set_intersect_again2
        forall|s1: GSet<A, Finite1>, s2: GSet<A, Finite2>, a: A| s2.contains(a) ==> !s1.difference(s2).contains(a),  //from lemma_set_difference2
        forall|a: GSet<A, Finite1>, b: GSet<A, Finite2>|
            #![trigger a.union(b).difference(a)]
            a.disjoint(b) ==> (a.union(b).difference(a) =~= b.to_infinite() && a.union(b).difference(b) =~= a.to_infinite()),  //from lemma_set_disjoint
        forall|s: GSet<A, Finite1>| #[trigger] s.len() != 0 && s.finite() ==> exists|a: A| s.contains(a),  // half of lemma_set_empty_equivalency_len
        forall|a: GSet<A, Finite1>, b: GSet<A, Finite2>|
            (a.finite() && b.finite() && a.disjoint(b)) ==> #[trigger] a.union(b).len() == a.len()
                + b.len(),  //from lemma_set_disjoint_lens
        forall|a: GSet<A, Finite1>, b: GSet<A, Finite2>|
            (a.finite() && b.finite()) ==> #[trigger] a.union(b).len() + #[trigger] a.intersect(
                b,
            ).len() == a.len() + b.len(),  //from lemma_set_intersect_union_lens
        forall|a: GSet<A, Finite1>, b: GSet<A, Finite2>|
            (a.finite() && b.finite()) ==> ((#[trigger] a.difference(b).len() + b.difference(
                a,
            ).len() + a.intersect(b).len() == a.union(b).len()) && (a.difference(b).len() == a.len()
                - a.intersect(b).len())),  //from lemma_set_difference_len
{
    broadcast use group_set_properties;

    // TODO(verus): For some reason I now have to explicitly re-trigger extensionality expressions sitting in ensures
    assert( forall|a: GSet<A, Finite1>, b: GSet<A, Finite2>| #[trigger] a.union(b).union(b) == a.union(b) );
    assert( forall|a: GSet<A, Finite1>, b: GSet<A, Finite2>| #[trigger] a.union(b).union(a) == a.union(b) );
    assert( forall|a: GSet<A, Finite1>, b: GSet<A, Finite2>| #[trigger] (a.intersect(b)).intersect(b) == a.intersect(b) );
    assert( forall|a: GSet<A, Finite1>, b: GSet<A, Finite2>| #[trigger] (a.intersect(b)).intersect(a) == a.intersect(b) );
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
    admit();  // REVIEW, should this be in `set`, or have a proof?
}

pub broadcast proof fn lemma_is_empty_len0<A>(s: Set<A>)
    ensures
        #[trigger] s.is_empty() <==> (s.finite() && s.len() == 0),
{
}

#[doc(hidden)]
#[verifier::inline]
pub open spec fn check_argument_is_set<A, const Finite: bool>(s: GSet<A, Finite>) -> GSet<A, Finite> {
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
        ::builtin_macros::verus_proof_macro_exprs!($crate::vstd::set_lib::assert_sets_equal_internal!($($tail)*))
    };
}

#[macro_export]
#[doc(hidden)]
macro_rules! assert_sets_equal_internal {
    (::builtin::spec_eq($s1:expr, $s2:expr)) => {
        $crate::vstd::set_lib::assert_sets_equal_internal!($s1, $s2)
    };
    (::builtin::spec_eq($s1:expr, $s2:expr), $elem:ident $( : $t:ty )? => $bblock:block) => {
        $crate::vstd::set_lib::assert_sets_equal_internal!($s1, $s2, $elem $( : $t )? => $bblock)
    };
    (crate::builtin::spec_eq($s1:expr, $s2:expr)) => {
        $crate::vstd::set_lib::assert_sets_equal_internal!($s1, $s2)
    };
    (crate::builtin::spec_eq($s1:expr, $s2:expr), $elem:ident $( : $t:ty )? => $bblock:block) => {
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
