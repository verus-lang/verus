#[allow(unused_imports)]
use super::iset::*;
#[allow(unused_imports)]
use super::multiset::Multiset;
#[allow(unused_imports)]
use super::pervasive::*;
use super::prelude::Seq;
#[allow(unused_imports)]
use super::prelude::*;
#[allow(unused_imports)]
use super::relations::*;
#[allow(unused_imports)]
use super::set::*;

verus! {

broadcast use {
    super::iset::group_iset_lemmas,
    super::set::group_set_lemmas,
};

impl<A> Set<A> {
    /// Is `true` if called by an "empty" set, i.e., a set containing no elements and has length 0
    pub open spec fn is_empty(self) -> (b: bool) {
        self =~= Set::<A>::empty()
    }

    /// Returns the set contains an element `f(x)` for every element `x` in `self`.
    pub closed spec fn map<B>(self, f: spec_fn(A) -> B) -> Set<B> {
        Set::new_from_iset(self.to_iset().map(f)).unwrap()
    }

    pub broadcast proof fn lemma_map_contains<B>(self, f: spec_fn(A) -> B, b: B)
        ensures
            #[trigger] self.map(f).contains(b) <==> exists|a: A| self.contains(a) && b == f(a)
    {
        self.to_iset().lemma_map_finite(f);
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
    pub closed spec fn map_by<B>(self, fwd: spec_fn(A) -> B, rev: spec_fn(B) -> A) -> Set<B>
        recommends
            forall|a: A| self.contains(a) ==> rev(fwd(a)) == a,
    {
        Set::new_from_iset(self.to_iset().map_by(fwd, rev)).unwrap()
    }

    pub broadcast proof fn lemma_map_by_contains<B>(self, fwd: spec_fn(A) -> B, rev: spec_fn(B) -> A, b: B)
        ensures
            #[trigger] self.map_by(fwd, rev).contains(b) <==> self.contains(rev(b)) && b == fwd(rev(b)),
        decreases self.len(),
    {
        self.to_iset().lemma_map_by_finite(fwd, rev);
    }

    /// Similar to `Set::map_by`, but the forward function returns `Set<B>` rather than `B`,
    /// and `map_flatten_by` flattens the final result from `Set<Set<B>>` to just `Set<B>`.
    /// This can be easier to work with in proofs than calling `map` and `flatten` separately,
    /// since `map` and `flatten` introduce "exists", while `map_flatten_by` does not.
    /// Also see the `set_build!` macro for a convenient interface to `map_flatten_by`.
    pub closed spec fn map_flatten_by<B>(
        self,
        fwd: spec_fn(A) -> Set<B>,
        rev: spec_fn(B) -> A,
    ) -> Set<B>
        recommends
            forall|a: A, b: B| #[trigger]
                self.contains(a) && fwd(a).contains(b) ==> #[trigger] rev(b) == a,
    {
        Set::new(|b: B| self.contains(rev(b)) && fwd(rev(b)).contains(b)).unwrap()
    }

    proof fn lemma_map_flatten_by_finite<B>(
        self,
        fwd: spec_fn(A) -> Set<B>,
        rev: spec_fn(B) -> A,
    )
        requires
            forall|a: A, b: B| #[trigger]
                self.contains(a) && fwd(a).contains(b) ==> #[trigger] rev(b) == a,
        ensures
            ISet::new(|b: B| self.contains(rev(b)) && fwd(rev(b)).contains(b)).finite(),
        decreases
            self.len(),
    {
        let map_f = |b: B| self.contains(rev(b)) && fwd(rev(b)).contains(b);
        if self == Self::empty() {
            assert(ISet::<B>::new(map_f) =~= ISet::<B>::empty());
        }
        else {
            lemma_set_is_empty(self);
            let a: A = choose|a: A| self.contains(a);
            self.remove(a).lemma_map_flatten_by_finite(fwd, rev);
            let map_remove_f = |b: B| self.remove(a).contains(rev(b)) && fwd(rev(b)).contains(b);
            assert(ISet::<B>::new(map_f) =~= ISet::<B>::new(map_remove_f).union(fwd(a).to_iset()));
            lemma_to_iset(fwd(a));
        }
    }

    pub broadcast proof fn lemma_map_flatten_by_contains<B>(
        self,
        fwd: spec_fn(A) -> Set<B>,
        rev: spec_fn(B) -> A,
        b: B
    )
        requires
            forall|a: A, b: B| #[trigger]
                self.contains(a) && fwd(a).contains(b) ==> #[trigger] rev(b) == a,
        ensures
            #[trigger] self.map_flatten_by(fwd, rev).contains(b) <==>
                self.contains(rev(b)) && fwd(rev(b)).contains(b),
        decreases self.len(),
    {
        self.lemma_map_flatten_by_finite(fwd, rev);
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
        broadcast use Set::lemma_flatten_contains;
        broadcast use Set::lemma_map_flatten_by_contains;
        broadcast use Set::lemma_map_contains;

        self.lemma_map_flatten_by_finite(fwd, rev);
        assert forall|b: B| self.map_flatten_by(fwd, rev).contains(b)
               implies #[trigger] self.map(fwd).flatten().contains(b) by {
            let bs = choose|bs: Set<B>|
                (exists|a: A| self.contains(a) && bs == fwd(a)) && #[trigger] bs.contains(b);
            assert(self.map(fwd).contains(bs) <==> (exists|a: A| self.contains(a) && bs == fwd(a)));
        }
    }

    /// Converts a set into a sequence with an arbitrary ordering.
    pub open spec fn to_seq(self) -> Seq<A>
        decreases self.len(),
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

    pub open spec fn injective_on<B>(self, r: spec_fn(A) -> B) -> bool {
        self.to_iset().injective_on(r)
    }

    /// An element in an ordered set is called a least element (or a minimum), if it is less than
    /// every other element of the set.
    ///
    /// change f to leq bc it is a relation. also these are an ordering relation
    pub open spec fn has_least(self, leq: spec_fn(A, A) -> bool, min: A) -> bool {
        self.to_iset().has_least(leq, min)
    }

    /// An element in an ordered set is called a minimal element, if no other element is less than it.
    pub open spec fn has_minimum(self, leq: spec_fn(A, A) -> bool, min: A) -> bool {
        self.to_iset().has_minimum(leq, min)
    }

    /// An element in an ordered set is called a greatest element (or a maximum), if it is greater than
    ///every other element of the set.
    pub open spec fn has_greatest(self, leq: spec_fn(A, A) -> bool, max: A) -> bool {
        self.to_iset().has_greatest(leq, max)
    }

    /// An element in an ordered set is called a maximal element, if no other element is greater than it.
    pub open spec fn has_maximum(self, leq: spec_fn(A, A) -> bool, max: A) -> bool {
        self.to_iset().has_maximum(leq, max)
    }

    /// If a function is injective on the set `self`, then it is also injective on any subset `other` of `self`.
    pub proof fn lemma_injective_on_subset<B>(self, r: spec_fn(A) -> B, other: Self)
        requires
            other <= self,
            self.injective_on(r),
        ensures
            other.injective_on(r),
    {
        self.to_iset().lemma_injective_on_subset(r, other.to_iset());
    }

    /// Any totally-ordered set contains a unique minimal (equivalently, least) element.
    /// Returns an arbitrary value if r is not a total ordering
    pub closed spec fn find_unique_minimal(self, r: spec_fn(A, A) -> bool) -> A
        recommends
            total_ordering(r),
            self.len() > 0,
        decreases self.len(),
    {
        self.to_iset().find_unique_minimal(r)
    }

    /// Proof of correctness and expected behavior for `Set::find_unique_minimal`.
    pub proof fn find_unique_minimal_ensures(self, r: spec_fn(A, A) -> bool)
        requires
            self.len() > 0,
            total_ordering(r),
        ensures
            self.has_minimum(r, self.find_unique_minimal(r)) && (forall|min: A|
                self.has_minimum(r, min) ==> self.find_unique_minimal(r) == min),
    {
        self.to_iset().find_unique_minimal_ensures(r);
    }

    /// Any totally-ordered set contains a unique maximal (equivalently, greatest) element.
    /// Returns an arbitrary value if r is not a total ordering
    pub closed spec fn find_unique_maximal(self, r: spec_fn(A, A) -> bool) -> A
        recommends
            total_ordering(r),
            self.len() > 0,
    {
        self.to_iset().find_unique_maximal(r)
    }

    /// Proof of correctness and expected behavior for `Set::find_unique_maximal`.
    pub proof fn find_unique_maximal_ensures(self, r: spec_fn(A, A) -> bool)
        requires
            self.len() > 0,
            total_ordering(r),
        ensures
            self.has_maximum(r, self.find_unique_maximal(r)) && (forall|max: A|
                self.has_maximum(r, max) ==> self.find_unique_maximal(r) == max),
    {
        self.to_iset().find_unique_maximal_ensures(r);
    }

    /// Converts a set into a multiset where each element from the set has
    /// multiplicity 1 and any other element has multiplicity 0.
    pub open spec fn to_multiset(self) -> Multiset<A>
        decreases self.len(),
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

    /// A set has exactly one element, if and only if, it has at least one element and any two elements are equal.
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
    pub proof fn lemma_len_filter(self, f: spec_fn(A) -> bool)
        ensures
            self.filter(f).len() <= self.len(),
        decreases self.len(),
    {
        if self.is_empty() {
            assert(self.filter(f) =~= self);
        } else {
            let a = self.choose();
            assert(self.filter(f).remove(a) =~= self.remove(a).filter(f));
            self.remove(a).lemma_len_filter(f);
        }
    }

    /// In a pre-ordered set, a greatest element is necessarily maximal.
    pub proof fn lemma_greatest_implies_maximal(self, r: spec_fn(A, A) -> bool, max: A)
        requires
            pre_ordering(r),
        ensures
            self.has_greatest(r, max) ==> self.has_maximum(r, max),
    {
    }

    /// In a pre-ordered set, a least element is necessarily minimal.
    pub proof fn lemma_least_implies_minimal(self, r: spec_fn(A, A) -> bool, min: A)
        requires
            pre_ordering(r),
        ensures
            self.has_least(r, min) ==> self.has_minimum(r, min),
    {
    }

    /// In a totally-ordered set, an element is maximal if and only if it is a greatest element.
    pub proof fn lemma_maximal_equivalent_greatest(self, r: spec_fn(A, A) -> bool, max: A)
        requires
            total_ordering(r),
        ensures
            self.has_greatest(r, max) <==> self.has_maximum(r, max),
    {
        self.to_iset().lemma_maximal_equivalent_greatest(r, max);
    }

    /// In a totally-ordered set, an element is maximal if and only if it is a greatest element.
    pub proof fn lemma_minimal_equivalent_least(self, r: spec_fn(A, A) -> bool, min: A)
        requires
            total_ordering(r),
        ensures
            self.has_least(r, min) <==> self.has_minimum(r, min),
    {
        self.to_iset().lemma_minimal_equivalent_least(r, min);
    }

    /// In a partially-ordered set, there exists at most one least element.
    pub proof fn lemma_least_is_unique(self, r: spec_fn(A, A) -> bool)
        requires
            partial_ordering(r),
        ensures
            forall|min: A, min_prime: A|
                self.has_least(r, min) && self.has_least(r, min_prime) ==> min == min_prime,
    {
        self.to_iset().lemma_least_is_unique(r);
    }

    /// In a partially-ordered set, there exists at most one greatest element.
    pub proof fn lemma_greatest_is_unique(self, r: spec_fn(A, A) -> bool)
        requires
            partial_ordering(r),
        ensures
            forall|max: A, max_prime: A|
                self.has_greatest(r, max) && self.has_greatest(r, max_prime) ==> max == max_prime,
    {
        self.to_iset().lemma_greatest_is_unique(r);
    }

    /// In a totally-ordered set, there exists at most one minimal element.
    pub proof fn lemma_minimal_is_unique(self, r: spec_fn(A, A) -> bool)
        requires
            total_ordering(r),
        ensures
            forall|min: A, min_prime: A|
                self.has_minimum(r, min) && self.has_minimum(r, min_prime) ==> min == min_prime,
    {
        self.to_iset().lemma_minimal_is_unique(r);
    }

    /// In a totally-ordered set, there exists at most one maximal element.
    pub proof fn lemma_maximal_is_unique(self, r: spec_fn(A, A) -> bool)
        requires
            total_ordering(r),
        ensures
            forall|max: A, max_prime: A|
                self.has_maximum(r, max) && self.has_maximum(r, max_prime) ==> max == max_prime,
    {
        self.to_iset().lemma_maximal_is_unique(r);
    }

    /// Set difference with an additional element inserted decreases the size of
    /// the result. This can be useful for proving termination when traversing
    /// a set while tracking the elements that have already been handled.
    pub broadcast proof fn lemma_set_insert_diff_decreases(self, s: Set<A>, elt: A)
        requires
            self.contains(elt),
            !s.contains(elt),
        ensures
            #[trigger] self.difference(s.insert(elt)).len() < self.difference(s).len(),
    {
        self.difference(s.insert(elt)).lemma_subset_not_in_lt(self.difference(s), elt);
    }

    /// If there is an element not present in a subset, its length is stricly smaller.
    pub proof fn lemma_subset_not_in_lt(self: Set<A>, s2: Set<A>, elt: A)
        requires
            self.subset_of(s2),
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
        broadcast use Set::lemma_map_contains;

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
            (self.union(t)).map(f) =~= self.map(f).union(t.map(f)),
    {
        broadcast use Set::lemma_map_contains;

        let lhs = self.union(t).map(f);
        let rhs = self.map(f).union(t.map(f));

        assert forall|elem: B| rhs.contains(elem) implies lhs.contains(elem) by {
            if self.map(f).contains(elem) {
                let preimage = choose|preimage: A| self.contains(preimage) && f(preimage) == elem;
                assert(self.union(t).contains(preimage));
            } else {
                assert(t.map(f).contains(elem));
                let preimage = choose|preimage: A| t.contains(preimage) && f(preimage) == elem;
                assert(self.union(t).contains(preimage));
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
        broadcast use Set::lemma_map_contains;

        let x = choose|x: A| self.contains(x) && p(x);
        assert(self.map(f).contains(f(x)));
    }

    /// Collecting all elements `b` where `f` returns `Some(b)`
    pub open spec fn filter_map<B>(self, f: spec_fn(A) -> Option<B>) -> Set<B> {
        self.map(
            |elem: A|
                match f(elem) {
                    Option::Some(r) => set!{r},
                    Option::None => set!{},
                },
        ).flatten()
    }

    /// Inserting commutes with `filter_map`
    pub broadcast proof fn lemma_filter_map_insert<B>(
        s: Set<A>,
        f: spec_fn(A) -> Option<B>,
        elem: A,
    )
        ensures
            #[trigger] s.insert(elem).filter_map(f) == (match f(elem) {
                Some(res) => s.filter_map(f).insert(res),
                None => s.filter_map(f),
            }),
    {
        broadcast use group_set_lemmas;
        broadcast use Set::lemma_flatten_contains;
        broadcast use Set::lemma_map_contains;
        broadcast use Set::lemma_set_map_insert_commute;

        let lhs = s.insert(elem).filter_map(f);
        let rhs = match f(elem) {
            Some(res) => s.filter_map(f).insert(res),
            None => s.filter_map(f),
        };
        let to_set = |elem: A|
            match f(elem) {
                Option::Some(r) => set!{r},
                Option::None => set!{},
            };
        assert forall|r: B| #[trigger] lhs.contains(r) implies rhs.contains(r) by {
            if f(elem) != Some(r) {
                let orig = choose|orig: A| #[trigger]
                    s.contains(orig) && f(orig) == Option::Some(r);
                assert(to_set(orig) == set!{r});
                assert(s.map(to_set).contains(to_set(orig)));
            }
        }
        assert forall|r: B| #[trigger] rhs.contains(r) implies lhs.contains(r) by {
            if Some(r) == f(elem) {
                assert(s.insert(elem).map(to_set).contains(to_set(elem)));
            } else {
                let orig = choose|orig: A| #[trigger]
                    s.contains(orig) && f(orig) == Option::Some(r);
                assert(s.insert(elem).map(to_set).contains(to_set(orig)));
            }
        }
        assert(lhs =~= rhs);
    }

    /// `filter_map` and `union` commute.
    pub broadcast proof fn lemma_filter_map_union<B>(self, f: spec_fn(A) -> Option<B>, t: Set<A>)
        ensures
            #[trigger] self.union(t).filter_map(f) == self.filter_map(f).union(t.filter_map(f)),
    {
        broadcast use group_set_lemmas;
        broadcast use Set::lemma_flatten_contains;
        broadcast use Set::lemma_map_contains;

        let lhs = self.union(t).filter_map(f);
        let rhs = self.filter_map(f).union(t.filter_map(f));
        let to_set = |elem: A|
            match f(elem) {
                Option::Some(r) => set!{r},
                Option::None => set!{},
            };

        assert forall|elem: B| rhs.contains(elem) implies lhs.contains(elem) by {
            if self.filter_map(f).contains(elem) {
                let x = choose|x: A| self.contains(x) && f(x) == Option::Some(elem);
                assert(self.union(t).contains(x));
                assert(self.union(t).map(to_set).contains(to_set(x)));
            }
            if t.filter_map(f).contains(elem) {
                let x = choose|x: A| t.contains(x) && f(x) == Option::Some(elem);
                assert(self.union(t).contains(x));
                assert(self.union(t).map(to_set).contains(to_set(x)));
            }
        }
        assert forall|elem: B| lhs.contains(elem) implies rhs.contains(elem) by {
            let x = choose|x: A| self.union(t).contains(x) && f(x) == Option::Some(elem);
            if self.contains(x) {
                assert(self.map(to_set).contains(to_set(x)));
                assert(self.filter_map(f).contains(elem));
            } else {
                assert(t.contains(x));
                assert(t.map(to_set).contains(to_set(x)));
                assert(t.filter_map(f).contains(elem));
            }
        }
        assert(lhs =~= rhs);
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

    /// Conversion to a sequence and back to a set is the identity function.
    pub broadcast proof fn lemma_to_seq_to_set_id(self)
        ensures
            #[trigger] self.to_seq().to_set() =~= self,
        decreases self.len(),
    {
        broadcast use lemma_set_empty_equivalency_len;
        broadcast use Seq::to_set_ensures;
        broadcast use super::seq_lib::group_seq_properties;

        if self.len() == 0 {
            assert(self.to_seq().to_set() =~= Set::<A>::empty());
        } else {
            let elem = self.choose();
            self.remove(elem).lemma_to_seq_to_set_id();
            assert(self =~= self.remove(elem).insert(elem));
            assert(self.to_seq().to_set() =~= self.remove(elem).to_seq().to_set().insert(elem));
        }
    }
}

impl<A> Set<Set<A>> {
    pub closed spec fn flatten(self) -> Set<A> {
        Set::new(|elem| exists|elem_s: Set<A>| #[trigger] self.contains(elem_s) && elem_s.contains(elem)).unwrap()
    }

    proof fn lemma_flatten_finite(self)
        ensures
            ISet::new(|elem| exists|elem_s: Set<A>| #[trigger] self.contains(elem_s) && elem_s.contains(elem)).finite(),
        decreases
            self.len(),
    {
        let flatten_f = |elem| exists|elem_s: Set<A>| #[trigger] self.contains(elem_s) && elem_s.contains(elem);
        if forall|s: Set<A>| !self.contains(s) {
            assert(self =~= Set::<Set<A>>::empty());
            assert(ISet::new(flatten_f) =~= ISet::<A>::empty());
        }
        else {
            let s = choose|s: Set<A>| self.contains(s);
            self.remove(s).lemma_flatten_finite();
            let flatten_remove_f =
                |elem| exists|elem_s: Set<A>| #[trigger] self.remove(s).contains(elem_s) && elem_s.contains(elem);
            assert(s.to_iset().finite());
            assert(ISet::new(flatten_f) =~= ISet::new(flatten_remove_f).union(s.to_iset()));
        }
    }

    pub broadcast proof fn lemma_flatten_contains(self, elem: A)
        ensures
            #[trigger] self.flatten().contains(elem) <==>
                (exists|elem_s: Set<A>| #[trigger] self.contains(elem_s) && elem_s.contains(elem))
    {
        self.lemma_flatten_finite();
    }

    pub broadcast proof fn flatten_insert_union_commute(self, other: Set<A>)
        ensures
            self.flatten().union(other) =~= #[trigger] self.insert(other).flatten(),
    {
        broadcast use Set::lemma_flatten_contains;
        broadcast use Set::lemma_map_contains;

        let lhs = self.flatten().union(other);
        let rhs = self.insert(other).flatten();

        assert forall|elem: A| lhs.contains(elem) implies rhs.contains(elem) by {
            if self.flatten().contains(elem) {
                self.lemma_flatten_contains(elem);
                let s = choose|s: Set<A>| #[trigger] self.contains(s) && s.contains(elem);
                assert(self.insert(other).contains(s));
                assert(s.contains(elem));
            } else {
                assert(other.contains(elem));
                assert(self.insert(other).contains(other));
            }
            self.insert(other).lemma_flatten_contains(elem);
        }
    }
}

pub trait FiniteRange: Sized {
    spec fn in_range(i: Self, lo: Self, hi: Self) -> bool;

    spec fn range_set(lo: Self, hi: Self) -> Set<Self>;

    spec fn range_len(lo: Self, hi: Self) -> nat;

    proof fn range_properties(lo: Self, hi: Self)
        ensures
            forall|i: Self| #[trigger] Self::range_set(lo, hi).contains(i) <==> Self::in_range(i, lo, hi),
            Self::range_set(lo, hi).len() == Self::range_len(lo, hi),
    ;
}

pub broadcast proof fn range_set_properties<A: FiniteRange>(lo: A, hi: A)
    ensures
        forall|i: A| #[trigger] A::range_set(lo, hi).contains(i) <==> A::in_range(i, lo, hi),
        (#[trigger] A::range_set(lo, hi)).len() == A::range_len(lo, hi),
{
    A::range_properties(lo, hi);
}

pub trait FiniteFull: Sized {
    proof fn full_properties()
        ensures
            Set::<Self>::full() is Some,
    ;
}

pub broadcast proof fn full_set_properties<A: FiniteFull>()
    ensures
        #![trigger Set::<A>::full()]
        Set::<A>::full() is Some,
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
        Set::<A>::full().unwrap().filter(f)
    }
}

// Macro to implement the trait for every numeric type. We need a macro here
// because 'as nat' can't be written as a type generic.
macro_rules! range_impls {
    ([$($t:ty)*]) => {
        $(
            verus! {
                impl FiniteRange for $t {
                    open spec fn in_range(i: Self, lo: Self, hi: Self) -> bool {
                        lo <= i < hi
                    }
                    open spec fn range_set(lo: Self, hi: Self) -> Set<Self> {
                        Set::new(|i: Self| Self::in_range(i, lo, hi)).unwrap()
                    }
                    open spec fn range_len(lo: Self, hi: Self) -> nat {
                        if lo <= hi { (hi - lo) as nat } else { 0 }
                    }
                    proof fn range_properties(lo: Self, hi: Self)
                        decreases hi - lo
                    {
                        proof fn range_properties_helper(lo: $t, hi: $t)
                            ensures
                                ISet::<$t>::new(|i: $t| $t::in_range(i, lo, hi)).finite(),
                            decreases
                                hi - lo,
                        {
                            if lo >= hi {
                                assert(ISet::<$t>::new(|i: $t| $t::in_range(i, lo, hi)) =~= ISet::<$t>::empty());
                            }
                            else {
                                let hi_minus_1: $t = (hi - 1) as $t;
                                assert(hi_minus_1 == hi - 1);
                                range_properties_helper(lo, hi_minus_1);
                                assert(ISet::<$t>::new(|i: $t| $t::in_range(i, lo, hi)) =~=
                                       ISet::<$t>::new(|i: $t| $t::in_range(i, lo, hi_minus_1)).insert(hi_minus_1));
                            }
                        }

                        range_properties_helper(lo, hi);
                        if hi <= lo {
                            assert(Self::range_set(lo, hi) =~= Set::<Self>::empty());
                        } else {
                            let hi1 = (hi - 1) as $t;
                            Self::range_properties(lo, hi1);
                            assert(ISet::new(|i: Self| Self::in_range(i, lo, hi)) =~=
                                   ISet::new(|i: Self| Self::in_range(i, lo, hi1)).insert(hi1));
                            assert(Self::range_set(lo, hi) == Self::range_set(lo, hi1).insert(hi1));
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
                        proof fn full_properties_helper(lo: $t, hi: $t)
                            requires
                                lo <= hi,
                            ensures
                                ISet::<$t>::new(|a: $t| lo <= a && a <= hi).finite(),
                            decreases
                                hi - lo,
                        {
                            if lo == hi {
                                assert(ISet::<$t>::new(|a: $t| lo <= a && a <= hi) =~= iset![lo]);
                            }
                            else {
                                let hi_minus_1: $t = (hi - 1) as $t;
                                assert(hi_minus_1 == hi - 1);
                                full_properties_helper(lo, hi_minus_1);
                                assert(ISet::<$t>::new(|a: $t| lo <= a && a <= hi) =~=
                                       ISet::<$t>::new(|a: $t| lo <= a && a <= hi_minus_1).insert(hi));
                            }
                        }

                        full_properties_helper($t::MIN, $t::MAX);
                        assert(ISet::<$t>::new(|a: $t| true) =~=
                               ISet::<$t>::new(|a: $t| $t::MIN <= a && a <= $t::MAX));
                        assert(Set::<$t>::full() is Some);
                        Self::range_properties($t::MIN, $t::MAX);
                        assert(Set::<$t>::full().unwrap() == Set::range_inclusive($t::MIN, $t::MAX));
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
    broadcast use Set::lemma_map_contains;

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

/// Two sets are equal iff applying an injective (in the union of the sets) function `f` to each set produces equal sets.
pub proof fn lemma_sets_eq_iff_injective_map_on_eq<T, S>(s1: Set<T>, s2: Set<T>, f: spec_fn(T) -> S)
    requires
        (s1 + s2).injective_on(f),
    ensures
        (s1 == s2) <==> (s1.map(f) == s2.map(f)),
{
    broadcast use group_set_lemmas;
    broadcast use Set::lemma_map_contains;

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

/// The size of a union of two sets is less than or equal to the size of
/// both individual sets combined.
pub proof fn lemma_len_union<A>(s1: Set<A>, s2: Set<A>)
    ensures
        s1.union(s2).len() <= s1.len() + s2.len(),
    decreases s1.len(),
{
    if s1.is_empty() {
        assert(s1.union(s2) =~= s2);
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
pub proof fn lemma_len_intersect<A>(s1: Set<A>, s2: Set<A>)
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
pub proof fn lemma_len_subset<A>(s1: Set<A>, s2: Set<A>)
    requires
        s1.subset_of(s2),
    ensures
        s1.len() <= s2.len(),
{
    lemma_len_intersect::<A>(s2, s1);
    assert(s2.intersect(s1) =~= s1);
}

/// The size of the difference of finite set `s1` and set `s2` is less than or equal to the size of `s1`.
pub proof fn lemma_len_difference<A>(s1: Set<A>, s2: Set<A>)
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

/// Creates a finite set of integers in the range [lo, hi).
pub open spec fn set_int_range(lo: int, hi: int) -> Set<int> {
    Set::<int>::range(lo, hi)
}

/// If a set solely contains integers in the range [a, b), then its size is
/// bounded by b - a.
pub proof fn lemma_int_range(lo: int, hi: int)
    requires
        lo <= hi,
    ensures
        forall|j: int| set_int_range(lo, hi).contains(j) <==> lo <= j < hi,
        set_int_range(lo, hi).len() == hi - lo,
    decreases hi - lo,
{
    broadcast use range_set_properties;
}

/// If x is a subset of y and the size of x is equal to the size of y, x is equal to y.
pub proof fn lemma_subset_equality<A>(x: Set<A>, y: Set<A>)
    requires
        x.subset_of(y),
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
pub proof fn lemma_map_size<A, B>(x: Set<A>, y: Set<B>, f: spec_fn(A) -> B)
    requires
        x.injective_on(f),
        x.map(f) == y,
    ensures
        x.len() == y.len(),
    decreases x.len(),
{
    broadcast use group_set_properties;
    broadcast use Set::lemma_map_contains;

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
        x.map(f) == y,
    ensures
        y.len() <= x.len(),
    decreases x.len(),
{
    broadcast use group_set_properties;
    broadcast use Set::lemma_map_contains;

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
pub broadcast proof fn lemma_set_difference2<A>(s1: Set<A>, s2: Set<A>, a: A)
    ensures
        #![trigger s1.difference(s2).contains(a)]
        s2.contains(a) ==> !s1.difference(s2).contains(a),
{
}

// This verified lemma used to be an axiom in the Dafny prelude
/// If sets `a` and `b` are disjoint, meaning they have no elements in common, then the set difference
/// of `a + b` and `b` is equal to `a` and the set difference of `a + b` and `a` is equal to `b`.
pub broadcast proof fn lemma_set_disjoint<A>(a: Set<A>, b: Set<A>)
    ensures
        #![trigger (a + b).difference(a)]  //TODO: this might be too free
        a.disjoint(b) ==> ((a + b).difference(a) =~= b && (a + b).difference(b) =~= a),
{
}

// This verified lemma used to be an axiom in the Dafny prelude
// Dafny encodes the second clause with a single directional, although
// it should be fine with both directions?
// REVIEW: excluded from broadcast group if trigger is too free
//         also not that some proofs in seq_lib requires this lemma
/// Set `s` has length 0 if and only if it is equal to the empty set. If `s` has length greater than 0,
/// Then there must exist an element `x` such that `s` contains `x`.
pub broadcast proof fn lemma_set_empty_equivalency_len<A>(s: Set<A>)
    ensures
        #![trigger s.len()]
        (s.len() == 0 <==> s == Set::<A>::empty()) && (s.len() != 0 ==> exists|x: A| s.contains(x)),
{
    assert(s.len() == 0 ==> s =~= Set::empty()) by {
        if s.len() == 0 {
            assert(forall|a: A| !(Set::empty().contains(a)));
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
    assert(s.len() == 0 <== s =~= Set::empty());
}

// This verified lemma used to be an axiom in the Dafny prelude
/// If sets `a` and `b` are disjoint, meaning they share no elements in common, then the length
/// of the union `a + b` is equal to the sum of the lengths of `a` and `b`.
pub broadcast proof fn lemma_set_disjoint_lens<A>(a: Set<A>, b: Set<A>)
    ensures
        a.disjoint(b) ==> #[trigger] (a + b).len() == a.len() + b.len(),
    decreases a.len(),
{
    if a.len() == 0 {
        lemma_set_empty_equivalency_len(a);
        assert(a + b =~= b);
    } else {
        if a.disjoint(b) {
            let x = a.choose();
            assert(a.remove(x) + b =~= (a + b).remove(x));
            lemma_set_disjoint_lens(a.remove(x), b);
        }
    }
}

/// Two sets are disjoint iff their intersection is empty
pub proof fn lemma_set_disjoint_iff_empty_intersection<T>(a: Set<T>, b: Set<T>)
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

// This verified lemma used to be an axiom in the Dafny prelude
/// The length of the union between two sets added to the length of the intersection between the
/// two sets is equal to the sum of the lengths of the two sets.
pub broadcast proof fn lemma_set_intersect_union_lens<A>(a: Set<A>, b: Set<A>)
    ensures
        #[trigger] (a + b).len() + #[trigger] a.intersect(b).len() == a.len() + b.len(),
    decreases a.len(),
{
    if a.len() == 0 {
        lemma_set_empty_equivalency_len(a);
        assert(a + b =~= b);
        assert(a.intersect(b) =~= Set::empty());
        assert(a.intersect(b).len() == 0);
    } else {
        let x = a.choose();
        lemma_set_intersect_union_lens(a.remove(x), b);
        if (b.contains(x)) {
            assert(a.remove(x) + b =~= (a + b));
            assert(a.intersect(b).remove(x) =~= a.remove(x).intersect(b));
        } else {
            assert(a.remove(x) + b =~= (a + b).remove(x));
            assert(a.remove(x).intersect(b) =~= a.intersect(b));
        }
    }
}

// This verified lemma used to be an axiom in the Dafny prelude
/// The length of the set difference `A \ B` added to the length of the set difference `B \ A` added to
/// the length of the intersection `A ∩ B` is equal to the length of the union `A + B`.
///
/// The length of the set difference `A \ B` is equal to the length of `A` minus the length of the
/// intersection `A ∩ B`.
pub broadcast proof fn lemma_set_difference_len<A>(a: Set<A>, b: Set<A>)
    ensures
        (#[trigger] a.difference(b).len() + b.difference(a).len() + a.intersect(b).len() == (a
            + b).len()) && (a.difference(b).len() == a.len() - a.intersect(b).len()),
    decreases a.len(),
{
    if a.len() == 0 {
        lemma_set_empty_equivalency_len(a);
        assert(a.difference(b) =~= Set::empty());
        assert(b.difference(a) =~= b);
        assert(a.intersect(b) =~= Set::empty());
        assert(a + b =~= b);
    } else {
        let x = a.choose();
        lemma_set_difference_len(a.remove(x), b);
        if b.contains(x) {
            assert(a.intersect(b).remove(x) =~= a.remove(x).intersect(b));
            assert(a.remove(x).difference(b) =~= a.difference(b));
            assert(b.difference(a.remove(x)).remove(x) =~= b.difference(a));
            assert(a.remove(x) + b =~= a + b);
        } else {
            assert(a.remove(x) + b =~= (a + b).remove(x));
            assert(a.remove(x).difference(b) =~= a.difference(b).remove(x));
            assert(b.difference(a.remove(x)) =~= b.difference(a));
            assert(a.remove(x).intersect(b) =~= a.intersect(b));
        }
    }
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

pub broadcast proof fn lemma_set_is_empty<A>(s: Set<A>)
    requires
        !(#[trigger] s.is_empty()),
    ensures
        exists|a: A| s.contains(a),
{
    super::iset_lib::axiom_iset_is_empty(s.to_iset());
}

pub broadcast proof fn lemma_set_is_empty_len0<A>(s: Set<A>)
    ensures
        #[trigger] s.is_empty() <==> s.len() == 0,
{
}

#[doc(hidden)]
#[verifier::inline]
pub open spec fn check_argument_is_set<A>(s: Set<A>) -> Set<A> {
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
    lemma_set_is_empty,
    lemma_set_is_empty_len0,
    Set::lemma_map_contains,
    Set::lemma_map_by_contains,
    Set::lemma_map_flatten_by_contains,
    range_set_properties,
    full_set_properties,
}

pub use assert_sets_equal_internal;
pub use assert_sets_equal;

} // verus!
