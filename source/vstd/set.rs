#[allow(unused_imports)]
use super::iset::*;
#[allow(unused_imports)]
use super::map::*;
#[allow(unused_imports)]
use super::pervasive::*;
#[allow(unused_imports)]
use super::prelude::*;

verus! {

/// `Set<A>` is a finite set type for specifications.
///
/// An object `set: Set<A>` is a subset of the set of all values `a: A`.
/// Equivalently, it can be thought of as a boolean predicate on `A`.
///
/// Sets can be constructed in a few different ways:
///  * [`Set::empty`] gives an empty set
///  * [`Set::new`] constructs a set from a boolean predicate
///  * The [`set!`] macro, to construct small sets of a fixed size
///  * By manipulating an existing sequence with [`Set::union`], [`Set::intersect`],
///    [`Set::difference`], [`Set::complement`], [`Set::filter`], [`Set::insert`],
///    or [`Set::remove`].
///
/// To prove that two sequences are equal, it is usually easiest to use the extensionality
/// operator `=~=`.
///
/// `Set` only holds finite sets, so it can be used in recursive types.
/// For instance, a type `T` can contain a `Set<T>`.
#[verifier::ext_equal]
#[verifier::external_body]
#[verifier::accept_recursive_types(A)]
#[cfg_attr(verus_keep_ghost, rustc_diagnostic_item = "verus::vstd::set::Set")]
pub struct Set<A> {
    // To prevent Verus's internal checks from rejecting recursive types,
    // we use an artificial definition of `Set` that hides its inclusion
    // of a function from `A` to `bool`.
    //
    // To make sure that proofs in this file don't take advantage of
    // this artificial structure (e.g., to prove that any two `Set`s are
    // equal), we mark this definition as `external_body`.
    //
    // For future work, we may figure out how to have `Set` use a
    // `Seq`-like representation that is inherently finite, to eliminate
    // the need for this. We haven't done this yet, though, because it would
    // introduce the problem of multiple representations of equivalent
    // sets, which creates a different problem with extensional equality.
    dummy: core::marker::PhantomData<A>,
}

impl<A> Set<A> {
    /// Generates an `ISet` with the same elements
    pub uninterp spec fn to_iset(self) -> ISet<A>;

    /// Generates a `Set` from the given `ISet`, governed by
    /// `axiom_make_set`. Thanks to the axiom `axiom_make_set`, this
    /// function is known to produce a `Set` with the same elements as
    /// the given `ISet`, provided that `ISet` is finite. If the given
    /// `ISet` is infinite, it produces an arbitrary finite set.
    uninterp spec fn make_set(s: ISet<A>) -> Set<A>;

    /// This axiom says that `make_set` produces a `Set` with the same
    /// elements as the given `ISet`, provided that `ISet` is finite.
    /// (If the given `ISet` is infinite, `make_set` produces an
    /// arbitrary finite set.)
    broadcast axiom fn axiom_make_set(s: ISet<A>)
        requires
            s.finite(),
        ensures
            #![trigger Self::make_set(s).to_iset()]
            Self::make_set(s).to_iset() == s,
    ;

    /// This axiom says that the set represented by a `Set` is always
    /// finite.
    broadcast axiom fn axiom_is_finite(self)
        ensures
            #![trigger self.to_iset().finite()]
            self.to_iset().finite(),
    ;

    /// The "empty" set.
    ///
    /// Usage Example: <br>
    /// ```rust
    /// let empty_set = Set::<A>::empty();
    ///
    /// assert(empty_set.is_empty());
    /// assert(empty_set.complement() =~= Set::<A>::full());
    /// assert(Set::<A>::empty().finite());
    /// assert(Set::<A>::empty().len() == 0);
    /// assert(forall |x: A| !Set::<A>::empty().contains(x));
    /// ```
    /// Axioms around the empty set are: <br>
    /// * [`lemma_set_empty_len`] <br>
    /// * [`lemma_set_empty`]
    #[rustc_diagnostic_item = "verus::vstd::set::Set::empty"]
    pub closed spec fn empty() -> Set<A> {
        Self::make_set(ISet::<A>::empty())
    }

    /// Set whose membership is determined by the given `ISet`,
    /// but only if that `ISet` is finite.
    ///
    /// Usage Examples:
    /// ```rust
    /// let iset_a = ISet::new(|x : nat| x < 42);
    /// let option_set_b = Set::<A>::new(iset_a);
    /// assert(iset_a.finite() ==>
    ///        option_set_b matches Some(s) &&
    ///        forall|x| x < 42 <==> s.contains(x));
    /// ```
    pub closed spec fn new_from_iset(s: ISet<A>) -> Option<Set<A>> {
        if s.finite() {
            Some(Self::make_set(s))
        } else {
            None
        }
    }

    /// Set whose membership is determined by the given boolean predicate,
    /// but only if the predicate produces a finite set. (If it produces an
    /// infinite set, the result of this function is None.)
    ///
    /// Usage Examples:
    /// ```rust
    /// let option_set_a = Set::new(|x : nat| x < 42);
    /// let option_set_b = Set::<A>::new(|x| some_predicate(x));
    /// assert(ISet::new(|x| some_predicate(x)).finite()) ==>
    ///        option_set_b matches Some(s) &&
    ///        forall|x| some_predicate(x) <==> s.contains(x));
    /// ```
    pub closed spec fn new(f: spec_fn(A) -> bool) -> Option<Set<A>> {
        Self::new_from_iset(ISet::new(f))
    }

    /// Set whose membership is determined by the given boolean predicate,
    /// assuming the predicate produces a finite set.
    ///
    /// Usage Examples:
    /// ```rust
    /// let set_a = Set::new_assuming_finite(|x : nat| x < 42);
    /// let set_b = Set::<A>::new_assuming_finite(|x| some_predicate(x));
    /// assert(forall|x| some_predicate(x) <==> set_b.contains(x));
    /// ```
    #[deprecated(note = "Set::new_assuming_finite is helpful for incremental porting of existing code to the new version of Verus supporting finite sets. But it's dangerous since it assumes the given function describes a finite set.")]
    pub closed spec fn new_assuming_finite(f: spec_fn(A) -> bool) -> Set<A> {
        Self::make_set(ISet::new(f))
    }

    /// The "full" set, i.e., set containing every element of type `A`.
    /// Note that if `A` is infinite, then this produces None.
    #[rustc_diagnostic_item = "verus::vstd::set::Set::full"]
    pub open spec fn full() -> Option<Set<A>> {
        Set::new(|a: A| true)
    }

    /// Predicate indicating if the set contains the given element.
    #[rustc_diagnostic_item = "verus::vstd::set::Set::contains"]
    #[verifier::inline]
    pub open spec fn contains(self, a: A) -> bool {
        self.to_iset().contains(a)
    }

    /// Predicate indicating if the set contains the given element: supports `self has a` syntax.
    #[verifier::inline]
    pub open spec fn spec_has(self, a: A) -> bool {
        self.contains(a)
    }

    /// Returns `true` if the first argument is a subset of the second.
    #[rustc_diagnostic_item = "verus::vstd::set::Set::subset_of"]
    pub open spec fn subset_of(self, s2: Set<A>) -> bool {
        forall|a: A| self.contains(a) ==> s2.contains(a)
    }

    #[verifier::inline]
    pub open spec fn spec_le(self, s2: Set<A>) -> bool {
        self.subset_of(s2)
    }

    /// Returns a new set with the given element inserted.
    /// If that element is already in the set, then an identical set is returned.
    #[rustc_diagnostic_item = "verus::vstd::set::Set::insert"]
    pub closed spec fn insert(self, a: A) -> Set<A> {
        Self::make_set(self.to_iset().insert(a))
    }

    /// Returns a new set with the given element removed.
    /// If that element is already absent from the set, then an identical set is returned.
    #[rustc_diagnostic_item = "verus::vstd::set::Set::remove"]
    pub closed spec fn remove(self, a: A) -> Set<A> {
        Self::make_set(self.to_iset().remove(a))
    }

    /// Union of two sets.
    pub closed spec fn union(self, s2: Set<A>) -> Set<A> {
        Self::make_set(self.to_iset().union(s2.to_iset()))
    }

    /// `+` operator, synonymous with `union`
    #[verifier::inline]
    pub open spec fn spec_add(self, s2: Set<A>) -> Set<A> {
        self.union(s2)
    }

    /// Intersection of two sets.
    pub closed spec fn intersect(self, s2: Set<A>) -> Set<A> {
        Self::make_set(self.to_iset().intersect(s2.to_iset()))
    }

    /// `*` operator, synonymous with `intersect`
    #[verifier::inline]
    pub open spec fn spec_mul(self, s2: Set<A>) -> Set<A> {
        self.intersect(s2)
    }

    /// Set difference, i.e., the set of all elements in the first one but not in the second.
    pub closed spec fn difference(self, s2: Set<A>) -> Set<A> {
        Self::make_set(self.to_iset().difference(s2.to_iset()))
    }

    /// `-` operator, synonymous with `difference`
    #[verifier::inline]
    pub open spec fn spec_sub(self, s2: Set<A>) -> Set<A> {
        self.difference(s2)
    }

    /// Set complement (within the space of all possible elements in `A`).
    /// Returns None if this would be an infinite set.
    pub open spec fn complement(self) -> Option<Set<A>> {
        Set::new(|a| !self.contains(a))
    }

    /// Set of all elements in the given set which satisfy the predicate `f`.
    pub closed spec fn filter(self, f: spec_fn(A) -> bool) -> Set<A> {
        Self::make_set(self.to_iset().filter(f))
    }

    /// Returns `true` if the set is finite.
    #[deprecated(note = "Every Set is always finite, so this is always true.")]
    pub open spec fn finite(self) -> bool {
        true
    }

    /// Returns `true` if this set is congruent to (contains the same elements as)
    /// a given ISet.
    pub open spec fn congruent(self, s2: ISet<A>) -> bool {
        forall|a: A| #![all_triggers] self.contains(a) <==> s2.contains(a)
    }

    /// Cardinality of the set.
    pub closed spec fn len(self) -> nat {
        self.to_iset().len()
    }

    /// Chooses an arbitrary element of the set.
    ///
    /// This is often useful for proofs by induction.
    ///
    /// (Note that, although the result is arbitrary, it is still a _deterministic_ function
    /// like any other `spec` function.)
    pub open spec fn choose(self) -> A {
        choose|a: A| self.contains(a)
    }

    /// Returns `true` if the sets are disjoint, i.e., if their interesection is
    /// the empty set.
    pub open spec fn disjoint(self, s2: Self) -> bool {
        forall|a: A| self.contains(a) ==> !s2.contains(a)
    }
}

/// Sets `s1` and `s2` are considered equal if and only if they contain all of the same elements.
/// This has to be an axiom because `Set` is `external_body`.
pub broadcast proof fn axiom_set_ext_equal<A>(s1: Set<A>, s2: Set<A>)
    ensures
        #[trigger] (s1 =~= s2) <==> (forall|a: A| s1.contains(a) == s2.contains(a)),
{
    admit();
}

/// Sets `s1` and `s2` are considered equal if and only if they contain all of the same elements.
/// This has to be an axiom because `Set` is `external_body`.
pub broadcast proof fn axiom_set_ext_equal_deep<A>(s1: Set<A>, s2: Set<A>)
    ensures
        #[trigger] (s1 =~~= s2) <==> s1 =~= s2,
{
    admit();
}

broadcast use super::iset::group_iset_lemmas;

pub mod fold {
    use super::*;

    impl<A> Set<A> {
        /// Folds the set, applying `f` to perform the fold. The next element for the fold is chosen by
        /// the choose operator.
        ///
        /// Given a set `s = {x0, x1, x2, ..., xn}`, applying this function `s.fold(init, f)`
        /// returns `f(...f(f(init, x0), x1), ..., xn)`.
        #[verifier::inline]
        pub open spec fn fold<B>(self, z: B, f: spec_fn(B, A) -> B) -> B
            recommends
                super::super::iset::fold::is_fun_commutative(f),
        {
            self.to_iset().fold(z, f)
        }
    }

}

/// The empty set contains no elements
pub broadcast proof fn lemma_set_empty<A>(a: A)
    ensures
        !(#[trigger] Set::empty().contains(a)),
{
    broadcast use Set::axiom_make_set;

}

/// If `Set::<A>::new(f)` produces `Some(s)`, then `s` contains `a`
/// if and only if `f(a)` is true.
pub broadcast proof fn lemma_set_new<A>(f: spec_fn(A) -> bool, a: A)
    requires
        Set::<A>::new(f) is Some,
    ensures
        #[trigger] Set::<A>::new(f).unwrap().contains(a) == f(a),
{
    broadcast use Set::axiom_make_set;

}

/// If `ISet::<A>::new(f)` is finite, then `Set::<A>::new(f)`
/// produces `Some(s)`. Useful for triggering the `lemma_set_new`
/// to show that `s` contains `a` if and only if `f(a)` is true.
pub broadcast proof fn lemma_set_new_some<A>(f: spec_fn(A) -> bool)
    requires
        ISet::<A>::new(f).finite(),
    ensures
        #[trigger] Set::<A>::new(f) is Some,
{
    broadcast use Set::axiom_make_set;

}

/// Shows that `Set::<A>::new_assuming_finite(f)` contains `a`
/// if and only if `f(a)` is true.
#[allow(deprecated)]
pub broadcast proof fn lemma_set_new_assuming_finite<A>(f: spec_fn(A) -> bool, a: A)
    ensures
        #[trigger] Set::<A>::new_assuming_finite(f).contains(a) == f(a),
{
    broadcast use Set::axiom_make_set;

    assume(ISet::new(f).finite());  // This is the assumption
}

/// If an iset `s` is finite, then `Set::new_from_iset(s)` has the same
/// contents as `s`.
pub broadcast proof fn lemma_set_new_from_iset<A>(s: ISet<A>)
    requires
        s.finite(),
    ensures
        #![trigger Set::<A>::new_from_iset(s)]
        Set::<A>::new_from_iset(s) is Some,
        Set::<A>::new_from_iset(s).unwrap().to_iset() == s,
{
    broadcast use Set::axiom_make_set;

    assert(ISet::new(|a: A| s.contains(a)) =~= s);
}

/// The result of inserting element `a` into set `s` must contains `a`.
pub broadcast proof fn lemma_set_insert_same<A>(s: Set<A>, a: A)
    ensures
        #[trigger] s.insert(a).contains(a),
{
    broadcast use Set::axiom_make_set;
    broadcast use Set::axiom_is_finite;

}

/// If `a1` does not equal `a2`, then the result of inserting element `a2` into set `s`
/// must contain `a1` if and only if the set contained `a1` before the insertion of `a2`.
pub broadcast proof fn lemma_set_insert_different<A>(s: Set<A>, a1: A, a2: A)
    requires
        a1 != a2,
    ensures
        #[trigger] s.insert(a2).contains(a1) == s.contains(a1),
{
    broadcast use Set::axiom_make_set;
    broadcast use Set::axiom_is_finite;

}

/// The result of removing element `a` from set `s` must not contain `a`.
pub broadcast proof fn lemma_set_remove_same<A>(s: Set<A>, a: A)
    ensures
        !(#[trigger] s.remove(a).contains(a)),
{
    broadcast use Set::axiom_make_set;
    broadcast use Set::axiom_is_finite;

}

/// Removing an element `a` from a set `s` and then inserting `a` back into the set`
/// is equivalent to the original set `s`.
pub broadcast proof fn lemma_set_remove_insert<A>(s: Set<A>, a: A)
    requires
        s.contains(a),
    ensures
        (#[trigger] s.remove(a)).insert(a) == s,
{
    assert forall|aa| #![all_triggers] s.remove(a).insert(a).contains(aa) implies s.contains(
        aa,
    ) by {
        if a == aa {
        } else {
            lemma_set_remove_different(s, aa, a);
            lemma_set_insert_different(s.remove(a), aa, a);
        }
    };
    assert forall|aa| #![all_triggers] s.contains(aa) implies s.remove(a).insert(a).contains(
        aa,
    ) by {
        if a == aa {
            lemma_set_insert_same(s.remove(a), a);
        } else {
            lemma_set_remove_different(s, aa, a);
            lemma_set_insert_different(s.remove(a), aa, a);
        }
    };
    axiom_set_ext_equal(s.remove(a).insert(a), s);
}

/// If `a1` does not equal `a2`, then the result of removing element `a2` from set `s`
/// must contain `a1` if and only if the set contained `a1` before the removal of `a2`.
pub broadcast proof fn lemma_set_remove_different<A>(s: Set<A>, a1: A, a2: A)
    requires
        a1 != a2,
    ensures
        #[trigger] s.remove(a2).contains(a1) == s.contains(a1),
{
    broadcast use axiom_set_ext_equal;
    broadcast use Set::axiom_make_set;
    broadcast use Set::axiom_is_finite;

}

/// The union of sets `s1` and `s2` contains element `a` if and only if
/// `s1` contains `a` and/or `s2` contains `a`.
pub broadcast proof fn lemma_set_union<A>(s1: Set<A>, s2: Set<A>, a: A)
    ensures
        #[trigger] s1.union(s2).contains(a) == (s1.contains(a) || s2.contains(a)),
{
    broadcast use axiom_set_ext_equal;
    broadcast use Set::axiom_make_set;
    broadcast use Set::axiom_is_finite;

}

/// The intersection of sets `s1` and `s2` contains element `a` if and only if
/// both `s1` and `s2` contain `a`.
pub broadcast proof fn lemma_set_intersect<A>(s1: Set<A>, s2: Set<A>, a: A)
    ensures
        #[trigger] s1.intersect(s2).contains(a) == (s1.contains(a) && s2.contains(a)),
{
    broadcast use axiom_set_ext_equal;
    broadcast use Set::axiom_make_set;
    broadcast use Set::axiom_is_finite;

}

/// The set difference between `s1` and `s2` contains element `a` if and only if
/// `s1` contains `a` and `s2` does not contain `a`.
pub broadcast proof fn lemma_set_difference<A>(s1: Set<A>, s2: Set<A>, a: A)
    ensures
        #[trigger] s1.difference(s2).contains(a) == (s1.contains(a) && !s2.contains(a)),
{
    broadcast use Set::axiom_make_set;
    broadcast use Set::axiom_is_finite;

}

/// The complement of set `s` contains element `a` if and only if `s` does not contain `a`.
pub broadcast proof fn lemma_set_complement<A>(s: Set<A>, a: A)
    requires
        ISet::new(|a| !s.contains(a)).finite(),
    ensures
        #[trigger] s.complement().unwrap().contains(a) == !s.contains(a),
{
    broadcast use Set::axiom_make_set;

}

/// The filter of set `s` using function `f` contains element `a` if and only if `s` contains `a`
/// and `f(a)` is true.
pub broadcast proof fn lemma_set_filter<A>(s: Set<A>, f: spec_fn(A) -> bool, a: A)
    ensures
        #[trigger] s.filter(f).contains(a) == (s.contains(a) && f(a)),
{
    broadcast use Set::axiom_make_set;
    broadcast use Set::axiom_is_finite;

}

// Lemmas about len
// The following, with lemma_set_ext_equal, are enough to build libraries about len.
/// The empty set has length 0.
pub broadcast proof fn lemma_set_empty_len<A>()
    ensures
        #[trigger] Set::<A>::empty().len() == 0,
{
    broadcast use Set::axiom_make_set;

}

/// The result of inserting an element `a` into a finite set `s` has length
/// `s.len() + 1` if `a` is not already in `s` and length `s.len()` otherwise.
pub broadcast proof fn lemma_set_insert_len<A>(s: Set<A>, a: A)
    ensures
        #[trigger] s.insert(a).len() == s.len() + (if s.contains(a) {
            0int
        } else {
            1
        }),
{
    broadcast use Set::axiom_make_set;
    broadcast use Set::axiom_is_finite;

}

/// The result of removing an element `a` from a finite set `s` has length
/// `s.len() - 1` if `a` is in `s` and length `s.len()` otherwise.
pub broadcast proof fn lemma_set_remove_len<A>(s: Set<A>, a: A)
    ensures
        s.len() == #[trigger] s.remove(a).len() + (if s.contains(a) {
            1int
        } else {
            0
        }),
{
    broadcast use Set::axiom_make_set;
    broadcast use Set::axiom_is_finite;

}

/// If a finite set `s` contains any element, it has length greater than 0.
pub broadcast proof fn lemma_set_contains_len<A>(s: Set<A>, a: A)
    requires
        #[trigger] s.contains(a),
    ensures
        #[trigger] s.len() != 0,
{
    broadcast use Set::axiom_make_set;
    broadcast use Set::axiom_is_finite;

}

/// A finite set `s` contains the element `s.choose()` if it has length greater than 0.
pub broadcast proof fn lemma_set_choose_len<A>(s: Set<A>)
    requires
        #[trigger] s.len() != 0,
    ensures
        #[trigger] s.contains(s.choose()),
{
    assert(s.to_iset().contains(s.to_iset().choose()));
}

/// Converting a `Set` to an `ISet` produces a finite result.
pub broadcast proof fn lemma_to_iset_finite<A>(s: Set<A>)
    ensures
        #[trigger] s.to_iset().finite(),
{
    broadcast use Set::axiom_make_set;
    broadcast use Set::axiom_is_finite;

}

/// Converting a `Set` to an `ISet` produces a result with the same
/// length.
pub broadcast proof fn lemma_to_iset_len<A>(s: Set<A>)
    ensures
        #[trigger] s.to_iset().len() == s.len(),
{
    broadcast use Set::axiom_make_set;
    broadcast use Set::axiom_is_finite;

}

pub broadcast group group_set_lemmas {
    axiom_set_ext_equal,
    axiom_set_ext_equal_deep,
    lemma_set_empty,
    lemma_set_new,
    lemma_set_new_assuming_finite,
    lemma_set_new_from_iset,
    lemma_set_new_some,
    lemma_set_insert_same,
    lemma_set_insert_different,
    lemma_set_remove_same,
    lemma_set_remove_insert,
    lemma_set_remove_different,
    lemma_set_union,
    lemma_set_intersect,
    lemma_set_difference,
    lemma_set_complement,
    lemma_set_filter,
    lemma_set_empty_len,
    lemma_set_insert_len,
    lemma_set_remove_len,
    lemma_set_contains_len,
    lemma_set_choose_len,
    lemma_set_new,
    lemma_to_iset_finite,
    lemma_to_iset_len,
}

// Macros
#[doc(hidden)]
#[macro_export]
macro_rules! set_internal {
    [$($elem:expr),* $(,)?] => {
        $crate::vstd::set::Set::empty()
            $(.insert($elem))*
    };
}

#[macro_export]
macro_rules! set {
    [$($tail:tt)*] => {
        $crate::vstd::prelude::verus_proof_macro_exprs!($crate::vstd::set::set_internal!($($tail)*))
    };
}

pub use set_internal;
pub use set;

} // verus!
