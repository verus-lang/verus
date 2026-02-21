#[allow(unused_imports)]
use super::map::*;
#[allow(unused_imports)]
use super::pervasive::*;
#[allow(unused_imports)]
use super::prelude::*;
use core::marker::PhantomData;
use super::gset::*;

verus! {

/// `Set<A>` is a set type for specifications.
///
/// An object `set: Set<A>` is a subset of the set of all values `a: A`.
/// Equivalently, it can be thought of as a boolean predicate on `A`.
/// Sets are always finite; the constructors only allow construction of finite sets. If you require
/// infinite sets, see `Iset`.
pub struct Set<A>(GSet<A, Finite>);



impl<A> Set<A> {
    /// Returns the set that contains an element `f(x)` for every element `x` in `self`.
    #[verifier::inline]
    pub closed spec fn map<B>(self, f: spec_fn(A) -> B) -> Set<B> {
        GSet::map(self, f)
    }

    /// Set of all elements in the given set which satisfy the predicate `f`.
    /// Preserves finiteness of self.
    #[verifier::inline]
    pub closed spec fn filter(self, f: spec_fn(A) -> bool) -> (out: Set<A>) {
        GSet::filter(self, f)
    }

    /// Replace each element of a set with the elements of another set.
    /// Preserves finiteness of self.
    #[verifier::inline]
    pub closed spec fn product<B>(self, f: spec_fn(A) -> Set<B>) -> (out: Set<B>) {
        GSet::product(self, f)
    }

    #[verifier::inline]
    pub open spec fn to_finite(self) -> Set<A>
        recommends
            self.finite(),
    {
        self.cast_finiteness::<Finite>()
    }
}

pub(super) broadcast proof fn lemma_set_finite_from_type<A>(s: Set<A>)
    ensures
        #[trigger] s.finite(),
{
    axiom_set_finite_from_trait(s);
}

pub broadcast proof fn lemma_set_map_contains<A, B>(s: Set<A>, f: spec_fn(A) -> B)
    ensures
        #![trigger s.map(f)]
        forall|y|
            s.map(f).contains(y) <==> (exists|x| s.contains(x) && f(x) == y),
{
    lemma_gset_map_contains(s, f)
}




impl<A, FINITE: Finiteness> GSet<A, FINITE> {
    #[rustc_diagnostic_item = "verus::vstd::set::GSet::empty"]
    pub(super) closed spec fn empty() -> GSet<A, FINITE> {
        Self { set: |a| false, _phantom: PhantomData }
    }

    /// The "full" set, i.e., set containing every element of type `A`.
    /// Note that `full()` always returns an ISet, even if A is inhabited
    /// by only a finite number of elements.
    #[rustc_diagnostic_item = "verus::vstd::set::GSet::full"]
    pub(super) open spec fn full() -> ISet<A> {
        ISet::empty().complement()
    }

    /// Predicate indicating if the set contains the given element.
    #[rustc_diagnostic_item = "verus::vstd::set::GSet::contains"]
    pub(super) closed spec fn contains(self, a: A) -> bool {
        (self.set)(a)
    }

    /// Returns `true` if the first argument is a subset of the second.
    #[rustc_diagnostic_item = "verus::vstd::set::GSet::subset_of"]
    pub open spec fn subset_of<FINITE2: Finiteness>(self, s2: GSet<A, FINITE2>) -> bool {
        forall|a: A| self.contains(a) ==> s2.contains(a)
    }

    #[verifier::inline]
    pub open spec fn spec_le<FINITE2: Finiteness>(self, s2: GSet<A, FINITE2>) -> bool {
        self.subset_of(s2)
    }

    /// Returns a new set with the given element inserted.
    /// If that element is already in the set, then an identical set is returned.
    #[rustc_diagnostic_item = "verus::vstd::set::GSet::insert"]
    pub closed spec fn insert(self, a: A) -> GSet<A, FINITE> {
        GSet {
            set: |a2|
                if a2 == a {
                    true
                } else {
                    (self.set)(a2)
                },
            _phantom: PhantomData,
        }
    }

    /// Returns a new set with the given element removed.
    /// If that element is already absent from the set, then an identical set is returned.
    #[rustc_diagnostic_item = "verus::vstd::set::GSet::remove"]
    pub closed spec fn remove(self, a: A) -> GSet<A, FINITE> {
        GSet {
            set: |a2|
                if a2 == a {
                    false
                } else {
                    (self.set)(a2)
                },
            _phantom: PhantomData,
        }
    }

    /// Union of two sets of possibly-mixed finiteness.
    /// Most applications should use the finite- or infinite- specializations
    /// `union`; this generic version is mostly useful for writing generic libraries.
    pub closed spec fn generic_union<FINITE2: Finiteness>(self, s2: GSet<A, FINITE2>) -> ISet<A> {
        GSet { set: |a| (self.set)(a) || (s2.set)(a), _phantom: PhantomData }
    }

    /// Intersection of two sets of possibly-mixed finiteness.
    /// Most applications should use the finite- or infinite- specializations
    /// `intersect`; this generic version is mostly useful for writing generic libraries.
    pub closed spec fn generic_intersect<FINITE2: Finiteness>(self, s2: GSet<A, FINITE2>) -> ISet<
        A,
    > {
        GSet { set: |a| (self.set)(a) && (s2.set)(a), _phantom: PhantomData }
    }

    /// Set difference, i.e., the set of all elements in the first one but not in the second.
    /// Most applications should use the finite- or infinite- specializations
    /// `difference`; this generic version is mostly useful for writing generic libraries.
    pub closed spec fn generic_difference<FINITE2: Finiteness>(self, s2: GSet<A, FINITE2>) -> ISet<
        A,
    > {
        GSet { set: |a| (self.set)(a) && !(s2.set)(a), _phantom: PhantomData }
    }

    /// Set complement (within the space of all possible elements in `A`).
    pub closed spec fn complement(self) -> ISet<A> {
        GSet { set: |a| !(self.set)(a), _phantom: PhantomData }
    }

    /// Returns `true` if the set is finite.
    pub closed spec fn finite(self) -> bool {
        exists|f: spec_fn(A) -> nat, ub: nat|
            {
                &&& #[trigger] trigger_finite(f, ub)
                &&& surj_on(f, self)
                &&& forall|a| self.contains(a) ==> f(a) < ub
            }
    }

    /// Cardinality of the set. (Only meaningful if a set is finite.)
    pub closed spec fn len(self) -> nat {
        self.fold(0, |acc: nat, a| acc + 1)
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

    /// Creates a [`Map`] whose domain is the given set.
    /// The values of the map are given by `f`, a function of the keys.
    #[deprecated = "Use `Map::from_set` instead"]
    pub open spec fn mk_map<V>(self, f: spec_fn(A) -> V) -> GMap<A, V, FINITE> {
        GMap::from_set(self, f)
    }

    /// Returns `true` if the sets are disjoint, i.e., if their interesection is
    /// the empty set.
    pub open spec fn disjoint<FINITE2: Finiteness>(self, s2: GSet<A, FINITE2>) -> bool {
        forall|a: A| self.contains(a) ==> !s2.contains(a)
    }
}

impl<A> Set<A> {
    /// The "empty" set.
    #[verifier::inline]
    pub closed spec fn empty() -> Set<A> { GSet::empty() }

    /// Predicate indicating if the set contains the given element.
    #[verifier::inline]
    pub closed spec fn contains(self, a: A) -> bool {
        GSet::contains(self, a)
    }
    
    /// Predicate indicating if the set contains the given element: supports `self has a` syntax.
    #[verifier::inline]
    pub open spec fn spec_has(self, a: A) -> bool {
        self.contains(a)
    }

    pub closed spec fn union(self, s2: Set<A>) -> Set<A> {
        Set { set: |a| (self.set)(a) || (s2.set)(a), _phantom: PhantomData }
    }

    /// If *either* set in an intersection is finite, the result is finite.
    /// To exploit that knowledge using this method, put the one you know is finite in the `self`
    /// position.
    pub closed spec fn intersect<FINITE2: Finiteness>(self, s2: GSet<A, FINITE2>) -> Set<A> {
        Set { set: |a| (self.set)(a) && (s2.set)(a), _phantom: PhantomData }
    }

    pub closed spec fn difference<FINITE2: Finiteness>(self, s2: GSet<A, FINITE2>) -> Set<A> {
        Set { set: |a| (self.set)(a) && !(s2.set)(a), _phantom: PhantomData }
    }

    /// `+` operator, synonymous with `union`
    #[verifier::inline]
    pub open spec fn spec_add(self, s2: Set<A>) -> Set<A> {
        self.union(s2)
    }

    /// `*` operator, synonymous with `intersect`
    #[verifier::inline]
    pub open spec fn spec_mul<FINITE2: Finiteness>(self, s2: GSet<A, FINITE2>) -> Set<A> {
        self.intersect(s2)
    }

    /// `-` operator, synonymous with `difference`
    #[verifier::inline]
    pub open spec fn spec_sub<FINITE2: Finiteness>(self, s2: GSet<A, FINITE2>) -> Set<A> {
        self.difference(s2)
    }
}

/// The empty set contains no elements
pub broadcast proof fn lemma_set_empty<A>(a: A)
    ensures
        !(#[trigger] Set::<A, FINITE>::empty().contains(a)),
{
}


/// The result of inserting element `a` into set `s` must contains `a`.
pub broadcast proof fn lemma_set_insert_same<A>(s: Set<A>, a: A)
    ensures
        #[trigger] s.insert(a).contains(a),
{
}

/// If `a1` does not equal `a2`, then the result of inserting element `a2` into set `s`
/// must contain `a1` if and only if the set contained `a1` before the insertion of `a2`.
pub broadcast proof fn lemma_set_insert_different<A>(s: Set<A>, a1: A, a2: A)
    requires
        a1 != a2,
    ensures
        #[trigger] s.insert(a2).contains(a1) == s.contains(a1),
{
}

/// The result of removing element `a` from set `s` must not contain `a`.
pub broadcast proof fn lemma_set_remove_same<A>(s: Set<A>, a: A)
    ensures
        !(#[trigger] s.remove(a).contains(a)),
{
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
    lemma_set_ext_equal(s.remove(a).insert(a), s);
}

/// If `a1` does not equal `a2`, then the result of removing element `a2` from set `s`
/// must contain `a1` if and only if the set contained `a1` before the removal of `a2`.
pub broadcast proof fn lemma_set_remove_different<A>( s: Set<A>, a1: A, a2: A,)
    requires
        a1 != a2,
    ensures
        #[trigger] s.remove(a2).contains(a1) == s.contains(a1),
{
}

/// The union of sets `s1` and `s2` contains element `a` if and only if
/// `s1` contains `a` and/or `s2` contains `a`.
pub broadcast proof fn lemma_set_union<A>(s1: Set<A>, s2: Set<A>, a: A)
    ensures
        #[trigger] s1.union(s2).contains(a) == (s1.contains(a) || s2.contains(a)),
{
}

/// The intersection of sets `s1` and `s2` contains element `a` if and only if
/// both `s1` and `s2` contain `a`.
pub broadcast proof fn lemma_set_intersect<A>( s1: Set<A>, s2: Set<A>, a: A,)
    ensures
        #[trigger] s1.intersect(s2).contains(a) == (s1.contains(a) && s2.contains(a)),
{
}

/// The set difference between `s1` and `s2` contains element `a` if and only if
/// `s1` contains `a` and `s2` does not contain `a`.
pub broadcast proof fn lemma_set_difference<A>( s1: Set<A>, s2: Set<A>, a: A,)
    ensures
        #[trigger] s1.difference(s2).contains(a) == (s1.contains(a) && !s2.contains(a)),
{
}

pub broadcast proof fn lemma_set_ext_equal<A>( s1: Set<A>, s2: Set<A>,)
    ensures
        #[trigger] (s1 =~= s2) <==> (forall|a: A| s1.contains(a) == s2.contains(a))
{
    GSet::lemma_set_ext_equal(s1, s2)
}

/// The empty set is finite.
pub broadcast proof fn lemma_set_empty_finite<A, FINITE: Finiteness>()
    ensures
        #[trigger] GSet::<A, FINITE>::empty().finite(),
{
    let f = |a: A| 0;
    let ub = 0;
    let _ = trigger_finite(f, ub);
}

//////////////////////////////////////////////////////////////////////////////
/// The empty set has length 0.
pub broadcast proof fn lemma_set_empty_len<A>()
    ensures
        #[trigger] Set::<A>::empty().len() == 0,
{
    lemma_gset_empty_len();
}

pub broadcast proof fn lemma_set_map_insert<A, B>(
    s: Set<A>,
    f: spec_fn(A) -> B,
    a: A,
)
    ensures
        #[trigger] s.insert(a).map(f) == s.map(f).insert(f(a)),
{
    lemma_gset_map_insert(s, f, a);
}


pub broadcast proof fn lemma_set_map_len<A, B>(
    s: Set<A>,
    f: spec_fn(A) -> B,
)
    requires
        s.finite(),
    ensures
        #![trigger(s.map(f))]
        s.map(f).len() <= s.len(),
    decreases s.len(),
{
    lemma_gset_map_len(s, f);
}

pub broadcast proof fn lemma_set_len_empty<A>(s: Set<A>)
    requires
        s.finite(),
    ensures
        #[trigger] s.len() == 0 ==> Set::<A>::empty() == s,
{
    lemma_gset_len_empty(s);
}

/// The result of inserting an element `a` into a finite set `s` has length
/// `s.len() + 1` if `a` is not already in `s` and length `s.len()` otherwise.
pub broadcast proof fn lemma_set_insert_len<A>(s: Set<A>, a: A)
    requires
        s.finite(),
    ensures
        #[trigger] s.insert(a).len() == s.len() + (if s.contains(a) {
            0int
        } else {
            1
        }),
{
    lemma_gset_insert_len(s, a);
}

/// The result of removing an element `a` from a finite set `s` has length
/// `s.len() - 1` if `a` is in `s` and length `s.len()` otherwise.
pub broadcast proof fn lemma_set_remove_len<A>(s: Set<A>, a: A)
    requires
        s.finite(),
    ensures
        s.len() == #[trigger] s.remove(a).len() + (if s.contains(a) {
            1int
        } else {
            0
        }),
{
    lemma_gset_remove_len(s, a);
}

/// If a finite set `s` contains any element, it has length greater than 0.
pub broadcast proof fn lemma_set_contains_len<A>(s: Set<A>, a: A)
    requires
        #[trigger] s.contains(a),
    ensures
        #[trigger] s.len() != 0,
{
    lemma_gset_contains_len(s, a);
}

/// A finite set `s` contains the element `s.choose()` if it has length greater than 0.
pub broadcast proof fn lemma_set_choose_len<A>(s: Set<A>)
    requires
        s.finite(),
        #[trigger] s.len() != 0,
    ensures
        #[trigger] s.contains(s.choose()),
{
    lemma_gset_choose_len(s);
}

//////////////////////////////////////////////////////////////////////////////

// TODO(jonh): left off here

//////////////////////////////////////////////////////////////////////////////
// Machinery to support range_set
pub trait FiniteRange: Sized {
    spec fn range_iset(lo: Self, hi: Self) -> ISet<Self>;

    spec fn range_len(lo: Self, hi: Self) -> nat;

    proof fn range_properties(lo: Self, hi: Self)
        ensures
            Self::range_iset(lo, hi).finite(),
            Self::range_iset(lo, hi).len() == Self::range_len(lo, hi),
    ;
}

pub broadcast proof fn range_set_properties<A: FiniteRange>(lo: A, hi: A)
    ensures
        (#[trigger] A::range_iset(lo, hi)).finite(),
        A::range_iset(lo, hi).len() == A::range_len(lo, hi),
{
    A::range_properties(lo, hi);
}

pub trait FiniteFull: Sized {
    proof fn full_properties()
        ensures
            ISet::<Self>::full().finite(),
    ;
}

pub broadcast proof fn full_set_properties<A: FiniteFull>()
    ensures
        #![trigger Set::<A>::full()]
        #![trigger ISet::<A>::full()]
        (ISet::<A>::full()).finite(),
{
    A::full_properties();
}

impl<A: FiniteRange> Set<A> {
    #[verifier::inline]
    /// This is a recommended constructor for building finite sets containing a contiguous range of a
    /// numeric type.
    pub open spec fn range(lo: A, hi: A) -> Set<A> {
        A::range_iset(lo, hi).to_finite()
    }

    #[verifier::inline]
    pub open spec fn range_inclusive(lo: A, hi: A) -> Set<A> {
        A::range_iset(lo, hi).insert(hi).to_finite()
    }
}

impl<A: FiniteRange> ISet<A> {
    #[verifier::inline]
    /// This is a recommended constructor for building finite sets containing a contiguous range of a
    /// numeric type.
    pub open spec fn range(lo: A, hi: A) -> ISet<A> {
        A::range_iset(lo, hi)
    }

    #[verifier::inline]
    pub open spec fn range_inclusive(lo: A, hi: A) -> ISet<A> {
        A::range_iset(lo, hi).insert(hi)
    }
}

// Macro to implement the trait for every numeric type. We need a macro here
// because 'as nat' can't be written as a type generic.
macro_rules! range_impls {
    ([$($t:ty)*]) => {
        $(
            verus! {
                impl FiniteRange for $t {
                    open spec fn range_iset(lo: Self, hi: Self) -> ISet<Self> {
                        ISet::new(|i: Self| lo <= i < hi)
                    }
                    open spec fn range_len(lo: Self, hi: Self) -> nat {
                        if lo <= hi { (hi - lo) as nat } else { 0 }
                    }
                    proof fn range_properties(lo: Self, hi: Self)
                        decreases hi - lo
                    {
                        broadcast use lemma_set_empty_finite;
                        broadcast use lemma_set_empty_len;
                        broadcast use lemma_set_insert_len;

                        if hi <= lo {
                            assert(Self::range_iset(lo, hi).is_empty());
                        } else {
                            let hi1 = (hi - 1) as $t;
                            Self::range_properties(lo, hi1);
                            assert(Self::range_iset(lo, hi) == Self::range_iset(lo, hi1).insert(hi1));
                            lemma_set_insert_finite(Self::range_iset(lo, hi1), hi1);
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
                        broadcast use lemma_set_insert_finite;

                        assert(ISet::<$t>::full() == ISet::range_inclusive($t::MIN, $t::MAX));
                        <$t as FiniteRange>::range_properties($t::MIN, $t::MAX);
                    }
                }
            } // verus!
        )*
    }
}

// Make Set,ISet::range available for all of the Verus numeric types
range_impls!([
    int nat
    usize u8 u16 u32 u64 u128
    isize i8 i16 i32 i64 i128
]);

// Make ISet::full available for all of the Verus numeric types
full_impls!([
    usize u8 u16 u32 u64 u128
    isize i8 i16 i32 i64 i128
]);

//////////////////////////////////////////////////////////////////////////////
#[deprecated = "Use `Set::range` instead"]
pub open spec fn set_int_range(lo: int, hi: int) -> Set<int> {
    Set::<int>::range(lo, hi)
}

// filter definition is closed now, so we expose its meaning through this lemma
pub broadcast proof fn lemma_set_filter_is_intersect<A, FINITE: Finiteness>(
    s: GSet<A, FINITE>,
    f: spec_fn(A) -> bool,
)
    ensures
        (#[trigger] s.filter(f)).congruent(s.generic_intersect(ISet::new(f))),
{
}

impl<A, FINITE: Finiteness> GSet<A, FINITE> {
    pub broadcast proof fn lemma_set_product_contains<B>(self, f: spec_fn(A) -> GSet<B, FINITE>)
        ensures
            #![trigger(self.product(f))]
            forall|b|
                (#[trigger] self.product(f).contains(b)) <==> exists|a|
                    self.contains(a) && f(a).contains(b),
    {
    }

    pub broadcast proof fn lemma_set_product_contains_2<B>(
        self,
        f: spec_fn(A) -> GSet<B, FINITE>,
        a: A,
        b: B,
    )
        ensures
            #![trigger self.contains(a), f(a).contains(b)]
            #![trigger self.product(f).contains(b), f(a).contains(b)]
            self.contains(a) && f(a).contains(b) ==> self.product(f).contains(b),
    {
    }
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

impl<A: FiniteFull> Set<A> {
    #[verifier::inline]
    pub open spec fn from_finite_type(f: spec_fn(A) -> bool) -> Set<A> {
        ISet::<A>::full().to_finite().filter(f)
    }
}

impl<A> Set<A> {
    /// Set::map_by is like Set::map, but map only takes a forward function fwd: spec_fn(A) -> B,
    /// while map_by also takes a reverse function rev: spec_fn(B) -> A.
    /// This reverse function can make proofs easier
    /// by avoiding the "exists" that appears in lemmas about Set::map.
    /// Example: for a set s: Set<int>, to map each i in s to (i, 10 * i),
    /// we can write either s.map(|i: int| (i, 10 * i))
    /// or s.map_by(|i: int| (i, 10 * i), |p: (int, int)| p.0);
    /// the version with map_by is usually easier to use in proofs.
    pub open spec fn map_by<B>(self, fwd: spec_fn(A) -> B, rev: spec_fn(B) -> A) -> Set<B> {
        ISet::new(|b: B| self.contains(rev(b)) && b == fwd(rev(b))).to_finite()
    }
}

pub broadcast proof fn lemma_map_by<A, B>(sa: Set<A>, fwd: spec_fn(A) -> B, rev: spec_fn(B) -> A)
    ensures
        #![trigger sa.map_by(fwd, rev)]
        forall|b: B| #[trigger]
            sa.map_by(fwd, rev).contains(b) <==> sa.contains(rev(b)) && b == fwd(rev(b)),
{
    broadcast use {fold::group_set_lemmas_early, GSet::to_infinite_ensures};

    let ib1 = ISet::new(|b: B| sa.contains(rev(b)) && b == fwd(rev(b)));
    let ib2 = sa.map(fwd).to_infinite();
    assert(ib1 == ib2.filter(|b| ib1.contains(b)));
}

pub broadcast group group_set_lemmas {
    // This line...
    fold::group_set_lemmas_early,
    // ...should replace these lines (up to the blank), but it doesn't.
    // (verus #1616)
    GSet::cast_finiteness_properties,
    GSet::lemma_self_castable,
    GSet::lemma_to_infinite_castable,
    lemma_set_finite_from_type,
    lemma_set_empty,
    lemma_set_new,
    lemma_set_insert_same,
    lemma_set_insert_different,
    lemma_set_remove_same,
    lemma_set_remove_insert,
    lemma_set_remove_different,
    lemma_set_generic_union,
    lemma_set_union,
    lemma_set_generic_intersect,
    lemma_set_intersect,
    lemma_set_generic_difference,
    lemma_set_difference,
    lemma_set_complement,
    lemma_set_ext_equal,
    lemma_set_ext_equal_deep,
    lemma_set_empty_finite,
    lemma_set_insert_finite,
    lemma_set_remove_finite,
    lemma_set_map_contains,
    lemma_iset_map_contains,
    lemma_set_map_subset,
    lemma_set_map_finite,
    lemma_set_filter_finite,
    GSet::to_infinite_ensures,
    lemma_set_map_len,
    lemma_set_map_insert,
    lemma_set_generic_union_finite,
    lemma_set_union_finite,
    lemma_set_generic_intersect_finite,
    lemma_set_intersect_finite,
    lemma_set_generic_difference_finite,
    lemma_set_difference_finite,
    lemma_set_choose_infinite,
    lemma_set_empty_len,
    lemma_set_len_empty,
    lemma_set_insert_len,
    lemma_set_remove_len,
    lemma_set_contains_len,
    lemma_set_choose_len,
    lemma_set_filter_is_intersect,
    GSet::lemma_set_product_contains,
    GSet::lemma_set_product_contains_2,
    range_set_properties,
    lemma_to_finite_len,
    lemma_map_by,
    full_set_properties,
}

} // verus!
