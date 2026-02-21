#[allow(unused_imports)]
use super::map::*;
#[allow(unused_imports)]
use super::pervasive::*;
#[allow(unused_imports)]
use super::prelude::*;
use core::marker::PhantomData;
use super::gset::*;

verus! {
/// `ISet<A>` is a set type for specifications.
///
/// An object `set: ISet<A>` is a subset of the set of all values `a: A`.
/// Equivalently, it can be thought of as a boolean predicate on `A`.
///
/// In general, an ISet might be infinite.
/// To work specifically with finite sets, see the [`self.finite()`](Set::finite) predicate.
///
/// Sets can be constructed in a few different ways:
///  * [`Set::empty`] gives an empty set
///  * [`Set::full`] gives the set of all elements in `A`
///  * [`Set::new`] constructs a set from a boolean predicate
///  * The [`set!`] macro, to construct small sets of a fixed size
///  * By manipulating an existing sequence with [`Set::union`], [`Set::intersect`],
///    [`Set::difference`], [`Set::complement`], [`Set::filter`], [`Set::insert`],
///    or [`Set::remove`].
///
/// To prove that two sequences are equal, it is usually easiest to use the extensionality
/// operator `=~=`.
pub struct ISet<A>(GSet<A, Infinite>);

impl<A> ISet<A> {
    pub closed spec fn new(f: spec_fn(A) -> bool) -> ISet<A> {
        ISet { set: f, _phantom: PhantomData }
    }

    /// The "empty" ISet.
    pub closed spec fn empty() -> ISet<A> { GSet::empty() }

    /// The "full" ISet, i.e., ISet containing every element of type `A`.
    /// Note that `full()` always returns an ISet, even if A is inhabited
    /// by only a finite number of elements.
    #[rustc_diagnostic_item = "verus::vstd::set::GSet::full"]
    pub(super) open spec fn full() -> ISet<A> {
        ISet::empty().complement()
    }

    /// Predicate indicating if the ISet contains the given element.
    #[verifier::inline]
    pub closed spec fn contains(self, a: A) -> bool {
        GSet::contains(self, a)
    }

    /// Predicate indicating if the set contains the given element: supports `self has a` syntax.
    #[verifier::inline]
    pub open spec fn spec_has(self, a: A) -> bool {
        self.contains(a)
    }

    pub open spec fn union<FINITE2: Finiteness>(self, s2: GSet<A, FINITE2>) -> Self {
        ISet::new(|a| self.contains(a) || s2.contains(a))
    }

    pub open spec fn intersect<FINITE2: Finiteness>(self, s2: GSet<A, FINITE2>) -> Self {
        ISet::new(|a| self.contains(a) && s2.contains(a))
    }

    pub open spec fn difference<FINITE2: Finiteness>(self, s2: GSet<A, FINITE2>) -> Self {
        ISet::new(|a| self.contains(a) && !s2.contains(a))
    }

    /// `+` operator, synonymous with `union`
    #[verifier::inline]
    pub open spec fn spec_add(self, s2: ISet<A>) -> ISet<A> {
        self.union(s2)
    }

    /// `*` operator, synonymous with `intersect`
    #[verifier::inline]
    pub open spec fn spec_mul<FINITE2: Finiteness>(self, s2: GSet<A, FINITE2>) -> ISet<A> {
        self.intersect(s2)
    }

    /// `-` operator, synonymous with `difference`
    #[verifier::inline]
    pub open spec fn spec_sub<FINITE2: Finiteness>(self, s2: GSet<A, FINITE2>) -> ISet<A> {
        self.difference(s2)
    }
}

pub broadcast proof fn lemma_iset_map_contains<A, B>(s: ISet<A>, f: spec_fn(A) -> B)
    ensures
        #![trigger s.map(f)]
        forall|y|
            s.map(f).contains(y) <==> (exists|x| s.contains(x) && f(x) == y),
{
    lemma_gset_map_contains(s, f)
}

/// The empty set contains no elements
pub broadcast proof fn lemma_iset_empty<A>(a: A)
    ensures
        !(#[trigger] ISet::<A>::empty().contains(a)),
{
}

pub broadcast proof fn lemma_iset_new<A>(f: spec_fn(A) -> bool, a: A)
    ensures
        #[trigger] ISet::new(f).contains(a) == f(a),
{
}

/// The result of inserting element `a` into set `s` must contains `a`.
pub broadcast proof fn lemma_iset_insert_same<A>(s: ISet<A>, a: A)
    ensures
        #[trigger] s.insert(a).contains(a),
{
}

/// If `a1` does not equal `a2`, then the result of inserting element `a2` into set `s`
/// must contain `a1` if and only if the set contained `a1` before the insertion of `a2`.
pub broadcast proof fn lemma_iset_insert_different<A>(s: ISet<A>, a1: A, a2: A)
    requires
        a1 != a2,
    ensures
        #[trigger] s.insert(a2).contains(a1) == s.contains(a1),
{
}

/// The result of removing element `a` from set `s` must not contain `a`.
pub broadcast proof fn lemma_iset_remove_same<A>(s: Set<A>, a: A)
    ensures
        !(#[trigger] s.remove(a).contains(a)),
{
}

/// Removing an element `a` from a set `s` and then inserting `a` back into the set`
/// is equivalent to the original set `s`.
pub broadcast proof fn lemma_iset_remove_insert<A>(s: ISet<A>, a: A)
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
            lemma_iset_remove_different(s, aa, a);
            lemma_iset_insert_different(s.remove(a), aa, a);
        }
    };
    assert forall|aa| #![all_triggers] s.contains(aa) implies s.remove(a).insert(a).contains(
        aa,
    ) by {
        if a == aa {
            lemma_iset_insert_same(s.remove(a), a);
        } else {
            lemma_iset_remove_different(s, aa, a);
            lemma_iset_insert_different(s.remove(a), aa, a);
        }
    };
    lemma_iset_ext_equal(s.remove(a).insert(a), s);
}

/// If `a1` does not equal `a2`, then the result of removing element `a2` from set `s`
/// must contain `a1` if and only if the set contained `a1` before the removal of `a2`.
pub broadcast proof fn lemma_iset_remove_different<A>( s: ISet<A>, a1: A, a2: A,)
    requires
        a1 != a2,
    ensures
        #[trigger] s.remove(a2).contains(a1) == s.contains(a1),
{
}

/// The intersection of sets `s1` and `s2` contains element `a` if and only if
/// both `s1` and `s2` contain `a`.
pub broadcast proof fn lemma_iset_intersect<A>( s1: ISet<A>, s2: ISet<A>, a: A,)
    ensures
        #[trigger] s1.intersect(s2).contains(a) == (s1.contains(a) && s2.contains(a)),
{
}

/// The set difference between `s1` and `s2` contains element `a` if and only if
/// `s1` contains `a` and `s2` does not contain `a`.
pub broadcast proof fn lemma_iset_difference<A>( s1: ISet<A>, s2: ISet<A>, a: A,)
    ensures
        #[trigger] s1.difference(s2).contains(a) == (s1.contains(a) && !s2.contains(a)),
{
}

/// The complement of set `s` contains element `a` if and only if `s` does not contain `a`.
pub broadcast proof fn lemma_iset_complement<A>(s: ISet<A>, a: A)
    ensures
        #[trigger] s.complement().contains(a) == !s.contains(a),
{
}

pub broadcast proof fn lemma_iset_ext_equal<A>( s1: ISet<A>, s2: ISet<A>,)
    ensures
        #[trigger] (s1 =~= s2) <==> (forall|a: A| s1.contains(a) == s2.contains(a))
{
    GSet::lemma_set_ext_equal(s1, s2)
}

/// The result of inserting an element `a` into a finite set `s` is also finite.
/// This conclusion is automatic for finite `Set`s, but still useful for SMT-`.finite()` `ISet`s.
pub broadcast proof fn lemma_set_insert_finite<A>(s: ISet<A>, a: A)
    requires
        s.finite(),
    ensures
        #[trigger] s.insert(a).finite(),
{
    broadcast use GSet::cast_finiteness_properties;

    lemma_gset_finite_from_type(s.to_finite().insert(a));
    lemma_congruence_extensionality(s, s.to_finite());
    s.to_finite().insert(a).congruent_infiniteness(s.insert(a));
}

/// The result of removing an element `a` from a finite set `s` is also finite.
/// This conclusion is automatic for finite `Set`s, but still useful for SMT-`.finite()` `ISet`s.
pub broadcast proof fn lemma_set_remove_finite<A>(s: ISet<A>, a: A)
    requires
        s.finite(),
    ensures
        #[trigger] s.remove(a).finite(),
{
    broadcast use GSet::cast_finiteness_properties;

    lemma_gset_finite_from_type(s.to_finite().remove(a));
    lemma_congruence_extensionality(s, s.to_finite());
    s.to_finite().remove(a).congruent_infiniteness(s.remove(a));
}

/// The union of two finite sets is finite.
/// This conclusion is automatic for `.union` on finite `Set`s, but helpful for `ISet`s and
/// `generic_union`s.
pub broadcast proof fn lemma_set_union_finite<A>(s1: ISet<A>, s2: ISet<A>)
    requires
        s1.finite(),
        s2.finite(),
    ensures
        #[trigger] s1.union(s2).finite(),
{
    assert(s1.union(s2) == s1.generic_union(s2));
    lemma_set_generic_union_finite(s1, s2);
}

/// The intersection of two finite sets is finite.
/// This conclusion is automatic for `.intersect` on finite `Set`s, but helpful for `ISet`s and
/// `generic_intersect`s.
pub broadcast proof fn lemma_set_intersect_finite<A>(s1: ISet<A>, s2: ISet<A>)
    requires
        s1.finite() || s2.finite(),
    ensures
        #[trigger] s1.intersect(s2).finite(),
{
}

/// The set difference between two finite sets is finite.
/// This conclusion is automatic for `.difference` on finite `Set`s, but helpful for `ISet`s and
/// `generic_difference`s.
pub broadcast proof fn lemma_set_difference_finite<A>(s1: ISet<A>, s2: ISet<A>)
    requires
        s1.finite(),
    ensures
        #[trigger] s1.difference(s2).finite(),
{
}

/// An non-`finite()` ISet `s` contains the element `s.choose()`.
/// Note here 'infinite' means not-SMT-finite. To illustrate,
/// ISet::empty() is type-infinite but not SMT-infinite.
pub broadcast proof fn lemma_iset_choose_infinite<A>(s: ISet<A>)
    requires
        !s.finite(),
    ensures
        #[trigger] s.contains(s.choose()),
{
    lemma_gset_choose_infinite(s)
}

//------------------------------------------------------------------------------

// 'iset' macro, so that the macro name prevents the need for type inference
// of the FINITE parameter.
#[doc(hidden)]
#[macro_export]
macro_rules! iset_internal {
    [$($elem:expr),* $(,)?] => {
        $crate::vstd::iset::ISet::empty()
            $(.insert($elem))*
    };
}

#[macro_export]
macro_rules! iset {
    [$($tail:tt)*] => {
        ::verus_builtin_macros::verus_proof_macro_exprs!($crate::vstd::iset::iset_internal!($($tail)*))
    };
}

pub use iset_internal;
pub use iset;

//////////////////////////////////////////////////////////////////////////////
/// The empty set has length 0.
pub broadcast proof fn lemma_iset_empty_len<A>()
    ensures
        #[trigger] ISet::<A>::empty().len() == 0,
{
    lemma_gset_empty_len();
}

pub broadcast proof fn lemma_iset_map_insert<A, B>(
    s: ISet<A>,
    f: spec_fn(A) -> B,
    a: A,
)
    ensures
        #[trigger] s.insert(a).map(f) == s.map(f).insert(f(a)),
{
    lemma_gset_map_insert(s, f, a);
}


pub broadcast proof fn lemma_iset_map_len<A, B>(
    s: ISet<A>,
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

pub broadcast proof fn lemma_iset_len_empty<A>(s: ISet<A>)
    requires
        s.finite(),
    ensures
        #[trigger] s.len() == 0 ==> ISet::<A>::empty() == s,
{
    lemma_gset_len_empty(s);
}

/// The result of inserting an element `a` into a finite set `s` has length
/// `s.len() + 1` if `a` is not already in `s` and length `s.len()` otherwise.
pub broadcast proof fn lemma_iset_insert_len<A>(s: ISet<A>, a: A)
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
pub broadcast proof fn lemma_iset_remove_len<A>(s: ISet<A>, a: A)
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
pub broadcast proof fn lemma_iset_contains_len<A>(s: ISet<A>, a: A)
    requires
        #[trigger] s.contains(a),
    ensures
        #[trigger] s.len() != 0,
{
    lemma_gset_contains_len(s, a);
}

/// A finite set `s` contains the element `s.choose()` if it has length greater than 0.
pub broadcast proof fn lemma_iset_choose_len<A>(s: ISet<A>)
    requires
        s.finite(),
        #[trigger] s.len() != 0,
    ensures
        #[trigger] s.contains(s.choose()),
{
    lemma_gset_choose_len(s);
}

//////////////////////////////////////////////////////////////////////////////

pub broadcast proof fn lemma_to_finite_len<A>(s: ISet<A>)
    requires
        s.finite(),
    ensures
        #[trigger] s.to_finite().len() == s.len(),
    decreases s.len(),
{
    broadcast use lemma_gset_empty_len;
    broadcast use lemma_gset_remove_len;
    broadcast use lemma_gset_len_empty;
    broadcast use GSet::cast_finiteness_properties;
    broadcast use lemma_set_remove_finite;
    broadcast use lemma_gset_choose_len;

    if s.len() == 0 {
        lemma_congruence_extensionality(s.to_finite(), GSet::<A, Finite>::empty());
    } else {
        let x = s.choose();
        lemma_to_finite_len(s.remove(x));
        // Not sure why this required so much more proof than Chris' draft. His draft got to enjoy
        // group_set_lemmas, but I can't figure out which one was doing the work that avoided this
        // step.
        let fr = s.to_finite().remove(x);
        let rf = s.remove(x).to_finite();
        assert(fr.congruent(rf)) by {
            assert forall|e| fr.contains(e) implies rf.contains(e) by {
                assert(s.contains(e));
            }
            assert forall|e| rf.contains(e) implies fr.contains(e) by {
                assert(s.contains(e));
            }
        }
        lemma_congruence_extensionality(s.to_finite().remove(x), s.remove(x).to_finite());
    }
}

} // verus!
