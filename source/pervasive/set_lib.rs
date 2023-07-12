#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;
#[allow(unused_imports)]
use crate::pervasive::*;
#[allow(unused_imports)]
use crate::set::*;
#[allow(unused_imports)]
use crate::multiset::Multiset;
#[allow(unused_imports)]
use crate::relations::*;


verus! {

impl<A> Set<A> {
    pub open spec fn is_full(self) -> bool {
        self == Set::<A>::full()
    }

    pub proof fn is_empty(self) -> (b: bool)
        requires
            self.finite(),
        ensures
            b <==> self.finite() && self.len() == 0,
            b <==> self =~= Set::empty(),
    {
        if self.finite() && self.len() == 0 {
            lemma_len0_is_empty::<A>(self);
        }
        self =~= Set::empty()
    }

    pub open spec fn map<B>(self, f: FnSpec(A) -> B) -> Set<B> {
        Set::new(|a: B| exists|x: A| self.contains(x) && a == f(x))
    }

    pub open spec fn fold<E>(self, init: E, f: FnSpec(E, A) -> E) -> E
        decreases
            self.len(),
    {
        if self.finite() {
            if self.len() == 0 {
                init
            } else {
                let a = self.choose();
                self.remove(a).fold(f(init, a), f)
            }
        } else {
            arbitrary()
        }
    }

    /// A singleton set has at least one element and any two elements are equal.
    pub open spec fn is_singleton(self) -> bool{
        &&& self.len()>0
        &&& (forall |x: A, y: A| self.contains(x) && self.contains(y) ==> x==y)
    }

    // pub open spec fn to_multiset(self) -> Multiset<A> {
    //     Multiset::<A>::empty().insert(self.choose()).add(self.remove(self.choose()).to_multiset())
    // }
}

pub proof fn lemma_len0_is_empty<A>(s: Set<A>)
    requires
        s.finite(),
        s.len() == 0,
    ensures
        s == Set::<A>::empty(),
{
    if exists|a: A| s.contains(a) {
        // derive contradiction:
        assert(s.remove(s.choose()).len() + 1 == 0);
    }
    assert(s =~= Set::empty());
}

pub proof fn lemma_singleton_size<A>(s: Set<A>)
    requires
        s.is_singleton(),
    ensures
        s.len() == 1
{
     let elt = choose |elt: A| s.contains(elt);
     assert(s.remove(elt).insert(elt) =~= s);
}

/// The size of a union of two sets is less than or equal to the size of
/// both individual sets combined.
pub proof fn lemma_len_union<A>(s1: Set<A>, s2: Set<A>)
    requires
        s1.finite(),
        s2.finite(),
    ensures
        s1.union(s2).len() <= s1.len() + s2.len(),
    decreases
        s1.len(),
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

pub proof fn lemma_len_union_ind<A>(s1: Set<A>, s2: Set<A>)
    requires
        s1.finite(),
        s2.finite(),
    ensures
        s1.union(s2).len() >= s1.len(),
        s1.union(s2).len() >= s2.len(),
    decreases
        s2.len(),
{
    if s2.len() == 0 {}
    else {
        let y = choose |y: A| s2.contains(y);
        if s1.contains(y) {
            assert(s1.remove(y).union(s2.remove(y)) =~= s1.union(s2).remove(y));
            lemma_len_union_ind(s1.remove(y), s2.remove(y))
        }
        else {
            assert(s1.union(s2.remove(y)) =~= s1.union(s2).remove(y));
            lemma_len_union_ind(s1, s2.remove(y))
        }
    }
}

pub proof fn lemma_len_intersect<A>(s1: Set<A>, s2: Set<A>)
    requires
        s1.finite(),
    ensures
        s1.intersect(s2).len() <= s1.len(),
    decreases
        s1.len(),
{
    if s1.is_empty() {
        assert(s1.intersect(s2) =~= s1);
    } else {
        let a = s1.choose();
        assert(s1.intersect(s2).remove(a) =~= s1.remove(a).intersect(s2));
        lemma_len_intersect::<A>(s1.remove(a), s2);
    }
}

pub proof fn lemma_len_subset<A>(s1: Set<A>, s2: Set<A>)
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

pub proof fn lemma_len_difference<A>(s1: Set<A>, s2: Set<A>)
    requires
        s1.finite(),
    ensures
        s1.difference(s2).len() <= s1.len(),
    decreases
        s1.len(),
{
    if s1.is_empty() {
        assert(s1.difference(s2) =~= s1);
    } else {
        let a = s1.choose();
        assert(s1.difference(s2).remove(a) =~= s1.remove(a).difference(s2));
        lemma_len_difference::<A>(s1.remove(a), s2);
    }
}

pub proof fn lemma_len_filter<A>(s: Set<A>, f: FnSpec(A) -> bool)
    requires
        s.finite(),
    ensures
        s.filter(f).finite(),
        s.filter(f).len() <= s.len(),
    decreases
        s.len(),
{
    lemma_len_intersect::<A>(s, Set::new(f));
}

pub open spec fn set_int_range(lo: int, hi: int) -> Set<int> {
    Set::new(|i: int| lo <= i && i < hi)
}

pub proof fn lemma_int_range(lo: int, hi: int)
    requires
        lo <= hi,
    ensures
        set_int_range(lo, hi).finite(),
        set_int_range(lo, hi).len() == hi - lo,
    decreases
        hi - lo,
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
    decreases x.len()
{
    if x =~= Set::<A>::empty() {}
    else {
        let e = choose |e: A| x.contains(e);
        lemma_subset_equality(x.remove(e), y.remove(e));
    }
}

pub proof fn lemma_map_size<A,B>(x: Set<A>, y: Set<B>, f: FnSpec(A) ->B)
    requires
        forall |a: A| #[trigger] f.requires((a,)),
        injective(f),
        forall |a: A| x.contains(a) ==> y.contains(#[trigger] f(a)),
        forall |b: B| #[trigger] y.contains(b) ==> exists |a: A| x.contains(a) && f(a) == b,
        x.finite(),
        y.finite(),
    ensures
        x.len() == y.len(), 
    decreases x.len(),
{
    if x.len() > 0 {
        let a = choose |a: A| x.contains(a);
        lemma_map_size(x.remove(a), y.remove(f(a)), f);
    }
}

/// In a pre-ordered set, a greatest element is necessarily maximal.
pub proof fn lemma_greatest_implies_maximal<A>(r: FnSpec(A,A) -> bool, max: A, s: Set<A>)
    requires pre_ordering(r),
    ensures is_greatest(r, max, s) ==> is_maximal(r, max, s),
{}

/// In a pre-ordered set, a least element is necessarily minimal.
pub proof fn lemma_least_implies_minimal<A>(r: FnSpec(A,A) -> bool, min: A, s: Set<A>)
    requires pre_ordering(r),
    ensures is_least(r, min, s) ==> is_minimal(r, min, s),
{}

/// In a totally-ordered set, an element is maximal if and only if it is a greatest element.
pub proof fn lemma_maximal_equivalent_greatest<A>(r: FnSpec(A,A) -> bool, max: A, s: Set<A>)
    requires total_ordering(r),
    ensures is_greatest(r, max, s) <==> is_maximal(r, max, s),
{
    assert(is_maximal(r, max, s) ==> forall |x:A| !s.contains(x) || !r(max,x) || r(x,max));
}

/// In a totally-ordered set, an element is maximal if and only if it is a greatest element.
pub proof fn lemma_minimal_equivalent_least<A>(r: FnSpec(A,A) -> bool, min: A, s: Set<A>)
    requires total_ordering(r),
    ensures is_least(r, min, s) <==> is_minimal(r, min, s),
{
    assert(is_minimal(r, min, s) ==> forall |x:A| !s.contains(x) || !r(x,min) || r(min,x));
}

/// In a partially-ordered set, there exists at most one least element.
pub proof fn lemma_least_is_unique<A>(r: FnSpec(A,A) -> bool, s: Set<A>)
    requires partial_ordering(r),
    ensures forall |min: A, min_prime: A| is_least(r, min, s) && is_least(r, min_prime, s) ==> min == min_prime,
{
   assert forall |min: A, min_prime: A| is_least(r, min, s) && is_least(r, min_prime, s) implies min == min_prime by {
        assert(r(min, min_prime));
        assert(r(min_prime, min));
   }
}

/// In a partially-ordered set, there exists at most one greatest element.
pub proof fn lemma_greatest_is_unique<A>(r: FnSpec(A,A) -> bool, s: Set<A>)
    requires partial_ordering(r),
    ensures forall |max: A, max_prime: A| is_greatest(r, max, s) && is_greatest(r, max_prime, s) ==> max == max_prime,
{
   assert forall |max: A, max_prime: A| is_greatest(r, max, s) && is_greatest(r, max_prime, s) implies max == max_prime by {
        assert(r(max_prime, max));
        assert(r(max, max_prime));
   }
}

/// In a totally-ordered set, there exists at most one minimal element.
pub proof fn lemma_minimal_is_unique<A>(r: FnSpec(A,A) -> bool, s: Set<A>)
    requires
        total_ordering(r),
    ensures
        forall |min: A, min_prime: A| is_minimal(r, min, s) && is_minimal(r, min_prime, s) ==> min == min_prime,
{
    assert forall |min: A, min_prime: A| is_minimal(r, min, s) && is_minimal(r, min_prime, s) implies min == min_prime by {
        lemma_minimal_equivalent_least(r,min,s);
        lemma_minimal_equivalent_least(r,min_prime,s);
        lemma_least_is_unique(r,s);
   }
}

/// In a totally-ordered set, there exists at most one maximal element.
pub proof fn lemma_maximal_is_unique<A>(r: FnSpec(A,A) -> bool, s: Set<A>)
    requires
        total_ordering(r),
    ensures
        forall |max: A, max_prime: A| is_maximal(r, max, s) && is_maximal(r, max_prime, s) ==> max == max_prime,
{
    assert forall |max: A, max_prime: A| is_maximal(r, max, s) && is_maximal(r, max_prime, s) implies max == max_prime by {
        lemma_maximal_equivalent_greatest(r,max,s);
        lemma_maximal_equivalent_greatest(r,max_prime,s);
        lemma_greatest_is_unique(r,s);
   }
}  

// pub proof fn lemma_multiset_from_set<A>()
//     ensures
//         forall |s: Set<A>, a: A| 
//             (#[trigger] s.to_multiset().count(a) == 0 <==> (!s.contains(a)))
//             && (s.to_multiset().count(a) == 1 <==> s.contains(a)),
// {}




/***************** Relations *********************/

/// An injective function maps distinct elements of its domain to distinct elements of its codomain.
/// In other words, a function that is one-to-one.
pub open spec fn injective<A, B>(f: FnSpec(A) -> B) -> bool
{
    forall|x1: A, x2: A| #[trigger] f(x1) == #[trigger] f(x2) ==> x1 == x2
}

pub open spec fn commutative<T,U>(r: FnSpec(T,T) -> U) ->bool
{
    forall|x: T, y: T| #[trigger] r(x,y)== #[trigger] r(y,x)
}

pub open spec fn associative<T>(r: FnSpec(T,T) -> T) -> bool{
    forall|x: T, y: T, z: T| #[trigger] r(x,r(y,z)) ==  #[trigger] r(r(x,y),z)
}

pub open spec fn reflexive<T>(r: FnSpec(T,T) -> bool) ->bool{
    forall |x: T| #[trigger] r(x,x)
}

pub open spec fn irreflexive<T>(r: FnSpec(T,T) -> bool) ->bool{
    forall |x: T| #[trigger] r(x,x) == false
}

pub open spec fn antisymmetric<T>(r: FnSpec(T,T) -> bool) ->bool{
    forall|x: T, y: T| #[trigger] r(x,y) && #[trigger] r(y,x) ==> x == y
}

pub open spec fn asymmetric<T>(r: FnSpec(T,T) -> bool) ->bool{
    forall|x: T, y: T| #[trigger] r(x,y) ==> #[trigger] r(y,x) == false
}

pub open spec fn symmetric<T>(r: FnSpec(T,T) -> bool) ->bool{
    forall|x: T, y: T| #[trigger] r(x,y) <==> #[trigger] r(y,x)
}

pub open spec fn connected<T>(r: FnSpec(T,T) -> bool) ->bool{
    forall|x: T, y: T| x != y ==> #[trigger] r(x,y) || #[trigger] r(y,x)
}

pub open spec fn strongly_connected<T>(r: FnSpec(T,T) -> bool) ->bool{
    forall|x: T, y: T| #[trigger] r(x,y) || #[trigger] r(y,x)
}

pub open spec fn transitive<T>(r: FnSpec(T,T) -> bool) -> bool{
    forall|x: T, y: T, z: T| #[trigger] r(x,y) && #[trigger] r(y,z) ==>  #[trigger] r(x,z)
}

pub open spec fn total_ordering<T>(r: FnSpec(T,T) ->bool) ->bool{
    &&& reflexive(r)
    &&& antisymmetric(r)
    &&& transitive(r)
    &&& strongly_connected(r)
}

pub open spec fn strict_total_ordering<T>(r: FnSpec(T,T) ->bool) ->bool{
    &&& irreflexive(r)
    &&& antisymmetric(r)
    &&& transitive(r)
    &&& connected(r)
}

pub open spec fn pre_ordering<T>(r: FnSpec(T,T) ->bool) ->bool{
    &&& reflexive(r)
    &&& transitive(r)
}

pub open spec fn partial_ordering<T>(r: FnSpec(T,T) ->bool) ->bool{
    &&& reflexive(r)
    &&& transitive(r)
    &&& antisymmetric(r)
}

pub open spec fn equivalence_relation<T>(r: FnSpec(T,T) ->bool) ->bool{
    &&& reflexive(r)
    &&& symmetric(r)
    &&& transitive(r)
}

/// An element in an ordered set is called a least element (or a minimum), if it is less than 
/// every other element of the set.
/// 
/// change f to leq bc it is a relation. also these are an ordering relation
pub open spec fn is_least<T>(leq: FnSpec(T,T) ->bool, min: T, s: Set<T>) ->bool{
    s.contains(min) && forall|x: T| s.contains(x) ==> #[trigger] leq(min,x)
}

/// An element in an ordered set is called a minimal element, if no other element is less than it.
pub open spec fn is_minimal<T>(leq: FnSpec(T,T) ->bool, min: T, s: Set<T>) ->bool{
    s.contains(min) && forall|x: T| s.contains(x) && #[trigger] leq(x,min) ==> #[trigger] leq(min,x)
}

/// An element in an ordered set is called a greatest element (or a maximum), if it is greater than 
///every other element of the set.
pub open spec fn is_greatest<T>(leq: FnSpec(T,T) ->bool, max: T, s: Set<T>) ->bool{
    s.contains(max) && forall|x: T| s.contains(x) ==> #[trigger] leq(x,max)
}

/// An element in an ordered set is called a maximal element, if no other element is greater than it.
pub open spec fn is_maximal<T>(leq: FnSpec(T,T) ->bool, max: T, s: Set<T>) ->bool{
    s.contains(max) && forall|x: T| s.contains(x) && #[trigger] leq(max,x) ==> #[trigger] leq(x,max)
}





#[doc(hidden)]
#[verifier(inline)]
pub open spec fn check_argument_is_set<A>(s: Set<A>) -> Set<A> { s }

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
        ::builtin_macros::verus_proof_macro_exprs!($crate::set_lib::assert_sets_equal_internal!($($tail)*))
    };
}

#[macro_export]
#[doc(hidden)]
macro_rules! assert_sets_equal_internal {
    (::builtin::spec_eq($s1:expr, $s2:expr)) => {
        assert_sets_equal_internal!($s1, $s2)
    };
    (::builtin::spec_eq($s1:expr, $s2:expr), $elem:ident $( : $t:ty )? => $bblock:block) => {
        assert_sets_equal_internal!($s1, $s2, $elem $( : $t )? => $bblock)
    };
    ($s1:expr, $s2:expr $(,)?) => {
        assert_sets_equal_internal!($s1, $s2, elem => { })
    };
    ($s1:expr, $s2:expr, $elem:ident $( : $t:ty )? => $bblock:block) => {
        #[verifier::spec] let s1 = $crate::set_lib::check_argument_is_set($s1);
        #[verifier::spec] let s2 = $crate::set_lib::check_argument_is_set($s2);
        ::builtin::assert_by(::builtin::equal(s1, s2), {
            ::builtin::assert_forall_by(|$elem $( : $t )?| {
                ::builtin::ensures(
                    ::builtin::imply(s1.contains($elem), s2.contains($elem))
                    &&
                    ::builtin::imply(s2.contains($elem), s1.contains($elem))
                );
                { $bblock }
            });
            ::builtin::assert_(::builtin::ext_equal(s1, s2));
        });
    }
}

pub use assert_sets_equal_internal;
pub use assert_sets_equal;

} // verus!
