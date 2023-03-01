#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;
#[allow(unused_imports)]
use crate::pervasive::*;
#[allow(unused_imports)]
use crate::pervasive::set::*;

verus! {

impl<A> Set<A> {
    pub proof fn is_empty(self) -> (b: bool)
        requires
            self.finite(),
        ensures
            b <==> self.finite() && self.len() == 0,
            b <==> self.ext_equal(Set::empty()),
    {
        if self.finite() && self.len() == 0 {
            lemma_len0_is_empty::<A>(self);
        }
        self.ext_equal(Set::empty())
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
    assert(s.ext_equal(Set::empty()));
}

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
        assert(s1.union(s2).ext_equal(s2));
    } else {
        let a = s1.choose();
        if s2.contains(a) {
            assert(s1.union(s2).ext_equal(s1.remove(a).union(s2)));
        } else {
            assert(s1.union(s2).remove(a).ext_equal(s1.remove(a).union(s2)));
        }
        lemma_len_union::<A>(s1.remove(a), s2);
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
        assert(s1.intersect(s2).ext_equal(s1));
    } else {
        let a = s1.choose();
        assert(s1.intersect(s2).remove(a).ext_equal(s1.remove(a).intersect(s2)));
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
    assert(s2.intersect(s1).ext_equal(s1));
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
        assert(s1.difference(s2).ext_equal(s1));
    } else {
        let a = s1.choose();
        assert(s1.difference(s2).remove(a).ext_equal(s1.remove(a).difference(s2)));
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
        assert(set_int_range(lo, hi).ext_equal(Set::empty()));
    } else {
        lemma_int_range(lo, hi - 1);
        assert(set_int_range(lo, hi - 1).insert(hi - 1).ext_equal(set_int_range(lo, hi)));
    }
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
        ::builtin_macros::verus_proof_macro_exprs!($crate::pervasive::set_lib::assert_sets_equal_internal!($($tail)*))
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
        #[verifier::spec] let s1 = $crate::pervasive::set_lib::check_argument_is_set($s1);
        #[verifier::spec] let s2 = $crate::pervasive::set_lib::check_argument_is_set($s2);
        ::builtin::assert_by(::builtin::equal(s1, s2), {
            ::builtin::assert_forall_by(|$elem $( : $t )?| {
                ::builtin::ensures(
                    ::builtin::imply(s1.contains($elem), s2.contains($elem))
                    &&
                    ::builtin::imply(s2.contains($elem), s1.contains($elem))
                );
                { $bblock }
            });
            $crate::pervasive::assert(s1.ext_equal(s2));
        });
    }
}

pub use assert_sets_equal_internal;
pub use assert_sets_equal;

} // verus!
