#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;
#[allow(unused_imports)]
use crate::pervasive::*;
#[allow(unused_imports)]
use crate::pervasive::set::*;

/// `Multiset<V>` is an abstract multiset type for specifications.
///
/// `Multiset<V>` can be encoded as a (total) map from elements to natural numbers,
/// where the number of nonzero entries is finite.
///
/// Multisets can be constructed in a few different ways:
///  * [`Multiset::empty()`] constructs an empty multiset.
///  * By manipulating existings multisets with [`Multiset::add`], [`Multiset::insert`],
///    [`Multiset::sub`], [`Multiset::remove`], or [`Multiset::filter`].
///  * TODO: `multiset!` constructor macro, multiset from set, from map, etc.
///
/// To prove that two multisets are equal, it is usually easiest to use the 
/// [`assert_multisets_equal!`] macro.

// We could in principle implement the Multiset via an inductive datatype
// and so we can mark its type argument as strictly_positive.

#[verifier(external_body)]
pub struct Multiset<#[verifier(strictly_positive)] V> {
    dummy: std::marker::PhantomData<V>,
}

impl<V> Multiset<V> {
    fndecl!(pub fn count(self, value: V) -> nat);

    fndecl!(pub fn empty() -> Self);
    fndecl!(pub fn singleton(v: V) -> Self);
    fndecl!(pub fn add(self, m2: Self) -> Self);
    fndecl!(pub fn sub(self, m2: Self) -> Self);

    /// Inserts one instance the value `v` into the multiset.
    ///
    /// This always increases the total size of the multiset by 1.

    #[spec] #[verifier(publish)]
    pub fn insert(self, v: V) -> Self {
        self.add(Self::singleton(v))
    }

    /// Removes one instance of the value `v` from the multiset.
    ///
    /// If `v` was absent from the multiset, then the multiset is unchanged.

    #[spec] #[verifier(publish)]
    pub fn remove(self, v: V) -> Self {
        self.sub(Self::singleton(v))
    }

    /// Returns `true` is the left argument is contained in the right argument,
    /// that is, if for each value `v`, the number of occurences in the left
    /// is at most the number of occurences in the right.

    #[spec] #[verifier(publish)]
    pub fn le(self, m2: Self) -> bool {
        forall(|v: V| self.count(v) <= m2.count(v))
    }

    /// Returns true if the two multisets are pointwise equal, i.e.,
    /// for every value `v: V`, the counts are the same in each multiset.
    /// This is equivalent to the multisets actually being equal
    /// by [`axiom_multiset_ext_equal`].
    ///
    /// To prove that two maps are equal via extensionality, it is generally easier
    /// to use the [`assert_multisets_equal!`] macro, rather than using `ext_equal` directly.

    #[spec] #[verifier(publish)]
    pub fn ext_equal(self, m2: Self) -> bool {
        forall(|v: V| self.count(v) == m2.count(v))
    }

    fndecl!(pub fn len(self) -> nat);

    // TODO define this in terms of a more general constructor?
    fndecl!(pub fn filter<F: Fn(V) -> bool>(self, f: F) -> Self);

    // TODO(tjhance) flesh out remaining proof-mode functions
    // (note: for collections of 'proof' objects I usually advise using maps when possible)

    #[proof]
    #[verifier(external_body)]
    #[verifier(returns(proof))]
    pub fn proof_remove(#[proof] &mut self, #[spec] v: V) -> V {
        requires(old(self).count(v) >= 1);
        ensures(|out_v: V|
            equal(out_v, v) && equal(*self, old(self).remove(v))
        );

        unimplemented!();
    }
}

// Specification of `empty`

#[proof]
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub fn axiom_multiset_empty<V>(v: V) {
    ensures(Multiset::empty().count(v) == 0);
}

// Specification of `singleton`

#[proof]
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub fn axiom_multiset_singleton<V>(v: V) {
    ensures(Multiset::singleton(v).count(v) == 1);
}

#[proof]
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub fn axiom_multiset_singleton_different<V>(v: V, w: V) {
    ensures(!equal(v, w) >>= Multiset::singleton(v).count(w) == 0);
}

// Specification of `add`

#[proof]
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub fn axiom_multiset_add<V>(m1: Multiset<V>, m2: Multiset<V>, v: V) {
    ensures(m1.add(m2).count(v) == m1.count(v) + m2.count(v));
}

// Specification of `sub`

#[proof]
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub fn axiom_multiset_sub<V>(m1: Multiset<V>, m2: Multiset<V>, v: V) {
    ensures(m1.sub(m2).count(v) ==
        if m1.count(v) >= m2.count(v) { m1.count(v) - m2.count(v) } else { 0 });
}

// Extensional equality

#[proof]
#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub fn axiom_multiset_ext_equal<V>(m1: Multiset<V>, m2: Multiset<V>) {
    ensures(m1.ext_equal(m2) == equal(m1, m2));
}

verus!{

// Specification of `len`

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_len_empty<V>()
    ensures (#[trigger] Multiset::<V>::empty().len()) == 0,
{}

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_len_singleton<V>(v: V)
    ensures (#[trigger] Multiset::<V>::singleton(v).len()) == 1,
{}

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_len_add<V>(m1: Multiset<V>, m2: Multiset<V>)
    ensures (#[trigger] m1.add(m2).len()) == m1.len() + m2.len(),
{}

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_count_le_len<V>(m: Multiset<V>, v: V)
    ensures #[trigger] m.count(v) <= #[trigger] m.len()
{}

// Specification of `filter`

#[verifier(external_body)]
#[verifier(broadcast_forall)]
pub proof fn axiom_filter_count<V, F: Fn(V) -> bool>(m: Multiset<V>, f: F, v: V)
    ensures (#[trigger] m.filter(f).count(v)) ==
        if f(v) { m.count(v) } else { 0 }
{}

}

#[macro_export]
macro_rules! assert_multisets_equal {
    ($m1:expr, $m2:expr $(,)?) => {
        assert_multisets_equal!($m1, $m2, key => { })
    };
    ($m1:expr, $m2:expr, $k:ident $( : $t:ty )? => $bblock:block) => {
        #[spec] let m1 = $m1;
        #[spec] let m2 = $m2;
        ::builtin::assert_by(::builtin::equal(m1, m2), {
            ::builtin::assert_forall_by(|$k $( : $t )?| {
                ::builtin::ensures([
                    ::builtin::equal(m1.count($k), m2.count($k))
                ]);
                { $bblock }
            });
            $crate::pervasive::assert(m1.ext_equal(m2));
        });
    }
}
