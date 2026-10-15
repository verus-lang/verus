use vstd::multiset::*;
/// Various utilties that should eventually be added to vstd
use vstd::prelude::*;
use vstd::set_lib::*;

verus! {

pub open spec fn insert_many<V>(m: Multiset<V>, v: V, count: nat) -> Multiset<V>
    decreases count,
{
    if count == 0 {
        m
    } else {
        insert_many(m, v, (count - 1) as nat).insert(v)
    }
}

pub proof fn insert_many_properties<V>(m: Multiset<V>, v: V, count: nat)
    ensures
        insert_many(m, v, count).count(v) == m.count(v) + count,
        insert_many(m, v, count).len() == m.len() + count,
        forall|w| w != v ==> #[trigger] insert_many(m, v, count).count(w) == m.count(w),
    decreases count,
{
    if count == 0 {
    } else {
        insert_many_properties(m, v, (count - 1) as nat);
    }
}

proof fn multiset_len_sums_counts_bool(m: Multiset<bool>)
    ensures
        m.len() == m.count(true) + m.count(false),
{
    let e = Multiset::empty();
    let m_true = insert_many(e, true, m.count(true));
    let m_new = insert_many(m_true, false, m.count(false));
    insert_many_properties(e, true, m.count(true));
    insert_many_properties(m_true, false, m.count(false));
    assert(m_new == m);
}

/// f is injective on a restricted portion of its domain
pub open spec fn injective_on<X, Y>(f: spec_fn(X) -> Y, s: Set<X>) -> bool {
    forall|x1: X, x2: X|
        s.contains(x1) && s.contains(x2) && #[trigger] f(x1) == #[trigger] f(x2) ==> x1 == x2
}

/// Given an function that's injective on each element of the input set,
/// applying the function to each element the input set to construct
/// another set produces a new set with the same size
pub proof fn lemma_map_size<A, B>(x: Set<A>, y: Set<B>, f: spec_fn(A) -> B)
    requires
        injective_on(f, x),
        forall|a: A| x.contains(a) ==> y.contains(#[trigger] f(a)),
        forall|b: B| (#[trigger] y.contains(b)) ==> exists|a: A| x.contains(a) && f(a) == b,
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

} // verus!
