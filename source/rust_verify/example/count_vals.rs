// TODO: finish proof
use vstd::prelude::*;
use vstd::relations::sorted_by;

verus! {

pub open spec fn seq_count_value<A>(s: Seq<A>, a: A) -> nat
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        ((if s.last() == a {
            1nat
        } else {
            0nat
        }) + seq_count_value(s.drop_last(), a)) as nat
    }
}

pub proof fn lemma_seq_count_value_zero<A>(s: Seq<A>, a: A)
    requires
        forall|i: nat| i < s.len() ==> s[i as int] != a,
    ensures
        seq_count_value(s, a) == 0,
    decreases s.len(),
{
    if s.len() == 0 {
    } else {
        assert(s.last() != a);
        lemma_seq_count_value_zero(s.drop_last(), a);
    }
}

pub proof fn lemma_seq_drop_index_count_value<A>(s: Seq<A>, i: nat, a: A)
    requires
        i < s.len(),
        s[i as int] == a,
        forall|j: nat| i < j < s.len() ==> s[j as int] != a,
    ensures
        seq_count_value(s.subrange(0, i as int) + s.subrange((i + 1) as int, s.len() as int), a)
            == seq_count_value(s, a) - 1,
    decreases s.len(),
{
    if i == s.len() - 1 {
        assert(seq_count_value(
            s.subrange(0, i as int) + s.subrange((i + 1) as int, s.len() as int),
            a,
        ) == seq_count_value(s, a) - 1);
    } else {
        lemma_seq_drop_index_count_value(s.drop_last(), i, a);
        assert(seq_count_value(
            s.drop_last().subrange(0, i as int) + s.drop_last().subrange(
                (i + 1) as int,
                s.len() - 1 as int,
            ),
            a,
        ) == seq_count_value(s.drop_last(), a) - 1);
        assert(s.drop_last().subrange(0, i as int) == s.subrange(0, i as int));
        assert(s.drop_last().subrange((i + 1) as int, s.len() - 1 as int) == s.subrange(
            (i + 1) as int,
            s.len() - 1 as int,
        ));
        reveal_with_fuel(seq_count_value, 4);
        assert(seq_count_value(
            s.subrange(0, i as int) + s.subrange((i + 1) as int, s.len() - 1 as int),
            a,
        ) == seq_count_value(s.drop_last(), a) - 1);
        assert(seq_count_value(s.drop_last(), a) - 1 == seq_count_value(s, a) - 1);
        assert((s.subrange(0, i as int) + s.subrange((i + 1) as int, s.len() as int)).last()
            == s.last());
        assume(seq_count_value(
            s.subrange(0, i as int) + s.subrange((i + 1) as int, s.len() - 1 as int),
            a,
        ) == seq_count_value(
            s.subrange(0, i as int) + s.subrange((i + 1) as int, s.len() as int),
            a,
        ));  // TODO
    }
}

pub proof fn lemma_multiset_matching_sequences<A>(s1: Seq<A>, s2: Seq<A>)
    requires
        s1.len() == s2.len(),
        forall|a: A| seq_count_value(s1, a) == seq_count_value(s2, a),
    ensures
        s1.to_multiset() == s2.to_multiset(),
    decreases s1.len(),
{
    reveal_with_fuel(seq_count_value, 4);
    s1.to_multiset_ensures();
    s2.to_multiset_ensures();
    if forall|a: A| seq_count_value(s1, a) == 0 {
        assert(forall|a: A| seq_count_value(s2, a) == 0);
        if s1.len() != 0 {
            let x = s1.last();
            assert(seq_count_value(s1, x) >= 1);
        }
        assert(s1.to_multiset() == s2.to_multiset());
    } else {
        let a = s1.last();
        assert(seq_count_value(s1, a) == seq_count_value(s2, a));
        if forall|i2: nat| i2 < s2.len() ==> s2[i2 as int] != a {
            lemma_seq_count_value_zero(s2, a);
            assert(seq_count_value(s2, a) == 0);
            assert(false);
        }
        assert(exists|i2: nat|
            i2 < s2.len() && s2[i2 as int] == a && forall|j: nat|
                i2 < j < s2.len() ==> s2[j as int] != a) by {
            assert(exists|i2: nat| i2 < s2.len() && s2[i2 as int] == a);
            if forall|i2: nat|
                (i2 < s2.len() ==> s2[i2 as int] != a) || exists|j: nat|
                    i2 < j < s2.len() ==> s2[j as int] != a {
                // ... ???
                assume(false);
            }
        }
        let i2 = choose|i2: nat|
            i2 < s2.len() && s2[i2 as int] == a && forall|j: nat|
                i2 < j < s2.len() ==> s2[j as int] != a;
        let s1_d = s1.drop_last();
        s1_d.to_multiset_ensures();
        //assert(s1_d.to_multiset() == s1.to_multiset().remove(a));
        let s2_d = s2.subrange(0int, i2 as int) + s2.subrange((i2 + 1) as int, s2.len() as int);
        s2_d.to_multiset_ensures();
        //assert(s2_d.to_multiset() == s1.to_multiset().remove(a));
        assert(seq_count_value(s1_d, a) == seq_count_value(s1, a) - 1);
        lemma_seq_drop_index_count_value(s2, i2, a);
        assert forall|aa: A| seq_count_value(s1_d, aa) == seq_count_value(s2_d, aa) by {
            if a == aa {
                assert(seq_count_value(s1_d, aa) == seq_count_value(s2_d, aa));
            } else {
                assume(seq_count_value(s1_d, aa) == seq_count_value(s2_d, aa));  // TODO
            }
        }
        lemma_multiset_matching_sequences(s1_d, s2_d);
        //assert(s1_d.to_multiset().insert(a) == s2_d.to_multiset().insert(a));
        assume(s1.to_multiset() == s2.to_multiset());  // TODO
    }
}

} // verus!
