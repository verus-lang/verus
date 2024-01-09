#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] multiset_basics verus_code! {
        use vstd::multiset::*;

        pub proof fn commutative<V>(a: Multiset<V>, b: Multiset<V>)
            ensures
                a.add(b) === b.add(a),
        {
            assert(a.add(b) =~= b.add(a));
        }

        pub proof fn associative<V>(a: Multiset<V>, b: Multiset<V>, c: Multiset<V>)
            ensures
                a.add(b.add(c)) ===
                a.add(b).add(c),
        {
            assert(a.add(b.add(c)) =~=
                a.add(b).add(c));
        }

        pub proof fn insert2<V>(a: V, b: V)
            ensures
                Multiset::empty().insert(a).insert(b) ===
                Multiset::empty().insert(b).insert(a),
        {
            assert(
                Multiset::empty().insert(a).insert(b) =~=
                Multiset::empty().insert(b).insert(a));
        }

        pub proof fn insert2_count<V>(a: V, b: V, c: V)
            requires
                a !== b && b !== c && c !== a,
        {
            assert(Multiset::empty().insert(a).insert(b).count(a) == 1);
            assert(Multiset::empty().insert(a).insert(b).count(b) == 1);
            assert(Multiset::empty().insert(a).insert(b).count(c) == 0);
        }

        pub proof fn add_sub_cancel<V>(a: Multiset<V>, b: Multiset<V>)
            ensures
                a.add(b).sub(b) === a,
        {
            assert(a.add(b).sub(b) =~= a);
        }

        pub proof fn sub_add_cancel<V>(a: Multiset<V>, b: Multiset<V>)
            requires
                b.subset_of(a),
            ensures
                a.sub(b).add(b) === a,
        {
            assert(a.sub(b).add(b) =~= a);
        }

        pub proof fn choose_count<V>(m: Multiset<V>)
            requires
                m.len() != 0,
        {
            assert(m.count(m.choose()) > 0);
        }

        pub proof fn len_is_zero_if_count_for_each_value_is_zero<V>(m: Multiset<V>)
            requires
                forall |v| m.count(v) == 0,
            ensures
                m.len() == 0,
        {
            if m.len() != 0 {
                assert(m.count(m.choose()) > 0);
            }
        }

    } => Ok(())
}

test_verify_one_file! {
    #[test] multiset_fail verus_code! {
        use vstd::multiset::*;

        pub proof fn insert2_fail<V>(a: V, b: V, c: V) {
            // should fail because we do not have precondition `a != b`
            assert(Multiset::empty().insert(a).insert(b).count(a) == 1); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] multiset_fail2 verus_code! {
        use vstd::multiset::*;

        pub proof fn add_fail<V>(a: Multiset<V>, b: Multiset<V>)
            ensures equal(a.add(b), a.add(a))
        {
            assert(a.add(b) =~= a.add(a)); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] multiset_fail3 verus_code! {
        use vstd::multiset::*;

        pub proof fn sub_add_cancel<V>(a: Multiset<V>, b: Multiset<V>)
            ensures equal(a.sub(b).add(b), a)
        {
            // Missing the condition `b.le(a)`
            assert(a.sub(b).add(b) =~= a); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] multiset_fail4 verus_code! {
        use vstd::multiset::*;

        pub proof fn choose_count<V>(m: Multiset<V>)
        {
            // Missing the precondition `m.len() != 0`
            assert(m.count(m.choose()) > 0); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}
