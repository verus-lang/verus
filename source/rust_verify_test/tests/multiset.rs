#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] multiset_basics verus_code! {
        use crate::pervasive::multiset::*;

        pub proof fn commutative<V>(a: Multiset<V>, b: Multiset<V>)
            ensures
                a.add(b) === b.add(a),
        {
            assert(a.add(b).ext_equal(b.add(a)));
        }

        pub proof fn associative<V>(a: Multiset<V>, b: Multiset<V>, c: Multiset<V>)
            ensures
                a.add(b.add(c)) ===
                a.add(b).add(c),
        {
            assert(a.add(b.add(c)).ext_equal(
                a.add(b).add(c)));
        }

        pub proof fn insert2<V>(a: V, b: V)
            ensures
                Multiset::empty().insert(a).insert(b) ===
                Multiset::empty().insert(b).insert(a),
        {
            assert(
                Multiset::empty().insert(a).insert(b).ext_equal(
                Multiset::empty().insert(b).insert(a)));
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
            assert(a.add(b).sub(b).ext_equal(a));
        }

        pub proof fn sub_add_cancel<V>(a: Multiset<V>, b: Multiset<V>)
            requires
                b.le(a),
            ensures
                a.sub(b).add(b) === a,
        {
            assert(a.sub(b).add(b).ext_equal(a));
        }

    } => Ok(())
}

test_verify_one_file! {
    #[test] multiset_fail verus_code! {
        use crate::pervasive::multiset::*;

        pub proof fn insert2_fail<V>(a: V, b: V, c: V) {
            // should fail because we do not have precondition `a != b`
            assert(Multiset::empty().insert(a).insert(b).count(a) == 1); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] multiset_fail2 code! {
        use crate::pervasive::multiset::*;

        #[verifier::proof]
        pub fn add_fail<V>(a: Multiset<V>, b: Multiset<V>) {
            ensures(equal(a.add(b), a.add(a)));

            assert(a.add(b).ext_equal(a.add(a))); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] multiset_fail3 code! {
        use crate::pervasive::multiset::*;

        #[verifier::proof]
        pub fn sub_add_cancel<V>(a: Multiset<V>, b: Multiset<V>) {
            // Missing the condition `b.le(a)`
            ensures(equal(a.sub(b).add(b), a));

            assert(a.sub(b).add(b).ext_equal(a)); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}
