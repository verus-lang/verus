#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] multiset_basics code! {
        use crate::pervasive::multiset::*;

        #[proof]
        pub fn commutative<V>(a: Multiset<V>, b: Multiset<V>)
        {
            ensures(equal(a.add(b), b.add(a)));

            assert(a.add(b).ext_equal(b.add(a)));
        }

        #[proof]
        pub fn associative<V>(a: Multiset<V>, b: Multiset<V>, c: Multiset<V>)
        {
            ensures(equal(
                a.add(b.add(c)),
                a.add(b).add(c)));

            assert(a.add(b.add(c)).ext_equal(
                a.add(b).add(c)));
        }

        #[proof]
        pub fn insert2<V>(a: V, b: V) {
            ensures(equal(
                Multiset::empty().insert(a).insert(b),
                Multiset::empty().insert(b).insert(a)));

            assert(
                Multiset::empty().insert(a).insert(b).ext_equal(
                Multiset::empty().insert(b).insert(a)));
        }

        #[proof]
        pub fn insert2_count<V>(a: V, b: V, c: V) {
            requires(!equal(a, b) && !equal(b, c) && !equal(c, a));

            assert(Multiset::empty().insert(a).insert(b).count(a) == 1);
            assert(Multiset::empty().insert(a).insert(b).count(b) == 1);
            assert(Multiset::empty().insert(a).insert(b).count(c) == 0);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] multiset_fail code! {
        use crate::pervasive::multiset::*;

        #[proof]
        pub fn insert2_fail<V>(a: V, b: V, c: V) {
            // should fail because we do not have precondition `a != b`
            assert(Multiset::empty().insert(a).insert(b).count(a) == 1); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] multiset_fail2 code! {
        use crate::pervasive::multiset::*;

        #[proof]
        pub fn add_fail<V>(a: Multiset<V>, b: Multiset<V>)
        {
            ensures(equal(a.add(b), a.add(a)));

            assert(a.add(b).ext_equal(a.add(a))); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}
