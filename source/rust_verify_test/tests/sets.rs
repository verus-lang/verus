#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test_len verus_code! {
        use vstd::set::*;

        proof fn test_len<A>(s: Set<A>) {
            assert(s.len() as int >= 0);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_len_fails verus_code! {
        use vstd::set::*;

        proof fn test_len<A>(s1: Set<A>, s2: Set<A>) {
            assert(s1.len() == s2.len()); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test1 verus_code! {
        use vstd::set::*;
        use vstd::set_lib::*;

        proof fn test_set() {
            let nonneg = Set::new(|i: int| i >= 0);
            assert(forall|i: int| nonneg.contains(i) == (i >= 0));
            let pos1 = nonneg.filter(|i: int| i > 0);
            assert(forall|i: int| pos1.contains(i) == (i > 0));
            let pos2 = nonneg.map(|i: int| i + 1);
            assert forall|i: int| pos2.contains(i) == (i > 0) by {
                assert(pos2.contains(i) == nonneg.contains(i - 1));
            }
            assert(forall|i: int| pos2.contains(i) == (i > 0));
            assert(pos1 =~= pos2);
            assert(pos1 === pos2);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test1_fails1 verus_code! {
        use vstd::set::*;

        pub closed spec fn set_map<A>(s: Set<A>, f: spec_fn(A) -> A) -> Set<A> {
            Set::new(|a: A| exists|x: A| s.contains(x) && a === f(x))
        }

        proof fn test_set() {
            let nonneg = Set::new(|i: int| i >= 0);
            assert(forall|i: int| nonneg.contains(i) == (i >= 0));
            let pos1 = nonneg.filter(|i: int| i > 0);
            assert(forall|i: int| pos1.contains(i) == (i > 0));
            let pos2 = set_map(nonneg, |i: int| i + 1);
            assert forall|i: int| pos2.contains(i) == (i > 0) by {} // FAILS
            assert(forall|i: int| pos2.contains(i) == (i > 0));
            assert(pos1 =~= pos2);
            assert(pos1 === pos2);
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_choose_assert_witness verus_code! {
        use vstd::set::*;

        #[verifier(opaque)]
        spec fn f(x: int) -> bool {
            true
        }

        proof fn test_witness() {
            assume(exists|x: int| f(x));

            let s = Set::new(|x: int| f(x));
            assert(exists|x: int| f(x) && s.contains(x));

            assert(s.contains(s.choose()));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_choose_fails_witness verus_code! {
        use vstd::set::*;

        #[verifier(opaque)]
        spec fn f(x: int) -> bool {
            true
        }

        proof fn test_witness() {
            assume(exists|x: int| f(x));

            let s = Set::new(|x: int| f(x));

            assert(s.contains(s.choose())); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_set_fold verus_code! {
        use vstd::set::*;

        proof fn test() {
            let s: Set<nat> = set![9];
            broadcast use {fold::lemma_fold_insert, fold::lemma_fold_empty};
            assert(s.finite());
            assert(s.len() > 0);
            assert(s.fold(0, |p: nat, a: nat| p + a) == 9);

            assert(set![].fold(0, |p: nat, a: nat| p + a) == 0);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_set_build verus_code! {
        use vstd::set::*;

        proof fn test1() {
            let s = set_build!{ (x, x): (u8, u8) | x: u8 };
            assert(s.finite());
            let z = Set::new(|p: (u8, u8)| p.0 == p.1);
            assert(s == z);
        }

        proof fn test2() {
            let s = set_build!{ (x, x): (u8, u8) | exists x: u8 };
            let z = Set::new(|p: (u8, u8)| p.0 == p.1);

            // assert(s == z); // FAILS by itself, because of the "exists x: u8"

            assert(s == z) by {
                assert forall|p: (u8, u8)| p.0 == p.1 implies #[trigger] s.contains(p) by {
                    // Exhibit the witness x of type u8 to trigger the "exists":
                    assert(set_build!{ x: u8 }.contains(p.0));
                }
            }
        }

        proof fn test3() {
            let s = set_build!{ (x, y, x - y): (int, int, int) | x: int in 10..20, y: int in x..20, x + y != 25 };
            assert(s.finite());
            let z = Set::new(|t: (int, int, int)| 10 <= t.0 < 20 && t.0 <= t.1 < 20 && t.0 + t.1 != 25 && t.2 == t.0 - t.1);
            assert(s == z);
        }
    } => Ok(())
}
