#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test1 verus_code! {
        spec fn tr(i: int) -> bool {
            true
        }

        proof fn test1() {
            assert(tr(300));
            assert(exists|i: nat| i >= 0 && tr(i));
        }

        proof fn test1_inference() {
            assert(tr(300));
            assert(exists|i| i >= 0 && tr(i));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test1_fails verus_code! {
        spec fn tr(i: int) -> bool {
            true
        }

        proof fn test1() {
            assert(exists|i: nat| i >= 0 && tr(i)); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test2 verus_code! {
        spec fn tr1(i: int) -> bool {
            true
        }

        spec fn tr2(i: int) -> bool {
            true
        }

        proof fn test1() {
            assert(tr1(300));
            assert(exists|i: nat| i >= 0 && tr1(i) && tr2(i));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test3 verus_code! {
        spec fn tr1(i: int) -> bool {
            true
        }

        spec fn tr2(i: int) -> bool {
            true
        }

        proof fn test1() {
            assert(tr2(300));
            assert(exists|i: nat| i >= 0 && tr1(i) && tr2(i));
        }
    } => Ok(())
}

////

test_verify_one_file! {
    #[test] test1g verus_code! {
        spec fn tr<A>(a: A) -> bool {
            true
        }

        proof fn test1() {
            assert(tr::<nat>(300));
            assert(exists|i: nat| i >= 0 && tr(i));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test1g_fails verus_code! {
        spec fn tr<A>(a: A) -> bool {
            true
        }

        proof fn test1() {
            assert(exists|i: nat| i >= 0 && tr(i)); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test2g verus_code! {
        spec fn tr1<A>(a: A) -> bool {
            true
        }

        spec fn tr2<A>(a: A) -> bool {
            true
        }

        proof fn test1() {
            assert(tr1::<nat>(300));
            assert(exists|i: nat| i >= 0 && tr1(i) && tr2(i));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test3g verus_code! {
        spec fn tr1<A>(a: A) -> bool {
            true
        }

        spec fn tr2<A>(a: A) -> bool {
            true
        }

        proof fn test1() {
            assert(tr2::<nat>(300));
            assert(exists|i: nat| i >= 0 && tr1(i) && tr2(i));
        }
    } => Ok(())
}

////

test_verify_one_file! {
    #[test] test4 verus_code! {
        spec fn tr1(i: int) -> bool {
            true
        }

        spec fn tr2(i: int) -> bool {
            true
        }

        proof fn test1() {
            assert(tr2(300));
            assert(exists|i: nat| i >= 0 && tr1(i) && #[trigger] tr2(i));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test4_fails verus_code! {
        spec fn tr1(i: int) -> bool {
            true
        }

        spec fn tr2(i: int) -> bool {
            true
        }

        proof fn test1() {
            assert(tr1(300));
            assert(exists|i: nat| i >= 0 && tr1(i) && #[trigger] tr2(i)); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[ignore] #[test] test_nested_assert_forall_by_regression_155 code! {
        use crate::pervasive::map::*;

        #[proof]
        pub fn test_forall_forall<S, T>() {
            assert_forall_by(|m1: Map<S, T>, m2: Map<S, T>, n: S| {
                requires(m1.dom().contains(n) && !m2.dom().contains(n));
                ensures(equal(m1.remove(n).union_prefer_right(m2), m1.union_prefer_right(m2).remove(n)));

                let union1 = m1.remove(n).union_prefer_right(m2);
                let union2 = m1.union_prefer_right(m2).remove(n);
                #[spec] let m1 = union1;
                #[spec] let m2 = union2;

                ::builtin::assert_by(::builtin::equal(m1, m2), {
                    ::builtin::assert_forall_by(|key| {
                        ::builtin::ensures([((#[trigger]
                        m1.dom().contains(key)) >>= m2.dom().contains(key))
                            && (m2.dom().contains(key) >>= m1.dom().contains(key))
                            && (m1.dom().contains(key) && m2.dom().contains(key) >>=
                                ::builtin::equal(m1.index(key), m2.index(key)))]);
                        { {} }
                    });
                    crate::pervasive::assert(m1.ext_equal(m2));
                });

                assume(equal(union1, union2));
                assert(equal(m1.remove(n).union_prefer_right(m2), union2));
                assert(equal(union1, m1.union_prefer_right(m2).remove(n)));
            });
        }
    } => Ok(())
}
