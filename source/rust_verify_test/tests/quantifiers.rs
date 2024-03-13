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
            assert(exists|i: nat| i >= 0 && tr(i as int));
        }

        proof fn test1_inference() {
            assert(tr(300));
            assert(exists|i| 0 <= i && tr(i));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test1_fails verus_code! {
        spec fn tr(i: int) -> bool {
            true
        }

        proof fn test1() {
            assert(exists|i: nat| i >= 0 && tr(i as int)); // FAILS
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
            assert(exists|i: nat| i >= 0 && tr1(i as int) && tr2(i as int));
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
            assert(exists|i: nat| i >= 0 && tr1(i as int) && tr2(i as int));
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
            assert(exists|i: nat| i >= 0 && tr1(i as int) && #[trigger] tr2(i as int));
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
            assert(exists|i: nat| i >= 0 && tr1(i as int) && #[trigger] tr2(i as int)); // FAILS
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_nested_assert_forall_by_regression_155 verus_code! {
        use vstd::map::*;

        pub proof fn test<S, T>() {
            assert forall |m1: Map<S, T>, m2: Map<S, T>, n: S|
                m1.dom().contains(n) && !m2.dom().contains(n) implies
                equal(m1.remove(n).union_prefer_right(m2), m1.union_prefer_right(m2).remove(n))
            by {
                let union1 = m1.remove(n).union_prefer_right(m2);
                let union2 = m1.union_prefer_right(m2).remove(n);
                assert_maps_equal!(union1, union2);
                assert(equal(m1.remove(n).union_prefer_right(m2), union2));
                assert(equal(union1, m1.union_prefer_right(m2).remove(n)));
            }
        }

        pub proof fn test_forall_forall<S, T>() {
            assert forall |m1: Map<S, T>, m2: Map<S, T>, n: S|
                m1.dom().contains(n) && !m2.dom().contains(n) implies
                equal(m1.remove(n).union_prefer_right(m2), m1.union_prefer_right(m2).remove(n))
            by {

                let union1 = m1.remove(n).union_prefer_right(m2);
                let union2 = m1.union_prefer_right(m2).remove(n);

                let mm1 = union1;
                let mm2 = union2;

                assert(equal(mm1, mm2)) by {
                    assert forall |key|
                        imply(#[trigger] mm1.dom().contains(key), mm2.dom().contains(key))
                            && imply(mm2.dom().contains(key), mm1.dom().contains(key))
                            && imply(mm1.dom().contains(key) && mm2.dom().contains(key),
                                equal(mm1.index(key), mm2.index(key)))
                        by { {} }
                    assert(mm1 =~= mm2);
                }

                assume(equal(union1, union2));
                assert(equal(m1.remove(n).union_prefer_right(m2), union2));
                assert(equal(union1, m1.union_prefer_right(m2).remove(n)));
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] manual_trigger verus_code! {
        use vstd::seq::*;
        proof fn test_distinct3(s: Seq<int>)
            requires
                5 <= s.len(),
                forall|i: int, j: int| #![trigger s[i], s[j]]
                    0 <= i < j < s.len() ==> s[i] != s[j],
        {
            assert(s[4] != s[2]);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] assert_forall_triggers_regression_335 verus_code! {
        spec fn f(x:int, y:int) -> bool { true }
        spec fn g(x:int, y:int) -> bool { true }
        spec fn h(x:int, y:int) -> bool { true }
        spec fn i(x:int, y:int) -> int { 5 }

        proof fn test(z:int)
        {
            assert forall |k:int| #![trigger f(k, z)] f(k, z) && g(z, k) ==> f(z, i(z, k)) by { };
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] assert_forall_triggers_regression_470 verus_code! {
        spec fn f(x:int, y:int) -> bool { true }
        spec fn g(x:int, y:int) -> bool { true }
        spec fn h(x:int, y:int) -> bool { true }
        spec fn i(x:int, y:int) -> int { 5 }

        proof fn test(z:int)
        {
            assert forall |k:int| #![auto] f(k, z) && g(z, k) ==> f(z, i(z, k)) by { };
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] assert_forall_invalid_attr verus_code! {
        spec fn f(x:int) -> bool { true }

        proof fn test(z:int)
        {
            assert forall |k:int| #![autos] f(k) by { };
        }
    } => Err(err) => assert_vir_error_msg(err, "expected trigger")
}

test_verify_one_file! {
    #[test] forall_auto_parens_regression_378 verus_code! {
        use vstd::seq::*;
        proof fn foo(s: Seq<int>)
            requires
                5 <= s.len(),
                forall (|i: int, j: int| #![auto]
                    0 <= i < j < s.len() ==> s[i] != s[j]),
        {
            assert(s[4] != s[2]);
        }
    } => Err(err) => assert_vir_error_msg(err, "forall, choose, and exists do not allow parentheses")
}

test_verify_one_file! {
    #[test] test_inner_triggers_broadcast_forall verus_code! {
        mod M {
            pub struct A {}
            impl A {
                pub spec fn f1(&self) -> bool;
                pub spec fn f2(&self) -> bool;
                pub spec fn f3(&self) -> bool;
            }

            #[verifier::external_body]
            pub broadcast proof fn ab(a: A)
                ensures #![trigger a.f1()] (a.f1() ==> a.f2()) && a.f3()
            {
            }
        }

        use M::*;
        proof fn p(a: A)
            requires a.f1(),
            ensures a.f2(),
        {
            broadcast use ab;
        }
    } => Ok(())
}
