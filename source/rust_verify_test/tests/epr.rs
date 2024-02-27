#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

const TYPES_TEST_2: &str = verus_code_str! {
    mod TypesTest2 {
        use vstd::prelude::nat;

        pub struct S1(nat);
        pub struct S2(nat);
        pub struct S3(nat);

        pub closed spec const S1Val : S1 = S1(0);
        pub closed spec const S2Val : S2 = S2(0);
        pub closed spec const S3Val : S3 = S3(0);

        pub closed spec(checked) fn s1_s2(x : S1) -> S2
        {
            S2(x.0)
        }

        pub closed spec(checked) fn s2_s1(x : S2) -> S1
        {
            S1(x.0)
        }

        pub closed spec(checked) fn s1_s3(x : S1) -> S3
        {
            S3(x.0)
        }

        pub closed spec(checked) fn s3_s1(x : S3) -> S1
        {
            S1(x.0)
        }

        pub closed spec(checked) fn s2_s3(x : S2) -> S3
        {
            S3(x.0)
        }

        pub closed spec(checked) fn s3_s2(x : S3) -> S2
        {
            S2(x.0)
        }

        pub open spec(checked) fn s1_pred(x : S1) -> bool {
            false
        }

        pub open spec(checked) fn s2_pred(x : S2) -> bool {
            false
        }

        pub open spec(checked) fn s3_pred(x : S3) -> bool {
            false
        }
    }
};

const TYPES_GENERICS: &str = verus_code_str! {
    trait MakeOne {
        spec fn make() -> Self where Self: std::marker::Sized;
    }

    mod EPRData {
        pub struct Foo<K, V> {
            k : K,
            v : V,
        }

        impl<K, V> Foo<K, V> {
            pub open spec fn pred(&self, k: K) -> bool {
                true
            }

            pub open spec fn pred_pair(&self, k: K, v: V) -> bool {
                true
            }

            pub closed spec fn get_k(&self) -> K {
                self.k
            }

            pub closed spec fn get_v(&self) -> V {
                self.v
            }

            pub proof fn foo_prop(&self)
                ensures
                    forall|k : K| self.pred(k) && exists |v : V| self.pred_pair(k, v)
            {
                assume(false);
            }

            pub open spec fn pred_map(&self) -> bool {
                self.pred_pair(self.get_k(), self.get_v())
            }
        }
    }
};

test_verify_one_file! {
    #[test] negate_ensures_pass TYPES_TEST_2.to_string() + verus_code_str! {
        #[verifier::epr_check]
        mod EPRProofTest2 {
            use crate::TypesTest2::*;

            // in EPR, as we negate our ensures clauses
            // so this should pass
            proof fn test()
                ensures
                    forall|y : S2| ((s2_s3(y) == S3Val) || (exists|x: S1| s1_s2(x) == y)),
            {
                assume(false);
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] negate_ensures_arg TYPES_TEST_2.to_string() + verus_code_str! {
        #[verifier::epr_check]
        mod EPRProofTest2 {
            use crate::TypesTest2::*;

            // should also pass if the argument is passed in
            proof fn test(y : S2)
                ensures
                    ((s2_s3(y) == S3Val) || (exists|x: S1| s1_s2(x) == y))
            {
                assume(false);
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] lemma_call_ensures_fail TYPES_TEST_2.to_string() + verus_code_str! {
        #[verifier::epr_check]
        mod EPRProofTest2 {
            use crate::TypesTest2::*;

            // in EPR, as we negate our ensures clauses
            // so this should pass
            proof fn lemma()
                ensures
                    forall|y : S2| ((s2_s3(y) == S3Val) || (exists|x: S1| s1_s2(x) == y)),
            {
                assume(false);
            }

            // not in EPR when lemma1 is called
            // should fail
            proof fn test()
                ensures
                    forall|x : S1| s1_s2(x) == S2Val,
            {
                lemma();
                assume(false);
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "Function not in EPR, quantifier alternation graph contains cycle")
}

test_verify_one_file! {
    #[test] lemma_call_with_arg TYPES_TEST_2.to_string() + verus_code_str! {
        #[verifier::epr_check]
        mod EPRProofTest2 {
            use crate::TypesTest2::*;

            // should also pass if the argument is passed in
            proof fn lemma(y : S2)
                ensures
                    ((s2_s3(y) == S3Val) || (exists|x: S1| s1_s2(x) == y))
            {
                assume(false);
            }

            // should be in EPR when lemma1_mod is called (arg is explicit)
            // should pass
            proof fn test()
                ensures
                    forall|x : S1| s1_s2(x) == S2Val,
            {
                lemma(S2Val);
                assume(false);
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] spec_fn_positive TYPES_TEST_2.to_string() + verus_code_str! {
        #[verifier::epr_check]
        mod EPRProofTest2 {
            use crate::TypesTest2::*;

            // caught by positive polarity
            spec(checked) fn positive(y : S2) -> bool {
                exists|x : S1| s1_s2(x) == y
            }

            proof fn test()
                ensures exists|y : S2| positive(y),
            {
                assume(false);
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "Function not in EPR, quantifier alternation graph contains cycle")
}

test_verify_one_file! {
    #[test] spec_fn_negative TYPES_TEST_2.to_string() + verus_code_str! {
        #[verifier::epr_check]
        mod EPRProofTest2 {
            use crate::TypesTest2::*;

            // caught by negative polarity
            spec(checked) fn negative(y : S2) -> bool {
                forall|x : S1| s1_s2(x) == y
            }

            // should fail
            proof fn test()
                ensures exists|y : S2| negative(y),
            {
                assume(false);
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "Function not in EPR, quantifier alternation graph contains cycle")
}

test_verify_one_file! {
    #[test] negate_ensures_fail TYPES_TEST_2.to_string() + verus_code_str! {
        #[verifier::epr_check]
        mod EPRProofTest2 {
            use crate::TypesTest2::*;

            // should fail
            proof fn test()
                ensures
                    exists|y : S2| #![trigger s2_s3(y)] forall|x : S1| s1_s2(x) == y || s2_s3(y) == S3Val,
            {
                assume(false);
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "Function not in EPR, quantifier alternation graph contains cycle")
}

test_verify_one_file! {
    #[test] lemma_call_ensures_pass TYPES_TEST_2.to_string() + verus_code_str! {
        mod Lemma4Mod {
            use crate::TypesTest2::*;
            pub proof fn lemma()
                ensures
                    exists|y : S2| #![trigger s2_s3(y)] forall|x : S1| s1_s2(x) == y || s2_s3(y) == S3Val,
            {
                assume(false);
            }
        }
        #[verifier::epr_check]
        mod EPRProofTest2 {
            use crate::TypesTest2::*;
            use crate::Lemma4Mod::lemma;

            proof fn test()
                ensures exists|x : S1| s1_s2(x) == S2Val,
            {
                // invoking lemma, which isn't in EPR, is fine as it
                // is used in opposite polarity
                lemma();
                assume(false);
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] implies_polarity_left TYPES_TEST_2.to_string() + verus_code_str! {
        #[verifier::epr_check]
        mod EPRProofTest2 {
            use crate::TypesTest2::*;

            // this should pass, as the forall is double negated
            proof fn test()
                ensures
                    exists|y : S2| (forall|x : S1| s1_s2(x) == y || s2_s3(y) == S3Val) ==> s2_s3(y) == S3Val,
            {
                assume(false);
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] implies_polarity_right TYPES_TEST_2.to_string() + verus_code_str! {
        #[verifier::epr_check]
        mod EPRProofTest2 {
            use crate::TypesTest2::*;

            // this should fail due to second forall from the second part of implication
            proof fn test()
                ensures
                    exists|y : S2| #![trigger s2_s3(y)] (forall|x : S1| s1_s2(x) == y || s2_s3(y) == S3Val) ==> (forall|z : S1| #![trigger s1_s2(z)] s1_s2(z) == y),
            {
                assume(false);
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "Function not in EPR, quantifier alternation graph contains cycle")
}

test_verify_one_file! {
    #[test] negation_polarity_flip TYPES_TEST_2.to_string() + verus_code_str! {
        #[verifier::epr_check]
        mod EPRProofTest2 {
            use crate::TypesTest2::*;

            // this should pass, as negation flips polarity
            proof fn test()
                ensures
                    exists|y : S2| #![trigger s2_s3(y)] !(forall|x : S1| s1_s2(x) == y || s2_s3(y) == S3Val),
            {
                assume(false);
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] function_type_cycle TYPES_TEST_2.to_string() + verus_code_str! {
        #[verifier::epr_check]
        mod EPRProofTest2 {
            use crate::TypesTest2::*;

            // should fail for function cycle
            proof fn test()
                ensures
                    forall|x : S1, y : S2, z : S3| s1_s2(x) == y || s2_s3(y) == z || s3_s1(z) == x
            {
                assume(false);
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "Function not in EPR, quantifier alternation graph contains cycle")
}

test_verify_one_file! {
    #[test] requires_positive_fail TYPES_TEST_2.to_string() + verus_code_str! {
        #[verifier::epr_check]
        mod EPRProofTest2 {
            use crate::TypesTest2::*;

            // should fail
            proof fn test()
                requires
                    forall|y : S2| (exists|x : S1| s1_s2(x) == y) || s2_s3(y) == S3Val
                ensures
                    s1_s2(S1Val) == S2Val
            {
                assume(false);
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "Function not in EPR, quantifier alternation graph contains cycle")
}

test_verify_one_file! {
    #[test] proof_args_not_foralled TYPES_TEST_2.to_string() + verus_code_str! {
        #[verifier::epr_check]
        mod EPRProofTest2 {
            use crate::TypesTest2::*;

            // should pass
            proof fn test(y : S2)
                ensures
                    forall|x : S1| s1_s2(x) == y
            {
                assume(false);
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] duplicate_type_forall TYPES_TEST_2.to_string() + verus_code_str! {
        #[verifier::epr_check]
        mod EPRProofTest2 {
            use crate::TypesTest2::*;

            // should fail (testing duplicate openings/closings)
            proof fn test()
                requires
                    forall|x : S1| s1_s2(x) == S2Val || (forall|y : S1| s1_s2(y) == s1_s2(x)) || exists|y : S2| s2_s1(y) == x
                ensures
                    s1_s2(S1Val) == S2Val
            {
                assume(false);
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "Function not in EPR, quantifier alternation graph contains cycle")
}

test_verify_one_file! {
    #[test] boolean_equality_both_polarity TYPES_TEST_2.to_string() + verus_code_str! {
        #[verifier::epr_check]
        mod EPRProofTest2 {
            use crate::TypesTest2::*;

            // should fail
            proof fn test()
                requires
                    forall|x : S2| (forall|y : S1| x == S2Val || s1_pred(y)) == ((s1_s2(S1Val) == x) || s2_pred(x))
                ensures
                    s1_s2(S1Val) == S2Val

            {
                assume(false);
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "Function not in EPR, quantifier alternation graph contains cycle")
}

test_verify_one_file! {
    #[test] boolean_iff_both_polarity TYPES_TEST_2.to_string() + verus_code_str! {
        #[verifier::epr_check]
        mod EPRProofTest2 {
            use crate::TypesTest2::*;

            // should fail
            proof fn test()
                requires
                    forall|x : S2| (forall|y : S1| x == S2Val || s1_pred(y)) <==> ((s1_s2(S1Val) == x) || s2_pred(x))
                ensures
                    s1_s2(S1Val) == S2Val

            {
                assume(false);
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "Function not in EPR, quantifier alternation graph contains cycle")
}

test_verify_one_file! {
    #[test] self_loop_fail TYPES_TEST_2.to_string() + verus_code_str! {
        #[verifier::epr_check]
        mod EPRProofTest2 {
            use crate::TypesTest2::*;

            spec(checked) fn self_loop(x : S1) -> S1 {
                x
            }

            // should fail (self loop S1 -> S1)
            proof fn test()
                ensures
                    forall| x : S1 | self_loop(x) == x
            {
                assume(false);
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "Function not in EPR, quantifier alternation graph contains cycle")
}

test_verify_one_file! {
    #[test] assume_positive_only_fail TYPES_TEST_2.to_string() + verus_code_str! {
        #[verifier::epr_check]
        mod EPRProofTest2 {
            use crate::TypesTest2::*;


            // should fail (forall exists in assume)
            proof fn test()
                ensures
                    s1_s2(S1Val) == S2Val
            {
                assume(forall|x : S2| s2_pred(x) && exists| y : S1| s1_s2(y) == x);
                assume(false);
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "Function not in EPR, quantifier alternation graph contains cycle")
}

test_verify_one_file! {
    #[test] assume_positive_only_pass TYPES_TEST_2.to_string() + verus_code_str! {
        #[verifier::epr_check]
        mod EPRProofTest2 {
            use crate::TypesTest2::*;


            // should pass (exists forall in assume)
            proof fn test()
                ensures
                    s1_s2(S1Val) == S2Val
            {
                assume(exists|x : S2| s2_pred(x) && forall| y : S1| s1_s2(y) == x);
                assume(false);
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] assert_positive_fail TYPES_TEST_2.to_string() + verus_code_str! {
        #[verifier::epr_check]
        mod EPRProofTest2 {
            use crate::TypesTest2::*;


            // should fail (forall exists in assert)
            proof fn test()
                ensures
                    s1_s2(S1Val) == S2Val
            {
                assume(false);
                assert(forall|x : S2| s2_pred(x) && exists| y : S1| s1_s2(y) == x);
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "Function not in EPR, quantifier alternation graph contains cycle")
}

test_verify_one_file! {
    #[test] assert_negative_fail TYPES_TEST_2.to_string() + verus_code_str! {
        #[verifier::epr_check]
        mod EPRProofTest2 {
            use crate::TypesTest2::*;


            // should fail (exists forall in assert (negative))
            proof fn test()
                ensures
                    s1_s2(S1Val) == S2Val
            {
                assume(false);
                assert(exists|x : S2| s2_pred(x) && forall| y : S1| s1_s2(y) == x);
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "Function not in EPR, quantifier alternation graph contains cycle")
}

test_verify_one_file! {
    #[test] func_arg_cycle TYPES_TEST_2.to_string() + verus_code_str! {
        #[verifier::epr_check]
        mod EPRProofTest2 {
            use crate::TypesTest2::*;


            proof fn test()
                ensures
                    // arguments to functions should also be checked
                    s2_pred(s1_s2(S1Val)),
                    s3_pred(s2_s3(S2Val)),
                    s1_pred(s3_s1(S3Val)),
            {
                assume(false);
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "Function not in EPR, quantifier alternation graph contains cycle")
}

test_verify_one_file! {
    #[test] generics_loop_1 TYPES_GENERICS.to_string() + verus_code_str! {
        #[verifier::epr_check]
        mod EPRMod {
            use super::EPRData::*;
            use super::MakeOne;

            spec fn loop_func<Kee: MakeOne, Value>(v : Value) -> Kee {
                Kee::make()
            }

            proof fn loop_prop<Key: MakeOne, Val: MakeOne>(f : Foo<Key, Val>)
                ensures
                    f.pred_map(),
                    // edge Val -> Key
                    loop_func::<Key, Val>(f.get_v()) == f.get_k(),

            {
                // edge Key -> Val (with correct bounds)
                f.foo_prop();
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "Function not in EPR, quantifier alternation graph contains cycle")

}

test_verify_one_file! {
    #[test] generics_loop_2 TYPES_GENERICS.to_string() + verus_code_str! {
        #[verifier::epr_check]
        mod EPRMod {
            use super::EPRData::*;
            use super::MakeOne;

            spec fn loop_func<Kee: MakeOne, Value>(v : Value) -> Kee {
                Kee::make()
            }

            proof fn loop_prop<Key: MakeOne, Val: MakeOne>(f : Foo<Key, Val>)
                ensures
                    // loops from binding function 2 ways
                    loop_func::<Key, Val>(f.get_v()) == f.get_k(),
                    loop_func::<Val, Key>(f.get_k()) == f.get_v(),

            {
                assume(false);
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "Function not in EPR, quantifier alternation graph contains cycle")

}
