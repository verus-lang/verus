#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test_trigger_block_regression_121_1 verus_code! {
        use vstd::seq::*;

        struct Node {
            base_v: nat,
            values: Seq<nat>,
            nodes: Seq<Box<Node>>,
        }

        impl Node {
            spec fn inv(&self) -> bool {
                forall|i: nat, j: nat|
                    i < self.nodes.len() && j < self.nodes.index(spec_cast_integer::<nat, int>(i)).values.len() ==>
                    {
                        let values = #[verifier(trigger)] self.nodes.index(spec_cast_integer::<nat, int>(i)).values;
                        self.base_v <= #[verifier(trigger)] values.index(spec_cast_integer::<nat, int>(j))
                    }
            }
        }
    } => Err(err) => assert_vir_error_msg(err, "let variables in triggers not supported")
}

test_verify_one_file! {
    #[test] test_trigger_block_regression_121_2 verus_code! {
        use vstd::seq::*;

        struct Node {
            base_v: nat,
            values: Seq<nat>,
            nodes: Seq<Box<Node>>,
        }

        impl Node {
            spec fn inv(&self) -> bool {
                forall|i: nat, j: nat|
                    #![trigger self.nodes.index(spec_cast_integer::<nat, int>(i)).values.index(spec_cast_integer::<nat, int>(j))]
                        i < self.nodes.len() && j < self.nodes.index(spec_cast_integer::<nat, int>(i)).values.len() ==>
                        {
                            let values = self.nodes.index(spec_cast_integer::<nat, int>(i)).values;
                            self.base_v <= values.index(spec_cast_integer::<nat, int>(j))
                        }
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_illegal_arith_trigger verus_code! {
        spec fn some_fn(a: nat) -> nat;
        proof fn quant()
            ensures
                forall|a: nat, b: nat| #[trigger] some_fn(a + b) == 10,
        {
            assume(false);
        }
    } => Err(err) => assert_vir_error_msg(err, "triggers cannot contain integer arithmetic")
}

test_verify_one_file! {
    #[test] test_mul_distrib_pass verus_code! {
        #[verifier(nonlinear)]
        proof fn mul_distributive_auto()
            ensures
                forall_arith(|a: nat, b: nat, c: nat| #[trigger] ((a + b) * c) == a * c + b * c),
        {
        }

        proof fn test1(a: nat, b: nat, c: nat)
            requires
                (a + b) * c == 20,
                a * c == 10,
            ensures
                b * c == 10,
        {
            mul_distributive_auto();
            assert((a + b) * c == a * c + b * c);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_mul_distrib_forall_fail verus_code! {
        #[verifier(nonlinear)]
        proof fn mul_distributive_auto()
            ensures
                forall|a: nat, b: nat, c: nat| #[trigger] ((a + b) * c) == a * c + b * c
        {
        }
    } => Err(err) => assert_vir_error_msg(err, "trigger must be a function call, a field access, or a bitwise operator")
}

test_verify_one_file! {
    #[test] test_arith_and_ord_fail verus_code! {
        proof fn quant()
            ensures forall_arith(|a: nat, b: nat, c: nat| #[trigger] a + b <= c)
        {
            assume(false)
        }
    } => Err(err) => assert_vir_error_msg(err, "trigger in forall_arith must be an integer arithmetic operator")
}

test_verify_one_file! {
    #[test] test_recommends_regression_163 verus_code! {
        spec fn some_fn(a: int) -> bool;

        proof fn p()
            ensures
                forall_arith(|a: int, b: int| #[trigger] (a * b) == b * a),
                forall|a: int| some_fn(a), // FAILS
        {
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] test_spec_index_trigger_regression_262 verus_code! {
        use vstd::seq::*;

        spec fn foo(a: nat) -> bool;

        proof fn f(s: Seq<nat>)
            requires
                s.len() == 10,
                forall|r: nat| foo(r) && 0 < #[trigger] s[r as int],
                //             ^^^^^^ is automatically selected
        {
            assert(0 < s.index(3));
        }
    } => Ok(())
}

const TRIGGER_ON_LAMBDA_COMMON: &str = verus_code_str! {
    struct S { a: int, }

    spec fn prop_1(s: S) -> bool;
    spec fn prop_2(s: S) -> bool;
};

test_verify_one_file! {
    #[test] test_trigger_on_lambda_1 TRIGGER_ON_LAMBDA_COMMON.to_string() + verus_code_str! {
        #[verifier(external_body)]
        proof fn something(fn1: FnSpec(S)->bool, fn2: FnSpec(S)->bool)
        ensures forall|s: S| #[trigger] fn1(s) ==> fn2(s) { }

        proof fn foo(s: S) {
          let p1 = |s1| prop_1(s1);
          something(p1, |s1| prop_2(s1));
          assert forall|s: S| prop_1(s) implies prop_2(s) by {
            assert(p1(s));
            assert(prop_2(s));
          }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_trigger_on_lambda_2 TRIGGER_ON_LAMBDA_COMMON.to_string() + verus_code_str! {
        #[verifier(external_body)]
        proof fn something(fn1: FnSpec(S)->bool, fn2: FnSpec(S)->bool)
        ensures forall|s: S| #[trigger] fn1(s) ==> fn2(s) { }

        proof fn foo(s: S) {
          something(|s1| #[trigger] prop_1(s1), |s1| prop_2(s1));
          assert forall|s: S| prop_1(s) implies prop_2(s) by {
            assert(prop_1(s));
            assert(prop_2(s));
          }
        }
    } => Ok(())
}
