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
    #[test] test_ok_arith_trigger verus_code! {
        spec fn some_fn(a: nat) -> nat;
        proof fn quant()
            ensures
                forall|a: nat, b: nat| #[trigger] some_fn(a + b) == 10,
        {
            assume(false);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_mul_distrib_pass verus_code! {
        #[verifier(nonlinear)]
        proof fn mul_distributive_auto()
            ensures
                forall|a: nat, b: nat, c: nat| #[trigger] ((a + b) * c) == a * c + b * c,
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
    #[test] test_mul_distrib_forall_ok verus_code! {
        #[verifier(nonlinear)]
        proof fn mul_distributive_auto()
            ensures
                forall|a: nat, b: nat, c: nat| #[trigger] ((a + b) * c) == a * c + b * c
        {
            assert forall|a: nat, b: nat, c: nat| #[trigger] ((a + b) * c) == a * c + b * c by {
            }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_mul_distrib_forall_ok2 verus_code! {
        spec fn t(n: nat) -> bool { true }
        #[verifier(nonlinear)]
        proof fn mul_distributive_auto()
            ensures
                forall|a: nat, b: nat, c: nat| t(c) ==> #[trigger] ((a + b) * c) == a * c + b * c
        {
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_mul_distrib_forall_fail1 verus_code! {
        spec fn f(n: nat) -> nat { 0 }
        #[verifier(nonlinear)]
        proof fn mul_distributive_auto()
            ensures
                forall|a: nat, b: nat, c: nat| #[trigger] ((a + b + f(c)) * c) == a * c + b * c
        {
        }
    } => Err(err) => assert_vir_error_msg(err, "variable `c` in trigger cannot appear in both arithmetic and non-arithmetic positions")
}

test_verify_one_file! {
    #[test] test_mul_distrib_forall_fail2 verus_code! {
        spec fn t(n: nat) -> bool { true }
        #[verifier(nonlinear)]
        proof fn mul_distributive_auto()
            ensures
                forall|a: nat, b: nat, c: nat| #[trigger] t(c) ==> #[trigger] ((a + b) * c) == a * c + b * c
        {
        }
    } => Err(err) => assert_vir_error_msg(err, "variable `c` in trigger cannot appear in both arithmetic and non-arithmetic positions")
}

test_verify_one_file! {
    #[test] test_arith_with_inline verus_code! {
        #[verifier(inline)]
        spec fn some_arith(a: nat, b: nat) -> nat {
            a + b
        }

        proof fn quant()
            ensures forall|a: nat, b: nat| (#[trigger] some_arith(a, b)) == 0
        {
            assume(false)
        }
    } => Err(err) => assert_vir_error_msg(err, "variable `a` in trigger cannot appear in both arithmetic and non-arithmetic positions")
}

test_verify_one_file! {
    #[test] test_arith_and_ord verus_code! {
        proof fn quant()
            ensures forall|a: nat, b: nat, c: nat| #[trigger] (a + b <= c)
        {
            assume(false)
        }
    } => Err(err) => assert_vir_error_msg(err, "trigger must be a function call, a field access, or arithmetic operator")
}

test_verify_one_file! {
    #[test] test_arith_assert_by verus_code! {
        proof fn assoc()
            ensures
                forall|x: int, y: int, z: int| #[trigger] ((x * y) * z) == x * (y * z),
        {
            assert forall|x: int, y: int, z: int| #[trigger] ((x * y) * z) == x * (y * z) by {
                assert((x * y) * z == x * (y * z)) by(nonlinear_arith);
            }
        }

        proof fn test(w: int, x: int, y: int, z: int)
        {
            assert(((w * x) * y) * z == w * (x * (y * z))) by {
                assoc();
            }
        }

        proof fn test_fail(w: int, x: int, y: int, z: int)
        {
            assert(((w * x) * y) * z == w * (x * (y * z))) by { // FAILS
            }
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] test_arith_assert_by_nat verus_code! {
        proof fn assoc()
            ensures
                forall|x: nat, y: nat, z: nat| #[trigger] ((x * y) * z) == x * (y * z),
        {
            assert forall|x: nat, y: nat, z: nat| #[trigger] ((x * y) * z) == x * (y * z) by {
                assert((x * y) * z == x * (y * z)) by(nonlinear_arith);
            }
        }

        proof fn test(w: nat, x: nat, y: nat, z: nat)
        {
            assert(((w * x) * y) * z == w * (x * (y * z))) by {
                assoc();
            }
        }

        proof fn test_fail(w: nat, x: nat, y: nat, z: nat)
        {
            assert(((w * x) * y) * z == w * (x * (y * z))) by { // FAILS
            }
        }
    } => Err(e) => assert_one_fails(e)
}

test_verify_one_file! {
    #[test] test_bitwise_trigger verus_code! {
        spec fn f(u: u8) -> bool;
        proof fn test() {
            assert(forall|i: u8| #[trigger]f(i) || #[trigger](i >> 2) == i >> 2);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_recommends_regression_163 verus_code! {
        spec fn some_fn(a: int) -> bool;

        proof fn p()
            ensures
                forall|a: int, b: int| #[trigger] (a * b) == b * a,
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
        proof fn something(fn1: spec_fn(S)->bool, fn2: spec_fn(S)->bool)
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
        proof fn something(fn1: spec_fn(S)->bool, fn2: spec_fn(S)->bool)
        ensures forall|s: S| #[trigger] fn1(s) ==> fn2(s) { }

        proof fn foo(s: S) {
          something(|s1| #[trigger] prop_1(s1), |s1| prop_2(s1));
          assert forall|s: S| prop_1(s) implies prop_2(s) by {
            assert(prop_1(s));
            assert(prop_2(s));
          }
        }
    } => Ok(_err) => { /* ignore deprecation warning */ }
}

test_verify_one_file! {
    #[test] test_trigger_on_lambda_3 verus_code! {
        spec fn id<A>(a: A) -> A { a }

        struct S<A>(A);
        impl<A> S<A> {
            spec fn f() -> (spec_fn(A) -> bool) {
                // From https://github.com/verus-lang/verus/issues/1033
                // Note that Z3 generates WARNING ... pattern does not contain all quantified variables.
                // This is why we're deprecating triggers in spec_fn closures.
                |a: A| #[trigger] id(a) == a
            }
        }

        proof fn test() {
            assert(S::f()(true));
        }
    } => Err(_) => { /* ignore deprecation warning, Z3 warning, etc. */ }
}

test_verify_one_file! {
    #[test] test_no_trigger_on_lambda TRIGGER_ON_LAMBDA_COMMON.to_string() + verus_code_str! {
        #[verifier(external_body)]
        proof fn something(fn1: spec_fn(S)->bool, fn2: spec_fn(S)->bool)
        ensures forall|s: S| #[trigger] fn1(s) ==> fn2(s) { }

        proof fn foo(s: S) {
          something(|s1| prop_1(s1), |s1| prop_2(s1));
          assert forall|s: S| prop_1(s) implies prop_2(s) by {
            assert((|s1| prop_1(s1))(s));
          }
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_trigger_all verus_code! {
        spec fn bar(i: nat) -> bool;
        spec fn baz(i: nat) -> bool;
        spec fn qux(j: nat) -> bool;
        spec fn mux(j: nat) -> bool;
        spec fn res(i : nat, j : nat) -> bool;

        proof fn foo()
            requires
                forall|i : nat, j : nat| #![all_triggers]
                    (bar(i) && qux(j)) ==> res(i, j) && (baz(j) && mux(i)),
                bar(3),
                qux(4),
            ensures
                baz(4)
        {}
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_with_trigger verus_code! {
        trait T {
            spec fn s(&self) -> bool;
        }
        impl T for u8 {
            spec fn s(&self) -> bool { true }
        }
        spec fn f(i: int) -> u8 { 0 }
        spec fn g() -> bool {
            forall|i: int| #![trigger f(i)] f(i).s()
        }
        proof fn p() {
            assert(g() == g());
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_broadcast_arith_trigger verus_code! {
        pub broadcast proof fn testb(x: int, y: int)
            ensures
                #[trigger] (2 * x + 2 * y) == (x + y) * 2
        {
        }
    } => Ok(())
}
