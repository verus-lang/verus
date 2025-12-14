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
                        let values = #[trigger] self.nodes.index(spec_cast_integer::<nat, int>(i)).values;
                        self.base_v <= #[trigger] values.index(spec_cast_integer::<nat, int>(j))
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
        uninterp spec fn some_fn(a: nat) -> nat;
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
    #[test] test_arith_function_trigger verus_code! {
        uninterp spec fn f(i: int) -> bool;
        proof fn test(x: int) {
            assume(forall|i: int| #[trigger] f(i) ==> #[trigger] (i + 1) >= 7);
            assume(f(x));
            assert(x + 1 >= 7);
            assert(x + 2 >= 8);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_arith_function_trigger_fail verus_code! {
        uninterp spec fn f(i: int) -> bool;
        proof fn test(x: int) {
            assume(forall|i: int| #[trigger] f(i) ==> #[trigger] (i + 1) >= 7);
            assume(f(x));
            assert(x + 2 >= 8); // FAILS
        }
    } => Err(e) => assert_one_fails(e)
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
    } => Ok(())
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
    #[test] test_arith_auto1 verus_code! {
        uninterp spec fn f(i: int) -> bool;

        proof fn test(x: int) {
            assume(forall|i: int| f(i / 2) == f(i / 2));
        }
    } => Err(err) => assert_vir_error_msg(err, "Could not automatically infer triggers")
}

test_verify_one_file! {
    #[test] test_arith_auto2 verus_code! {
        uninterp spec fn f(i: int) -> bool;

        proof fn test(x: int) {
            assume(forall|i: int| #[trigger] f(i / 2) == f(i / 2));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_arith_auto3 verus_code! {
        proof fn test(x: int) {
            assume(forall|i: u32| i >> 1 == i >> 1);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_arith_auto4 verus_code! {
        proof fn test(x: int) {
            assume(forall|i: u32| ((i / 2) >> 1) == (i / 2) >> 1);
        }
    } => Err(err) => assert_vir_error_msg(err, "Could not automatically infer triggers")
}

test_verify_one_file! {
    #[test] test_arith_auto5 verus_code! {
        proof fn test(x: int) {
            assume(forall|i: u32| #[trigger] ((i / 2) >> 1) == (i / 2) >> 1);
        }
    } => Ok(())
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
        uninterp spec fn f(u: u8) -> bool;
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

        uninterp spec fn foo(a: nat) -> bool;

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

test_verify_one_file! {
    #[test] test_arith_variables_with_same_names verus_code! {
        // https://github.com/verus-lang/verus/issues/1447
        spec fn a(x: int) -> bool;

        proof fn p_() {
            let ranking_pred = |n: int| a(n);
            assert forall|n: int| #![trigger a(n)] a(n) by { } // FAILS
            assert forall|n: int| #![trigger a(-n)] a(-n) by { }
        }
    } => Err(e) => assert_one_fails(e)
}

const TRIGGER_ON_LAMBDA_COMMON: &str = verus_code_str! {
    struct S { a: int, }

    uninterp spec fn prop_1(s: S) -> bool;
    uninterp spec fn prop_2(s: S) -> bool;
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
        uninterp spec fn bar(i: nat) -> bool;
        uninterp spec fn baz(i: nat) -> bool;
        uninterp spec fn qux(j: nat) -> bool;
        uninterp spec fn mux(j: nat) -> bool;
        uninterp spec fn res(i : nat, j : nat) -> bool;

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

test_verify_one_file! {
    #[test] test_nested verus_code! {
        uninterp spec fn f(x: int) -> bool;
        uninterp spec fn g(x: int) -> bool;

        proof fn test() {
            // trigger for outer quantifier should be f(x)
            // trigger for inner quantifier should be g(y) (and NOT include f(x))
            assume(forall |x: int|
              forall |y: int|
                #[trigger] f(x) && #[trigger] g(y));

            let t = f(3);
            let u = g(4);
            assert(f(3) && g(4));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_self_in_trigger_in_clone_issue1347 verus_code! {
        use vstd::*;
        use vstd::prelude::*;

        struct Node {
            child: Option<Box<Node>>,
        }

        impl Node {
            pub spec fn map(self) -> Map<int, int>;
        }

        impl Clone for Node {
            fn clone(&self) -> (res: Self)
                ensures forall |key: int| #[trigger] self.map().dom().contains(key) ==> key == 3
            {
                return Node { child: None }; // FAILS
            }
        }

        fn test(n: Node) {
            let t = n.clone();
            assert(forall |key: int| n.map().dom().contains(key) ==> key == 3);
        }

        fn test2(n: Node) {
            let c = Node::clone;
            let t = c(&n);
            assert(forall |key: int| n.map().dom().contains(key) ==> key == 3);
        }
    } => Err(err) => assert_one_fails(err)
}

test_verify_one_file! {
    #[test] test_lets_and_nested_quantifiers_issue1347 verus_code! {
        uninterp spec fn llama(x: int) -> int;
        uninterp spec fn foo(x: int, y: int) -> bool;
        uninterp spec fn bar(x: int) -> bool;

        proof fn test() {
            let b =
              forall |x: int| #[trigger] bar(x) ==> ({
                let y = llama(x);
                forall |z: int| #[trigger] foo(y, z)
              });

            assume(b);
            assume(bar(7));
            assert(foo(llama(7), 20));
            assert(foo(llama(7), 21));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_broadcast_all_triggers verus_code! {
        uninterp spec fn a(a: nat) -> bool;
        uninterp spec fn b(a: nat) -> bool;
        uninterp spec fn c(a: nat) -> bool;
        uninterp spec fn d(a: nat) -> bool;

        broadcast proof fn axiom_a(x: nat)
            requires
                a(x)
            ensures
                #![all_triggers] b(x) && c(x)
            // a(x) ==> b(x) && c(x)
        {
            admit();
        }

        proof fn test(x: nat)
            requires a(x)
        {
            broadcast use axiom_a;
            assume(forall|x: nat| b(x) ==> d(x));
            assert(d(x));
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_broadcast_all_trigger_ext_eq verus_code! {
        use vstd::set::*;
        pub uninterp spec fn my_contains<A>(s: Set<A>, a: A) -> bool;

        pub broadcast proof fn test_ext<A>(s1: Set<A>, s2: Set<A>)
            ensures
                #![all_triggers] (s1 =~= s2) <==> (forall|a: A| my_contains(s1, a) == my_contains(s2, a)),
        {
            admit();
        }

        proof fn test(a: Set<nat>, b: Set<nat>)
            requires forall|x: nat| my_contains(a, x) == my_contains(b, x),
        {
            broadcast use test_ext;
            assert(a == b); // in positive position: we infer a =~= b
        }
    } => Ok(())
}
