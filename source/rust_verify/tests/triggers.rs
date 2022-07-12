#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] test_trigger_block_regression_121_1 code! {
        use seq::*;

        struct Node {
            base_v: nat,
            values: Seq<nat>,
            nodes: Seq<Box<Node>>,
        }

        impl Node {
            #[spec] fn inv(&self) -> bool {
                forall(|i: nat, j: nat| (i < self.nodes.len() && j < self.nodes.index(i as int).values.len()) >>= {
                    let values = #[trigger] self.nodes.index(i as int).values;
                    self.base_v <= #[trigger] values.index(j as int)
                })
            }
        }

    } => Err(err) => assert_vir_error(err)
}

test_verify_one_file! {
    #[test] test_trigger_block_regression_121_2 code! {
        use seq::*;

        struct Node {
            base_v: nat,
            values: Seq<nat>,
            nodes: Seq<Box<Node>>,
        }

        impl Node {
            #[spec] fn inv(&self) -> bool {
                forall(|i: nat, j: nat| with_triggers!([self.nodes.index(i as int).values.index(j as int)] =>
                                                       (i < self.nodes.len() && j < self.nodes.index(i as int).values.len()) >>= {
                    let values = self.nodes.index(i as int).values;
                    self.base_v <= values.index(j as int)
                }))
            }
        }

    } => Ok(())
}

test_verify_one_file! {
    #[test] test_illegal_arith_trigger code! {
        fndecl!(fn some_fn(a: nat) -> nat);
        #[proof] fn quant() {
            ensures(forall(|a: nat, b: nat| #[trigger] some_fn(a + b) == 10));
            assume(false);
        }
    } => Err(err) => assert_vir_error(err)
}

test_verify_one_file! {
    #[test] test_mul_distrib_pass code! {
        #[proof] #[verifier(nonlinear)]
        fn mul_distributive_auto() {
            ensures(forall_arith(|a: nat, b: nat, c: nat| #[trigger] ((a + b) * c) == a * c + b * c));
        }

        #[proof]
        fn test1(a: nat, b: nat, c: nat) {
            requires([
                (a + b) * c == 20,
                a * c == 10,
            ]);
            ensures([
                b * c == 10,
            ]);
            mul_distributive_auto();
            assert((a + b) * c == a * c + b * c);
        }
    } => Ok(())
}

test_verify_one_file! {
    #[test] test_mul_distrib_forall_fail code! {
        #[proof] #[verifier(nonlinear)]
        fn mul_distributive_auto() {
            ensures(forall(|a: nat, b: nat, c: nat| #[trigger] ((a + b) * c) == a * c + b * c));
        }
    } => Err(e) => assert_vir_error(e)
}

test_verify_one_file! {
    #[test] test_arith_and_ord_fail code! {
        #[proof]
        fn quant() {
            ensures(forall_arith(|a: nat, b: nat, c: nat| #[trigger] a + b <= c));
            assume(false)
        }
    } => Err(e) => assert_vir_error(e)
}

test_verify_one_file! {
    #[test] test_recommends_regression_163 code! {
        fndecl!(fn some_fn(a: int) -> bool);

        #[proof]
        fn p() {
            ensures([
                forall_arith(|a: int, b: int| #[trigger] (a * b) == b * a),
                forall(|a: int| some_fn(a)), // FAILS
            ]);
        }
    } => Err(e) => assert_one_fails(e)
}
