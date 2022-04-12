#![feature(rustc_private)]
#[macro_use]
mod common;
use common::*;

test_verify_one_file! {
    #[test] #[ignore] test_trigger_block_regression_121 code! {
        use seq::*;

        struct Node {
            base_v: nat,
            values: Seq<nat>,
            nodes: Seq<Box<Node>>,
        }

        impl Node {
            #[spec] fn inv(&self) -> bool {
                forall(|i: nat, j: nat| (i < self.nodes.len() && j < self.nodes.index(i).values.len()) >>= {
                    let values = #[trigger] self.nodes.index(i).values;
                    self.base_v <= #[trigger] values.index(j)
                })
            }
        }

    } => Err(err) => assert_one_fails(err)
}
