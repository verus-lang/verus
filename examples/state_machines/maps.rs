#[allow(unused_imports)]
use builtin::*;
use vstd::map::*;
use vstd::{pervasive::*, *};

use state_machines_macros::tokenized_state_machine;

tokenized_state_machine!(
    X {
        fields {
            #[sharding(map)]
            pub bool_map: Map<int, bool>,

        }

        init!{
            initialize(cond: bool) {
                init bool_map = Map::empty().insert(5, true);
            }
        }

        transition!{
            add(n: int) {
                remove bool_map -= [n => true];
                add bool_map += [n => true];
            }
        }

        transition!{
            add_have(n: int) {
                remove bool_map -= [n => false];
                have bool_map >= [19 => false];
                add bool_map += [n => true];
            }
        }

        #[inductive(initialize)]
        fn initialize_inductive(post: Self, cond: bool) { }

        #[inductive(add)]
        fn add_inductive(pre: Self, post: Self, n: int) { }

        #[inductive(add_have)]
        fn add_have_inductive(pre: Self, post: Self, n: int) { }
    }
);

tokenized_state_machine!(
    Fancy {
        fields {
            #[sharding(variable)]
            pub m: int,

            #[sharding(map)]
            pub map: Map<int, bool>,

            #[sharding(storage_map)]
            pub storage_map: Map<int, bool>,
        }

        #[invariant]
        pub fn inv1(self) -> bool {
            forall |i: int|
              self.storage_map.dom().contains(i) ==> (0 <= i && i < self.m)
        }

        #[invariant]
        pub fn inv2(self) -> bool {
            forall |i: int|
              (0 <= i && i < self.m) ==> self.storage_map.dom().contains(i)
        }

        #[invariant]
        pub fn inv3(self) -> bool {
            self.m >= 0 &&
            equal(self.storage_map, self.map)
        }

        init!{
            initialize(cond: bool) {
                init m = 0;
                init storage_map = Map::empty();
                init map = Map::empty();
            }
        }

        transition!{
            do_deposit(b: bool) {
                update m = pre.m + 1;
                add map += [pre.m => b];
                deposit storage_map += [pre.m => b];
            }
        }

        transition! {
            do_withdraw(b: bool) {
                require(pre.m >= 1);
                update m = pre.m - 1;
                remove map -= [pre.m => b];
                withdraw storage_map -= [pre.m => b];
            }
        }

        property! {
            do_guard(i: int, b: bool) {
                have map >= [i => b];
                guard storage_map >= [i => b];
            }
        }

        #[inductive(initialize)]
        fn initialize_inductive(post: Self, cond: bool) { }

        #[inductive(do_deposit)]
        fn do_deposit_inductive(pre: Self, post: Self, b: bool) {
            /*
            assert_forall_by(|i: int| {
              requires(post.storage_map.dom().contains(i));
              ensures(0 <= i && i < post.m);
              if pre.storage_map.dom().contains(i) {
                  assert(0 <= i && i < post.m);
              } else {
                  assert(i == pre.m);
                  assert(0 <= i && i < post.m);
              }
            });
            */
        }

        #[inductive(do_withdraw)]
        fn do_withdraw_inductive(pre: Self, post: Self, b: bool) { }
    }
);

fn main() {}
