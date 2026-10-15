// EXPECTED-ERROR: precondition not satisfied
use verus_builtin::*;
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
verified_tokenized_state_machine!(

#[verified_local_ready(do_deposit, do_withdraw)]
    Fancy {
        fields {
            #[sharding(variable)]
            pub m: int,

            #[sharding(imap)]
            pub map: IMap<int, bool>,

            #[sharding(storage_imap)]
            pub storage_map: IMap<int, bool>,
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
                init storage_map = IMap::empty();
                init map = IMap::empty();
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

verus! {

fn main() {
    proof {
        let tracked (Tracked(instance), Tracked(mut m), Tracked(map)) = Fancy::Instance::initialize(
            false,
        );
        let tracked token = instance.do_deposit(true, &mut m, true);
        let tracked guard = instance.do_guard(0, true, &token);
        let tracked mut empty = Fancy::map_collection::empty(instance.id());
        let tracked removed = empty.remove(0);
        assert(*guard);
    }
}

} // verus!
