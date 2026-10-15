//! Every finite-map operand form from the strategy reference.
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
use vstd::resource::algebra::ResourceAlgebra;
use vstd::resource::pcm::PCM;

verus! {

verified_tokenized_state_machine! {
    #[verified_raw_tokens]

    MapOperands {
        fields {
            #[sharding(variable)] pub auth: Map<nat, int>,
            #[sharding(map)] pub entries: Map<nat, int>,
        }
        #[invariant] pub fn same(&self) -> bool { self.auth == self.entries }
        init! { initialize(m: Map<nat, int>) {
            init auth = m;
            init entries = m;
        } }
        transition! { add_one(k: nat, v: int) {
            require(!pre.auth.contains_key(k));
            update auth = pre.auth.insert(k, v);
            add entries += [k => v];
        } }
        transition! { remove_one(k: nat) {
            remove entries -= [k => let _];
            update auth = pre.auth.remove(k);
        } }
        readonly! { have_one(k: nat, v: int) { have entries >= [k => v]; } }
        transition! { add_many(m: Map<nat, int>) {
            require(pre.auth.dom().disjoint(m.dom()));
            update auth = pre.auth.union_prefer_right(m);
            add entries += (m);
        } }
        transition! { remove_many(m: Map<nat, int>) {
            remove entries -= (m);
            update auth = pre.auth.remove_keys(m.dom());
        } }
        readonly! { have_many(m: Map<nat, int>) { have entries >= (m); } }
        #[inductive(initialize)] fn initialize_inductive(post: Self, m: Map<nat, int>) {}
        #[inductive(add_one)] fn add_one_inductive(pre: Self, post: Self, k: nat, v: int) {}
        #[inductive(remove_one)] fn remove_one_inductive(pre: Self, post: Self, k: nat) {}
        #[inductive(add_many)] fn add_many_inductive(pre: Self, post: Self, m: Map<nat, int>) {}
        #[inductive(remove_many)] fn remove_many_inductive(pre: Self, post: Self, m: Map<nat, int>) {}
    }
}

fn main() {
    proof {
        let empty = Map::<nat, int>::empty();
        let pair = empty.insert(1nat, 10int).insert(2nat, 20int);
        let tracked token = MapOperands::Protocol::initialize(empty);
        let tracked token = MapOperands::Protocol::add_many(token, pair);
        let tracked token = MapOperands::Protocol::have_many(token, pair);
        let tracked token = MapOperands::Protocol::have_many(token, empty);
        let tracked token = MapOperands::Protocol::remove_many(token, empty);
        let tracked token = MapOperands::Protocol::remove_many(token, pair);
        let tracked token = MapOperands::Protocol::add_many(token, empty);
        let tracked token = MapOperands::Protocol::add_one(token, 3nat, 30int);
        let tracked token = MapOperands::Protocol::have_one(token, 3nat, 30int);
        let tracked token = MapOperands::Protocol::remove_one(token, 3nat);
        assert(token.fragment().auth->Some_0->Exclusive_0 == empty);
    }
}

} // verus!
