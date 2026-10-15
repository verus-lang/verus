//! Both singleton and arbitrary bool operands from the strategy reference.
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
use vstd::resource::algebra::ResourceAlgebra;
use vstd::resource::pcm::PCM;

verus! {

verified_tokenized_state_machine! {
    #[verified_raw_tokens]

    BoolOperands {
        fields {
            #[sharding(variable)] pub auth: bool,
            #[sharding(bool)] pub present: bool,
        }
        #[invariant] pub fn same(&self) -> bool { self.auth == self.present }
        init! { initialize(value: bool) {
            init auth = value;
            init present = value;
        } }
        transition! { add_optional(value: bool) {
            require(!pre.auth || !value);
            update auth = pre.auth || value;
            add present += (value);
        } }
        transition! { remove_optional(value: bool) {
            remove present -= (value);
            update auth = pre.auth && !value;
        } }
        readonly! { have_optional(value: bool) { have present >= (value); } }
        transition! { add_singleton() {
            require(!pre.auth);
            update auth = true;
            add present += true;
        } }
        transition! { remove_singleton() {
            remove present -= true;
            update auth = false;
        } }
        readonly! { have_singleton() { have present >= true; } }
        #[inductive(initialize)] fn initialize_inductive(post: Self, value: bool) {}
        #[inductive(add_optional)] fn add_inductive(pre: Self, post: Self, value: bool) {}
        #[inductive(remove_optional)] fn remove_inductive(pre: Self, post: Self, value: bool) {}
        #[inductive(add_singleton)] fn add_singleton_inductive(pre: Self, post: Self) {}
        #[inductive(remove_singleton)] fn remove_singleton_inductive(pre: Self, post: Self) {}
    }
}

fn main() {
    proof {
        let tracked token = BoolOperands::Protocol::initialize(false);
        let tracked token = BoolOperands::Protocol::add_optional(token, false);
        let tracked token = BoolOperands::Protocol::have_optional(token, false);
        let tracked token = BoolOperands::Protocol::remove_optional(token, false);
        let tracked token = BoolOperands::Protocol::add_optional(token, true);
        let tracked token = BoolOperands::Protocol::have_optional(token, true);
        let tracked token = BoolOperands::Protocol::have_optional(token, false);
        let tracked token = BoolOperands::Protocol::add_optional(token, false);
        let tracked token = BoolOperands::Protocol::remove_optional(token, false);
        assert(token.fragment().present.count == 1);
        let tracked token = BoolOperands::Protocol::remove_optional(token, true);
        let tracked token = BoolOperands::Protocol::add_singleton(token);
        let tracked token = BoolOperands::Protocol::have_singleton(token);
        let tracked token = BoolOperands::Protocol::remove_singleton(token);
        assert(token.fragment().present.count == 0);
    }
}

} // verus!
