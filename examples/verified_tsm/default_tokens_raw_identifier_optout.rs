//! Arbitrary optional operands, including the reference's empty no-op cases.
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
use vstd::resource::algebra::ResourceAlgebra;
use vstd::resource::pcm::PCM;

verus! {

verified_tokenized_state_machine! {
    #[r#verified_raw_tokens]

    OptionalOperands {
        fields {
            #[sharding(variable)] pub auth: Option<int>,
            #[sharding(option)] pub entry: Option<int>,
        }
        #[invariant] pub fn same(&self) -> bool { self.auth == self.entry }
        init! { initialize(value: Option<int>) {
            init auth = value;
            init entry = value;
        } }
        transition! { add_optional(value: Option<int>) {
            require(pre.auth is None || value is None);
            update auth = if value is Some { value } else { pre.auth };
            add entry += (value);
        } }
        transition! { remove_optional(value: Option<int>) {
            remove entry -= (value);
            update auth = if value is Some { None } else { pre.auth };
        } }
        readonly! { have_optional(value: Option<int>) { have entry >= (value); } }
        #[inductive(initialize)] fn initialize_inductive(post: Self, value: Option<int>) {}
        #[inductive(add_optional)] fn add_inductive(pre: Self, post: Self, value: Option<int>) {}
        #[inductive(remove_optional)] fn remove_inductive(pre: Self, post: Self, value: Option<int>) {}
    }
}

fn main() {
    proof {
        let tracked token = OptionalOperands::Protocol::initialize(None);
        let tracked token = OptionalOperands::Protocol::add_optional(token, None);
        let tracked token = OptionalOperands::Protocol::have_optional(token, None);
        let tracked token = OptionalOperands::Protocol::remove_optional(token, None);
        let tracked token = OptionalOperands::Protocol::add_optional(token, Some(7int));
        let tracked token = OptionalOperands::Protocol::have_optional(token, Some(7int));
        let tracked token = OptionalOperands::Protocol::have_optional(token, None);
        let tracked token = OptionalOperands::Protocol::add_optional(token, None);
        let tracked token = OptionalOperands::Protocol::remove_optional(token, None);
        assert(token.fragment().auth->Some_0->Exclusive_0 == Some(7int));
        let tracked token = OptionalOperands::Protocol::remove_optional(token, Some(7int));
        assert(token.fragment().entry is None);
    }
}

} // verus!
