// EXPECTED-ERROR: precondition not satisfied
//! A normal read needs the corresponding owned or borrowed observation.
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
use vstd::resource::algebra::ResourceAlgebra;
use vstd::resource::exclusive::ExclusiveRA;
use vstd::resource::pcm::PCM;
verus! {

verified_tokenized_state_machine! {
    #[verified_raw_tokens]

    Reads {
        fields {
            #[sharding(variable)] pub left:nat,
            #[sharding(variable)] pub right:nat,
        }
        init! { initialize() {init left=0;init right=7;} }
        transition! { copy() {let value=pre.right;update left=value;} }
    }
}

pub proof fn rejected() {
    let tracked whole = Reads::Protocol::initialize();
    let left = Reads::Fragment { left: Some(ExclusiveRA::Exclusive(0nat)), right: None };
    let right = Reads::Fragment { left: None, right: Some(ExclusiveRA::Exclusive(7nat)) };
    let tracked (left_token, right_token) = whole.split(left, right);
    let tracked _out = Reads::Protocol::copy(left_token);
}

} // verus!
fn main() {}
