//! Normal lets and branches preserve checked lexical assertion safety.
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
use vstd::resource::agree::AgreementRA;
use vstd::resource::algebra::ResourceAlgebra;
use vstd::resource::exclusive::ExclusiveRA;
use vstd::resource::pcm::PCM;
verus! {

verified_tokenized_state_machine! {
    #[verified_raw_tokens]

    Control {
        fields {
            #[sharding(variable)] pub value:nat,
            #[sharding(constant)] pub maximum:nat,
        }
        #[invariant] pub fn bounded(&self)->bool {self.value<=self.maximum}
        init! { initialize(maximum:nat, choose:bool) {
            init maximum=maximum;
            if choose { init value=0; } else { let zero=0nat; init value=zero; }
        } }
        transition! { increment(choose:bool) {
            let value=pre.value;
            assert value<=pre.maximum;
            require value<pre.maximum;
            if choose {
                let next=value+1;
                update value=next;
            } else {
                match choose { true=>{update value=value;},false=>{update value=value+1;} }
            }
        } }
        transition! { disabled(choose:bool) {
            if choose { require false; } else { require false; }
            assert false;
            update value=pre.value;
        } }
        transition! { matched_disabled(choose:bool) {
            match choose { true=>{require false;},false=>{require false;} }
            assert false;
        } }
        #[inductive(initialize)] fn initialize_inductive(post:Self,maximum:nat,choose:bool) {}
        #[inductive(increment)] fn increment_inductive(pre:Self,post:Self,choose:bool) {}
        #[inductive(disabled)] fn disabled_inductive(pre:Self,post:Self,choose:bool) {}
        #[inductive(matched_disabled)] fn matched_disabled_inductive(pre:Self,post:Self,choose:bool) {}
    }
}

pub proof fn scalar_control_demo() {
    let tracked token = Control::Protocol::initialize(2, true);
    let tracked token = Control::Protocol::increment(token, false);
    assert(token.fragment().value->Some_0->Exclusive_0 == 1);
}

pub proof fn borrowed_observation_demo() {
    let tracked token = Control::Protocol::initialize(2, false);
    let owned = Control::Fragment { value: Some(ExclusiveRA::Exclusive(0nat)), maximum: None };
    let observed = Control::Fragment { value: None, maximum: Some(AgreementRA::Agree(2nat)) };
    let tracked (owned, maximum) = token.split(owned, observed);
    let tracked owned = Control::Protocol::increment_with_shared(owned, &maximum, true);
    assert(owned.fragment().value->Some_0->Exclusive_0 == 1);
    assert(owned.fragment().maximum is None);
    assert(maximum.fragment() == observed);
}

} // verus!
fn main() {}
