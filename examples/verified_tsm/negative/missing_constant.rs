// EXPECTED-ERROR: precondition not satisfied
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
verus! {

verified_tokenized_state_machine! {
    #[verified_raw_tokens]

    Bound {
        fields {
            #[sharding(variable)] pub value: int,
            #[sharding(constant)] pub maximum: int,
        }
        #[invariant] pub fn inv(&self)->bool { self.value <= self.maximum }
        init! { initialize() { init value = 0; init maximum = 10; } }
        transition! { set(n:int) { require n <= pre.maximum; update value = n; } }
        #[inductive(initialize)] fn initialize_inductive(post:Self) {}
        #[inductive(set)] fn set_inductive(pre:Self, post:Self, n:int) {}
    }
}

pub proof fn missing_constant() {
    use vstd::resource::agree::AgreementRA;
    use vstd::resource::exclusive::ExclusiveRA;
    let tracked all = Bound::Protocol::initialize();
    let v = Bound::Fragment { value: Some(ExclusiveRA::Exclusive(0int)), maximum: None };
    let c = Bound::Fragment { value: None, maximum: Some(AgreementRA::Agree(10int)) };
    let tracked (value, constant) = all.split(v, c);
    // The bound is a known number, but its resource is not in this owner.
    let tracked invalid = Bound::Protocol::set(value, 9);
}

} // verus!
fn main() {}
