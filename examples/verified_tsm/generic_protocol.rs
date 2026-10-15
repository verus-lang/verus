//! Generic machine carriers retain checked algebra and protocol proofs.
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
verus! {

verified_tokenized_state_machine! {

    Generic<T> {
        fields {
            #[sharding(constant)] pub seed:T,
            #[sharding(variable)] pub current:T,
        }
        #[invariant] pub fn equals_seed(&self)->bool { self.current == self.seed }
        init! { initialize(value:T) { init seed=value; init current=value; } }
        transition! { reset(value:T) { require value == pre.seed; update current=value; } }
        #[inductive(initialize)] fn initialize_inductive(post:Self,value:T) {}
        #[inductive(reset)] fn reset_inductive(pre:Self,post:Self,value:T) {}
    }
}

pub proof fn generic_demo<T>(value: T) {
    let tracked (Tracked(instance), Tracked(mut current)) = Generic::Instance::<T>::initialize(
        value,
    );
    instance.reset(value, &mut current);
    assert(current.value() == value);
}

} // verus!
fn main() {}
