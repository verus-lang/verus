//! Generic parameters used only by stored resources still have checked carriers.
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
verus! {

verified_tokenized_state_machine! {
    #[verified_raw_tokens]

    GenericStore<T> {
        fields {
            #[sharding(variable)] pub occupied:bool,
            #[sharding(storage_option)] pub slot:Option<T>,
        }
        #[invariant] pub fn occupancy(&self)->bool { self.occupied == (self.slot is Some) }
        init! { initialize() { init occupied=false; init slot=None; } }
        transition! { deposit(value:T) {
            require !pre.occupied;
            deposit slot += Some(value);
            update occupied=true;
        } }
        #[inductive(initialize)] fn initialize_inductive(post:Self) {}
        #[inductive(deposit)] fn deposit_inductive(pre:Self,post:Self,value:T) {}
    }
}

pub proof fn generic_storage_demo<T>(tracked value: T) {
    let tracked empty = IMap::tracked_empty();
    let tracked token = GenericStore::Protocol::<T>::initialize(empty);
    let ghost mathematical_value = value;
    let tracked mut resources = IMap::tracked_empty();
    resources.tracked_insert(0int, value);
    let tracked token = GenericStore::Protocol::<T>::deposit(token, resources, mathematical_value);
    assert(token.fragment().occupied->Some_0->Exclusive_0);
}

} // verus!
fn main() {}
