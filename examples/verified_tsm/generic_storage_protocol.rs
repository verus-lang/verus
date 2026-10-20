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
    // The storage is one `IMap<__StorageKey, __StorageValue<T>>` (the value
    // enum is over `T`): here the tagged `Option<T>` of the one
    // `storage_option` field (`__pack_slot`).
    let tracked token = GenericStore::Protocol::<T>::initialize(IMap::tracked_empty());
    let ghost mathematical_value = value;
    let tracked resources = GenericStore::__pack_slot(Some(value));
    let tracked token = GenericStore::Protocol::<T>::deposit(token, resources, mathematical_value);
    assert(token.fragment().occupied->Some_0->Exclusive_0);
}

} // verus!
fn main() {}
