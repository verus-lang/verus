// EXPECTED-ERROR: error[E0277]
// The tagged storage layout keeps the storage protocol's Send/Sync rule: a
// token is Send/Sync only if every stored payload type is (here `Rc<u64>`, in
// the second of two differently typed storage fields, is not): the value enum
// `__StorageValue` holds every payload.
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
verified_tokenized_state_machine! {
    #[verified_raw_tokens]
Mixed {
    fields {
        #[sharding(variable)] pub phase: nat,
        #[sharding(storage_option)] pub first: Option<u64>,
        #[sharding(storage_map)] pub second: Map<nat, std::rc::Rc<u64>>,
    }
    init! {initialize() { init phase = 0; init first = None; init second = Map::empty(); }}
    #[invariant] pub fn shape(&self) -> bool { true }
    #[inductive(initialize)] fn initialize_inductive(post: Self) {}
}}
verus! {
fn require_traits<T: Send + Sync>() {
}
fn main() {
    require_traits::<Mixed::Token>();
}
} // verus!
