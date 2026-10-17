//! `#[verified_local_ready(..)]` on the default (generic) interface: the
//! attribute is accepted and its names are checked, but it changes nothing;
//! the operations keep the trusted macro's token-level preconditions.
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
verus! {

verified_tokenized_state_machine!(
    #[verified_local_ready(deposit, withdraw)]
    Cell {
        fields {
            #[sharding(variable)] pub full: bool,
            #[sharding(storage_option)] pub stored: Option<int>,
        }
        #[invariant]
        pub fn inv(&self) -> bool { self.full == self.stored is Some }
        init!{ initialize() { init full = false; init stored = None; } }
        transition!{ deposit(v: int) {
            require !pre.full;
            update full = true;
            deposit stored += Some(v);
        } }
        transition!{ withdraw() {
            require pre.full;
            update full = false;
            withdraw stored -= Some(let _);
        } }
        #[inductive(initialize)] fn initialize_inductive(post: Self) { }
        #[inductive(deposit)] fn deposit_inductive(pre: Self, post: Self, v: int) { }
        #[inductive(withdraw)] fn withdraw_inductive(pre: Self, post: Self) { }
    }
);

proof fn test() {
    let tracked (Tracked(inst), Tracked(mut full)) = Cell::Instance::initialize(None);
    inst.deposit(5, &mut full, 5);
    assert(full.value());
    let tracked v = inst.withdraw(&mut full);
    assert(!full.value());
}

fn main() {
    proof { test(); }
}

} // verus!
