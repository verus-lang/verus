// EXPECTED-ERROR: postcondition not satisfied
use verus_state_machines_macros::verified_state_machine_model;
use vstd::prelude::*;
verus! {

verified_state_machine_model!{ Bad {
    fields {pub n: int}
    init!{ initialize() {init n = 0;} }
    #[invariant] pub fn positive(&self)->bool {self.n>=1}
    #[inductive(initialize)] fn initialize_inductive(post: Self) {}
}}

fn main() {
}

} // verus!
