// EXPECTED-ERROR: identifiers starting with 'update_tmp_' are reserved identifiers in state machine definitions
use verus_state_machines_macros::verified_state_machine_model;
use vstd::prelude::*;
verus! {

verified_state_machine_model!{ Capture {
    fields {pub n: int}
    transition!{ set(r#update_tmp_n: int) { update n = r#update_tmp_n; } }
}}

fn main() {
}

} // verus!
