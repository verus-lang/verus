// EXPECTED-ERROR: precondition not satisfied
use verus_state_machines_macros::verified_state_machine_model;
use vstd::prelude::*;
verus! {

verified_state_machine_model!{ G<__tsm_checked_take_step_initialize> {
    fields {pub value: __tsm_checked_take_step_initialize, pub n: int}
    init!{ initialize(value: __tsm_checked_take_step_initialize) {init value = value; init n = 0;} }
    transition!{ set(value: __tsm_checked_take_step_initialize, r#__tsm_checked_take_step_set: int) {
        require r#__tsm_checked_take_step_set >= 0;
        let n: int = r#__tsm_checked_take_step_set;
        update value = value; update n = n;
    } }
    readonly!{ observe() {assert pre.n >= 0;} }
    #[invariant] pub fn nonnegative(&self)->bool {self.n>=0}
    #[inductive(initialize)] fn initialize_inductive(post: Self, value: __tsm_checked_take_step_initialize) {}
    #[inductive(set)] fn set_inductive(pre: Self, post: Self, value: __tsm_checked_take_step_initialize, r#__tsm_checked_take_step_set: int) {}
}}

fn main() {
    proof {
        let pre = G::State { value: 5int, n: -1int };
        let post = G::take_step::set(pre, 7int, 3int);
    }
}

} // verus!
