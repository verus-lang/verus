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
        let a = G::take_step::initialize::<int>(5int);
        let b = G::take_step::set(a, 7int, 3int);
        assert(b.value == 7 && b.n == 3 && b.invariant());
        let c = G::take_step::observe(b);
        assert(c == b && c.invariant());
    }
}

} // verus!
