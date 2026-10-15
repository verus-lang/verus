use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
verus! {

verified_tokenized_state_machine! {
Generic<T> {
 fields { #[sharding(variable)] pub value: Option<T>, }
 init! { initialize(v: Option<T>) { init value = v; } }
 transition! { clear(value:bool) { if value { update value = None; } else { update value = pre.value; } } }
}}

fn main() {
    proof {
        let tracked (Tracked(inst), Tracked(mut value)) = Generic::Instance::<u64>::initialize(
            Some(7),
        );
        inst.clear(false, &mut value);
        assert(value.value() == Some(7));
        inst.clear(true, &mut value);
        assert(value.value() == None);
    }
}

} // verus!
