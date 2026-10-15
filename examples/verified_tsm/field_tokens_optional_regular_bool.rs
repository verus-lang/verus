use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
verus! {

verified_tokenized_state_machine!{X{
fields{#[sharding(bool)]pub c:bool,}
init!{new(){init c=true;}}
transition!{observe(){have c >=true;}}
transition!{consume(){remove c -=true;}}
transition!{neutral(value:bool){remove c -=(value);}}
}
}

fn main() {
    proof {
        let tracked (Tracked(inst), Tracked(c)) = X::Instance::new();
        let tracked c = c.tracked_unwrap();
        inst.observe(&c);
        inst.consume(c);
        inst.neutral(false, None);
    }
}

} // verus!
