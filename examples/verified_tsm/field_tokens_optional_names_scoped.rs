use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
verus! {

verified_tokenized_state_machine!{X{
fields{#[sharding(option)]pub c:Option<int>,}
init!{new(){init c=Some(7);}}
transition!{observe(source:int){have c >=Some(source);}}
transition!{consume(__tsm_optional_typed:int){remove c -=Some(__tsm_optional_typed);}}
transition!{neutral(value:Option<int>){remove c -=(value);}}
}
}

fn main() {
    proof {
        let tracked (Tracked(inst), Tracked(c)) = X::Instance::new();
        let tracked c = c.tracked_unwrap();
        inst.observe(7, &c);
        inst.consume(7, c);
        inst.neutral(None, None);
    }
}

} // verus!
