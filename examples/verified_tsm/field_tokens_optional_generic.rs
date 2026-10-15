use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
verus! {

verified_tokenized_state_machine!{X<T>{
fields{#[sharding(option)]pub c:Option<T>,}
init!{new(value:T){init c=Some(value);}}
transition!{observe(value:T){have c >=Some(value);}}
transition!{consume(value:T){remove c -=Some(value);}}
transition!{neutral(value:Option<T>){remove c -=(value);}}
}
}

fn main() {
    proof {
        let tracked (Tracked(inst), Tracked(c)) = X::Instance::<int>::new(7);
        let tracked c = c.tracked_unwrap();
        inst.observe(7, &c);
        inst.consume(7, c);
        inst.neutral(None, None);
    }
}

} // verus!
