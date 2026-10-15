use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
verus! {

verified_tokenized_state_machine!{  X {
    fields {
        #[sharding(variable)] pub x:int,
        #[sharding(variable)] pub y:int,
        #[sharding(bool)] pub ticket:bool,
    }
    init!{initialize(){init x=0;init y=1;init ticket=false;}}
    transition!{issue(){require pre.x+pre.y<=5;update x=3;update y=3;add ticket +=true;}}
    transition!{observe(){have ticket >=true;assert pre.x+pre.y>5;}}
    #[invariant]pub fn phase(&self)->bool{self.ticket==(self.x+self.y>5)}
    #[inductive(initialize)]fn initialize_inductive(post:Self){}
    #[inductive(issue)]fn issue_inductive(pre:Self,post:Self){}
    #[inductive(observe)]fn observe_inductive(pre:Self,post:Self){}
}}

fn main() {
    proof {
        let tracked (Tracked(inst), Tracked(mut x), Tracked(mut y), Tracked(ticket)) =
            X::Instance::initialize();
        assert(ticket is None);
        let tracked ticket = inst.issue(&mut x, &mut y);
        assert(x.value() == 3 && y.value() == 3);
        inst.observe(&x, &y, &ticket);
    }
}

} // verus!
