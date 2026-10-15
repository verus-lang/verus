use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
verus! {

verified_tokenized_state_machine!{  X {
    fields {
        #[sharding(bool)] pub a:bool,
        #[sharding(option)] pub b:Option<int>,
    }
    init!{initialize(){init a=true;init b=None;}}
    transition!{transfer(){remove a -=true;add b +=Some(7);}}
    transition!{observe(){have b >=Some(7);}}
    #[invariant]pub fn exclusive_phase(&self)->bool{self.a == (self.b is None)}
    #[inductive(initialize)]fn initialize_inductive(post:Self){}
    #[inductive(transfer)]fn transfer_inductive(pre:Self,post:Self){}
    #[inductive(observe)]fn observe_inductive(pre:Self,post:Self){}
}}

fn main() {
    proof {
        let tracked (Tracked(inst), Tracked(a), Tracked(b)) = X::Instance::initialize();
        assert(b is None);
        let tracked a = a.tracked_unwrap();
        let tracked b = inst.transfer(a);
        assert(b.instance_id() == inst.id());
        assert(b.value() == 7);
        inst.observe(&b);
    }
}

} // verus!
