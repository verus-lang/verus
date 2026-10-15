// EXPECTED-ERROR: mismatched types
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
verus! {

verified_tokenized_state_machine!{ X{
fields{
#[sharding(bool)] pub a:bool,
#[sharding(bool)] pub b:bool,
#[sharding(persistent_option)] pub p:Option<int>,
#[sharding(persistent_option)] pub q:Option<int>,
}
#[invariant] pub fn phase(self)->bool{
&&& self.a == (self.p is None)
&&& self.b == (self.p is None)
&&& (self.p is Some) == (self.q is Some)
}
init!{new(){init a=true;init b=true;init p=None;init q=None;}}
#[inductive(new)] fn new_inductive(post:Self){}
property!{exclusion_a(){have a >=true;have p >=Some(let _sm);assert(false);}}
property!{exclusion_b(){have b >=true;have p >=Some(let _sm);assert(false);}}
property!{same(left:int,right:int){have p >=Some(left);have p >=Some(right);assert(left==right);}}
transition!{initialize(inst:int,tix:int){remove a -=true;remove b -=true;add p (union)=Some(inst);add q (union)=Some(tix);}}
#[inductive(initialize)] fn initialize_inductive(pre:Self,post:Self,inst:int,tix:int){}
}}

fn main() {
    proof {
        let tracked (Tracked(instance), Tracked(a), Tracked(b), Tracked(p), Tracked(q)) =
            X::Instance::new();
        let tracked (Tracked(p), Tracked(q)) = instance.initialize(
            17,
            19,
            a.tracked_borrow(),
            b.tracked_unwrap(),
        );
        assert(p.value() == 17 && q.value() == 19);
        let tracked cloned = p.clone();
        p.agree(&cloned);
        p.agree(&p);
        instance.same(p.value(), cloned.value(), &p, &cloned);
        instance.same(p.value(), p.value(), &p, &p);
        assert(cloned.instance_id() == p.instance_id() && cloned.value() == 17);

    }
}

} // verus!
