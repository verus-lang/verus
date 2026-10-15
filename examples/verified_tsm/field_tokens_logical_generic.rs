use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
verus! {

pub trait Ticketing<R> {
    type Id;
}

verified_tokenized_state_machine!{ X<R,T:Ticketing<R>>{
fields{
#[sharding(bool)]pub a:bool,
#[sharding(bool)]pub b:bool,
#[sharding(persistent_option)]pub p:Option<R>,
#[sharding(persistent_option)]pub q:Option<T>,
}
#[invariant] pub fn phase(self)->bool{
&&& self.a == (self.p is None)
&&& self.b == (self.p is None)
&&& (self.p is Some) == (self.q is Some)
}
init!{new(){init a=true;init b=true;init p=None;init q=None;}}
#[inductive(new)] fn new_inductive(post:Self){}
transition!{initialize(inst:R,tix:T){remove a -=true;remove b -=true;add p (union)=Some(inst);add q (union)=Some(tix);}}
#[inductive(initialize)] fn initialize_inductive(pre:Self,post:Self,inst:R,tix:T){}
property!{exclusion_a(){have a >=true;have p >=Some(let _sm);assert(false);}}
property!{exclusion_b(){have b >=true;have p >=Some(let _sm);assert(false);}}
}}

pub proof fn demonstration<R, T: Ticketing<R>>(inst: R, tix: T) {
    let tracked (Tracked(instance), Tracked(a), Tracked(b), Tracked(p), Tracked(q)) = X::Instance::<
        R,
        T,
    >::new();
    let tracked (Tracked(p), Tracked(q)) = instance.initialize(
        inst,
        tix,
        a.tracked_unwrap(),
        b.tracked_unwrap(),
    );
    assert(p.value() == inst && q.value() == tix);
    let tracked cp = p.clone();
    p.agree(&cp);
    p.agree(&p);
    let tracked cq = q.clone();
    q.agree(&cq);
}

fn main() {
}

} // verus!
