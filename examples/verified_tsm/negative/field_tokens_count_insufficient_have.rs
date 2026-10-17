// EXPECTED-ERROR: precondition not satisfied
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
verus! {

verified_tokenized_state_machine! {  VariableGuard {
 fields {#[sharding(variable)] pub item:int,}
 #[invariant] pub fn positive(&self)->bool {self.item>=2}
 init!{initialize(n:int){require n>=2;init item=n;}}
 transition!{step(){require pre.item==3;assert(pre.item==3);update item=pre.item+1;}}
 #[inductive(initialize)] fn init_inductive(post:Self,n:int){}
 #[inductive(step)] fn step_inductive(pre:Self,post:Self){}
}}

verified_tokenized_state_machine! {  CountGuard {
 fields {#[sharding(count)] pub item:nat,}
 init!{initialize(n:nat){require n>=2;init item=n;}}
 property!{enough(){have item >= (3);}}
}}

fn main() {
    proof {
        let tracked (Tracked(i), Tracked(mut all)) = CountGuard::Instance::initialize(3);
        let tracked part = all.split(1);
        i.enough(&all);
    }
}

} // verus!
