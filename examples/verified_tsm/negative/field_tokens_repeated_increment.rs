// EXPECTED-ERROR: precondition not satisfied
use vstd::prelude::*;
#[path="../counting_to_2.rs"] mod demo;
verus! {
proof fn misuse(){
    let tracked (Tracked(instance),Tracked(mut counter),Tracked(mut a),Tracked(_b))=demo::X::Instance::initialize();
    instance.tr_inc_a(&mut counter,&mut a);
    instance.tr_inc_a(&mut counter,&mut a);
}
fn main(){}
}
