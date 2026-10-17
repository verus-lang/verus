// EXPECTED-ERROR: mismatched types
use vstd::prelude::*;
#[path="../counting_to_2.rs"] mod demo;
verus! {
proof fn misuse(){
    let tracked (Tracked(instance),Tracked(mut counter),Tracked(_a),Tracked(mut b))=demo::X::Instance::initialize();
    instance.tr_inc_a(&mut counter,&mut b);
}
fn main(){}
}
