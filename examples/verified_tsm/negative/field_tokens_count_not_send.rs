// EXPECTED-ERROR: cannot be sent between threads safely
#[path="../field_tokens_count_generic.rs"] mod protocol;
use protocol::GenericCount;
use vstd::prelude::*;
use vstd::thread::*;
verus! {
fn main(){
    let ghost value=arbitrary::<std::rc::Rc<u64>>();
    let tracked (Tracked(instance),Tracked(flag),Tracked(input),Tracked(output))=GenericCount::Instance::<std::rc::Rc<u64>>::initialize(value);
    let handle=spawn(move || -> (result:Tracked<GenericCount::input<std::rc::Rc<u64>>>) {Tracked(input)});
}
}
