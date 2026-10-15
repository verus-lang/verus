// EXPECTED-ERROR: cannot be sent between threads safely
use vstd::prelude::*;
use vstd::thread::*;
#[path="../field_tokens_generic.rs"] mod generic;
verus! {
fn main(){
    let tracked (Tracked(_instance),Tracked(item))=generic::Generic::Instance::<std::rc::Rc<u64>>::initialize(arbitrary());
    let _handle=spawn(move || -> (result:Tracked<generic::Generic::item<std::rc::Rc<u64>>>) {Tracked(item)});
}
}
