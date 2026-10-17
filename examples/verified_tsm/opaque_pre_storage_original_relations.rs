use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
verified_tokenized_state_machine! {

X {
           fields {
               #[sharding(storage_imap)] pub v: IMap<int, int>,
           }

           init!{
               initialize() {
                   init v = IMap::empty();
               }
           }

           transition!{
               tr() {
                   // this is ok:
                   withdraw v -= [{ let s = pre; s.v.index(0) } => 5]
                         by { assume(false); };
               }
           }
       }}

verus! {

proof fn original_empty_initialization_and_relations() {
    let tracked m: IMap<int, int> = IMap::tracked_empty();
    let tracked inst = X::Instance::initialize(m);
    assert(inst.value() == IMap::<int, int>::empty());
    let pre = X::State { v: IMap::<int, int>::empty() };
    let post = X::State { v: IMap::<int, int>::empty() };
    assert(X::State::initialize(pre));
    assert(X::State::tr(pre, post));
    assert(!X::State::tr_strong(pre, post));
    assert(!X::State::tr_enabled_strong(pre));
}

} // verus!
fn main() {}
