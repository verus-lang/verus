// EXPECTED-ERROR: precondition not satisfied
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

proof fn foo(tracked m: IMap<int, int>) {
    requires(equal(m, IMap::empty()));
    let tracked mut inst = X::Instance::initialize(m);
    let tracked t = (inst).tr();
    assert(t == 5);
}

} // verus!
fn main() {}
