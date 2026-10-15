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
verified_tokenized_state_machine! {

ValidPhysical {
           fields {
               #[sharding(storage_imap)] pub v: IMap<int, int>,
           }

           init!{
               initialize(initial: IMap<int,int>) {
                   init v = initial;
               }
           }

           transition!{
               tr() {
                   // this is ok:
                   withdraw v -= [{ let s = pre; s.v.index(0) } => 5]
                         ;
               }
           }
       }}

verus! {

proof fn wrong_base() {
    let tracked m: IMap<int, int> = IMap::tracked_empty();
    let initial = IMap::<int, int>::empty().insert(0, 7);
    let tracked inst = ValidPhysical::Instance::initialize(initial, m);
}

} // verus!
fn main() {}
