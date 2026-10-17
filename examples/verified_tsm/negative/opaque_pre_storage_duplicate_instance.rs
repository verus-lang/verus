// EXPECTED-ERROR: use of moved value: `inst`
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

proof fn duplicate_owner() {
    let tracked mut m: IMap<int, int> = IMap::tracked_empty();
    m.tracked_insert(0, 7);
    m.tracked_insert(7, 5);
    let initial = IMap::<int, int>::empty().insert(0, 7).insert(7, 5);
    let tracked mut inst = ValidPhysical::Instance::initialize(initial, m);
    let tracked (a, b) = (inst, inst);
}

} // verus!
fn main() {}
