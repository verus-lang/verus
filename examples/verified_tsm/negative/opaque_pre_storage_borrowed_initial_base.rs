// EXPECTED-ERROR: mismatched types
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

proof fn borrowed_base(tracked m: &IMap<int, int>) {
    let tracked inst = ValidPhysical::Instance::initialize(*m, m);
}

} // verus!
fn main() {}
