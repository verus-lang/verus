type Token = vstd::prelude::int;
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

Qualified {
           fields {
               #[sharding(storage_imap)] pub v: IMap<int, super::Token>,
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

proof fn qualified_type_keeps_original_meaning() {
    let tracked m: IMap<int, Token> = IMap::tracked_empty();
    let tracked inst = Qualified::Instance::initialize(m);
    assert(inst.value() == IMap::<int, Token>::empty());
}

} // verus!
fn main() {}
