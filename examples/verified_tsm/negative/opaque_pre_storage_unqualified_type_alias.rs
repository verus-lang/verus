// EXPECTED-ERROR: owned storage source references a reserved generated namespace; qualify the original path
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
type Token = int;
verified_tokenized_state_machine! {

X {
           fields {
               #[sharding(storage_imap)] pub v: IMap<int, Token>,
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

fn main() {}
