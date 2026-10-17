// EXPECTED-ERROR: owned storage requires an explicit singleton withdrawal without a bound pattern
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
                   withdraw v -= [{ let s = pre; s.v.index(0) } => let value]
                         by { assume(false); };
               }
           }
       }}

fn main() {}
