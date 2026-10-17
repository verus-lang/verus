// EXPECTED-ERROR: owned storage raw field identifiers are not supported
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
verified_tokenized_state_machine! {

X {
           fields {
               #[sharding(storage_imap)] pub r#v: IMap<int, int>,
           }

           init!{
               initialize() {
                   init r#v = IMap::empty();
               }
           }

           transition!{
               tr() {
                   // this is ok:
                   withdraw r#v -= [{ let s = pre; s.r#v.index(0) } => 5]
                         by { assume(false); };
               }
           }
       }}

fn main() {}
