// EXPECTED-ERROR: owned storage source references a reserved generated namespace; qualify the original path
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

 Generic<r#Token,V> {
 fields { #[sharding(storage_imap)] pub storage: IMap<r#Token,V>, }
 init! { initialize(initial: IMap<r#Token,V>) { init storage = initial; } }
 transition! { withdraw_at(k: r#Token, v: V) { withdraw storage -= [{let s=pre; let _all=s.storage; k} => v]; } }
 }
}
fn main() {}
