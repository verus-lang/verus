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

 Generic<#[verifier::reject_recursive_types] K, #[verifier::reject_recursive_types] V> {
 fields { #[sharding(storage_imap)] pub storage: IMap<K,V>, }
 init! { initialize(initial: IMap<K,V>) { init storage = initial; } }
 transition! { withdraw_at(k: K, v: V) { withdraw storage -= [{let s=pre; let _all=s.storage; k} => v]; } }
 }
}
verus! {

proof fn generic_custody<K, V>(k: K, v: V, tracked m: IMap<K, V>)
    requires
        m == IMap::<K, V>::empty().insert(k, v),
{
    let tracked mut inst = Generic::Instance::initialize(m, m);
    let tracked borrowed = inst.borrow_at(k);
    assert(*borrowed == v);
    let tracked actual = inst.withdraw_at(k, v);
    assert(actual == v);
    assert(inst.value() == IMap::<K, V>::empty());
}

} // verus!
fn main() {}
