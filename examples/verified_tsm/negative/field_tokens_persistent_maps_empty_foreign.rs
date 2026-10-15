// EXPECTED-ERROR: error: precondition not satisfied
//! Generic present observations and idempotent union duplicate actual knowledge.
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
verified_tokenized_state_machine! {
Y<#[verifier::reject_recursive_types] K,#[verifier::reject_recursive_types] V>{
 fields{#[sharding(persistent_imap)]pub c:IMap<K,V>,}
 init!{initialize(key:K,value:V){init c=IMap::<K,V>::empty().insert(key,value);}}
 transition!{tr1(__tsm_native_pmap_key:K,__tsm_native_pmap_actual_value:V){
  have c>=[__tsm_native_pmap_key=>__tsm_native_pmap_actual_value];
  add c (union)=[__tsm_native_pmap_key=>__tsm_native_pmap_actual_value];
 }}
 transition!{tr3(values:IMap<K,V>){have c>=(values);}}
}}
verus! {

proof fn test_inst() {
    let tracked (Tracked(inst), Tracked(mut init_m)) = Y::Instance::<int, int>::initialize(1, 2);
    let tracked (Tracked(other), Tracked(other_m)) = Y::Instance::<int, int>::initialize(1, 2);
    let tracked m_5_12 = Y::c_collection::<int, int>::empty(other.id());
    inst.tr3(IMap::<int, int>::empty(), &m_5_12);
}

fn main() {
    proof {
        test_inst();
    }
}

} // verus!
