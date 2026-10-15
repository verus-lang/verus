//! Generic present observations and idempotent union duplicate actual knowledge.
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
verified_tokenized_state_machine! {
Y<#[verifier::reject_recursive_types] __tsm_native_pmap_observed,#[verifier::reject_recursive_types] V>{
 fields{#[sharding(persistent_imap)]pub c:IMap<__tsm_native_pmap_observed,V>,}
 init!{initialize(key:__tsm_native_pmap_observed,value:V){init c=IMap::<__tsm_native_pmap_observed,V>::empty().insert(key,value);}}
 transition!{tr1(__tsm_native_pmap_key:__tsm_native_pmap_observed,__tsm_native_pmap_actual_value:V){
  require (|__tsm_native_pmap_input:bool| true)(false);
  have c>=[__tsm_native_pmap_key=>__tsm_native_pmap_actual_value];
  add c (union)=[__tsm_native_pmap_key=>__tsm_native_pmap_actual_value];
 }}
 transition!{tr3(values:IMap<__tsm_native_pmap_observed,V>){have c>=(values);}}
}}
verus! {

proof fn test_inst<T, V>(key: T, value: V) {
    let tracked (Tracked(inst), Tracked(mut init_m)) = Y::Instance::<T, V>::initialize(key, value);
    assert(init_m.dom().contains(key));
    inst.tr3(IMap::<T, V>::empty().insert(key, value), &init_m);
    let tracked m_1 = init_m.remove(key);
    let tracked cloned = m_1.clone();
    let tracked m_3 = inst.tr1(key, value, &m_1);
    assert(m_3.key() == key && m_3.value() == value);
    let tracked m_5_12 = Y::c_collection::<T, V>::empty(inst.id());
    inst.tr3(IMap::<T, V>::empty(), &m_5_12);
    inst.tr3(IMap::<T, V>::empty(), &init_m);
}

fn main() {
    proof {
        test_inst(1int, 2int);
    }
}

} // verus!
