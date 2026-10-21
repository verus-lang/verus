// rust_verify/tests/example.rs ignore --- checked macro: Z3 warns "'=>' cannot be used in patterns" for a generated trigger (verifies otherwise)
//! Generic exact current-owner replacement with an independent actual observation.
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
verified_tokenized_state_machine! {
Y<#[verifier::reject_recursive_types] K,#[verifier::reject_recursive_types] V>{
 fields{#[sharding(imap)]pub map:IMap<K,V>,}
 init!{initialize(key:K,other:K,value:V){require key!=other;init map=IMap::empty().insert(key,value).insert(other,value);}}
 transition!{replace_observe(key:K,other:K,value:V,replacement:V){
  require (|__tsm_native_map_ordered_have_entry:bool| true)(false);
  remove map-=[key=>value];
  have map>=[other=>value];
  add map+=[key=>replacement];
 }}
}}
verus! {

proof fn test_inst<K, V>(key: K, other: K, value: V, replacement: V)
    requires
        key != other,
{
    let tracked (Tracked(inst), Tracked(mut map)) = Y::Instance::<K, V>::initialize(
        key,
        other,
        value,
    );
    let tracked token = map.remove(key);
    let tracked observer = map.remove(other);
    let tracked token = inst.replace_observe(key, other, value, replacement, token, &observer);
    assert(token.key() == key && token.value() == replacement);
    assert(observer.key() == other && observer.value() == value);
    map.insert(token);
    map.insert(observer);
    assert(map.map() == IMap::empty().insert(key, replacement).insert(other, value));
}

fn main() {
    proof {
        test_inst(5int, 19int, false, true);
    }
}

} // verus!
