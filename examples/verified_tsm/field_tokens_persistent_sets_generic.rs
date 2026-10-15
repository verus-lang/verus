use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
verified_tokenized_state_machine! { Y<#[verifier::reject_recursive_types] T>{
 fields{#[sharding(persistent_iset)]pub b:ISet<T>,}
 init!{initialize(){init b=ISet::<T>::empty();}}
 transition!{tr_add(__tsm_native_set_owned:T){add b (union)= set{__tsm_native_set_owned};}}
 transition!{tr_have(__tsm_native_set_input:T){have b >= set{__tsm_native_set_input};}}
 transition!{tr_add_gen(values:ISet<T>){add b (union)=(values);}}
 transition!{tr_have_gen(values:ISet<T>){have b >=(values);}}
}}
verus! {

proof fn test_generic<T>(value: T) {
    let tracked (Tracked(inst), Tracked(token_f)) = Y::Instance::<T>::initialize();
    let tracked token1 = inst.tr_add(value);
    inst.tr_have(value, &token1);
    let tracked token1_clone = token1.clone();
    inst.tr_have(value, &token1_clone);
    let tracked token_set = inst.tr_add_gen(ISet::<T>::empty().insert(value));
    inst.tr_have_gen(ISet::<T>::empty().insert(value), &token_set);
}

fn main() {
    proof {
        test_generic(5int);
    }
}

} // verus!
