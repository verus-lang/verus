//! Generic ordinary sets use current authority and actual supplied ownership.
#![allow(unused_imports)]
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::iset::*;
use vstd::prelude::*;

verified_tokenized_state_machine! {

SetNames<#[verifier::reject_recursive_types] K> {
    fields {
        #[sharding(iset)] pub b:ISet<K>,
        #[sharding(variable)] pub authority:ISet<K>,
        #[sharding(variable)] pub gate:bool,
        #[sharding(constant)] pub metadata:int,
    }
    init! { initialize(initial:ISet<K>) {
        init b=initial;
        init authority=initial;
        init gate=true;
        init metadata=42;
    } }
    transition! { tr_add(key:K) {
        require pre.gate;
        require !pre.authority.contains(key);
        add b+=set{key};
        update authority=pre.authority.insert(key);
    } }
    transition! { tr_have(key:K) { have b>=set{key}; } }
    transition! { tr_remove(key:K) {
        remove b-=set{key};
        update authority=pre.authority.remove(key);
    } }
    transition! { tr_add_gen(added:ISet<K>) {
        require pre.gate;
        require pre.authority.disjoint(added);
        add b+=(added);
        update authority=pre.authority.union(added);
    } }
    transition! { tr_have_gen(needed:ISet<K>) { have b>=(needed); } }
    transition! { tr_remove_gen(removed:ISet<K>) {
        remove b-=(removed);
        update authority=pre.authority.difference(removed);
    } }
    #[invariant] pub fn authority_matches(&self)->bool {self.b==self.authority}
    #[inductive(initialize)] fn initialize_inductive(post:Self,initial:ISet<K>) {}
    #[inductive(tr_add)] fn tr_add_inductive(pre:Self,post:Self,key:K) {}
    #[inductive(tr_have)] fn tr_have_inductive(pre:Self,post:Self,key:K) {}
    #[inductive(tr_remove)] fn tr_remove_inductive(pre:Self,post:Self,key:K) {}
    #[inductive(tr_add_gen)] fn tr_add_gen_inductive(pre:Self,post:Self,added:ISet<K>) {}
    #[inductive(tr_have_gen)] fn tr_have_gen_inductive(pre:Self,post:Self,needed:ISet<K>) {}
    #[inductive(tr_remove_gen)] fn tr_remove_gen_inductive(pre:Self,post:Self,removed:ISet<K>) {}
}}
verus! {

proof fn test_inst1<K>(initial: ISet<K>, key: K, added: ISet<K>)
    requires
        !initial.contains(key),
        initial.disjoint(added),
{
    let tracked (Tracked(inst), Tracked(token_f), Tracked(mut authority), Tracked(gate)) =
        SetNames::Instance::<K>::initialize(initial);
    let tracked token1 = inst.tr_add(key, &mut authority, &gate);
    assert(token1.element() == key);
    assert(inst.metadata() == 42);
    inst.tr_have(key, &token1);
    inst.tr_remove(key, &mut authority, token1);
    let tracked token_set = inst.tr_add_gen(added, &mut authority, &gate);
    inst.tr_have_gen(added, &token_set);
    inst.tr_remove_gen(added, &mut authority, token_set);
    assert(authority.value() == initial);
    let tracked empty = inst.tr_add_gen(ISet::<K>::empty(), &mut authority, &gate);
    inst.tr_have_gen(ISet::<K>::empty(), &empty);
    inst.tr_remove_gen(ISet::<K>::empty(), &mut authority, empty);
    assert(authority.value() == initial);
    let tracked no_resource = SetNames::b_collection::<K>::empty(inst.id());
    inst.tr_have_gen(ISet::<K>::empty(), &no_resource);
    inst.tr_remove_gen(ISet::<K>::empty(), &mut authority, no_resource);
    assert(authority.value() == initial);
}

} // verus!
verus! {

fn main() {
    proof {
        test_inst1(iset![19int], 5int, iset![6int]);
        let tracked (Tracked(inst), Tracked(token_f), Tracked(mut authority), Tracked(gate)) =
            SetNames::Instance::<int>::initialize(iset![5,6]);
        inst.tr_have_gen(iset![5], &token_f);
    }
}

} // verus!
