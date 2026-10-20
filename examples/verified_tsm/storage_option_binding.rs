//! Option storage supports checked Some(let permission) withdrawal bindings.
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::cell::{CellId, PCell, PointsTo};
use vstd::prelude::*;
use vstd::resource::algebra::ResourceAlgebra;
use vstd::resource::pcm::PCM;
use vstd::resource::tsm::Machine;
verus! {

verified_tokenized_state_machine! {
    #[verified_raw_tokens]

    StoredOption<T> {
        fields {
            #[sharding(constant)] pub cell:CellId,
            #[sharding(variable)] pub full:bool,
            #[sharding(variable)] pub expected:Option<PointsTo<T>>,
            #[sharding(storage_option)] pub stored:Option<PointsTo<T>>,
        }
        #[invariant] pub fn stored_matches(&self)->bool {
            self.full == (self.expected is Some)
            && self.stored==self.expected
            && (self.full ==> self.expected->Some_0.id()==self.cell)
        }
        init! { initialize(p:PointsTo<T>) {
            init cell=p.id();
            init full=true;
            init expected=Some(p);
            init stored=Some(p);
        } }
        transition! { take() {
            require pre.full;
            withdraw stored -= Some(let p);
            assert p.id()==pre.cell;
            update full=false;
            update expected=None;
        } }
        transition! { put(p:PointsTo<T>) {
            require !pre.full;
            require p.id()==pre.cell;
            deposit stored += Some(p);
            update full=true;
            update expected=Some(p);
        } }
        #[inductive(initialize)] fn initialize_inductive(post:Self,p:PointsTo<T>) {}
        #[inductive(take)] fn take_inductive(pre:Self,post:Self) {
            assert(post.stored==None);
        }
        #[inductive(put)] fn put_inductive(pre:Self,post:Self,p:PointsTo<T>) {}
    }
}

pub fn stored_option_binding_demo() -> (out: u64)
    ensures
        out == 9,
{
    let (cell, Tracked(permission)) = PCell::new(7u64);
    let ghost p = permission;
    // The storage is one `IMap<__StorageKey, __StorageValue>`: here the tagged
    // `Option` of the one `storage_option` field (`__pack_stored`).
    let tracked base = StoredOption::__pack_stored(Some(permission));
    let tracked token = StoredOption::Protocol::<u64>::initialize(base, p);
    let tracked (token, mut withdrawn) = StoredOption::Protocol::<u64>::take(token);
    let tracked mut permission = StoredOption::__unwrap_stored(withdrawn.tracked_remove(StoredOption::__StorageKey::stored));
    let before = cell.replace(Tracked(&mut permission), 9u64);
    assert(before == 7);
    let ghost p = permission;
    let tracked deposit = StoredOption::__pack_stored(Some(permission));
    assert(!token.fragment().full->Some_0->Exclusive_0);
    assert(token.fragment().expected->Some_0->Exclusive_0 == None);
    assert(token.fragment().cell->Some_0->Agree_0 == p.id());
    proof {
        token.fragment().op_unit();
        assert(StoredOption::Protocol::<u64>::put_requires(
            token.fragment(),
            StoredOption::Fragment::<u64>::unit(),
            deposit,
            p,
        )) by {
            assert forall|z: StoredOption::Fragment<u64>, pre: StoredOption::State<u64>|
                pre.invariant() && StoredOption::Fragment::<u64>::op(token.fragment(), z)
                    == StoredOption::Protocol::<u64>::embed(pre) implies StoredOption::State::<
                u64,
            >::put_enabled(pre, p) && deposit == StoredOption::State::<u64>::put_deposited(
                pre,
                p,
            ) by {};
        }
    }
    let tracked token = StoredOption::Protocol::<u64>::put(token, deposit, p);
    assert(token.fragment().full->Some_0->Exclusive_0);
    assert(token.fragment().expected->Some_0->Exclusive_0 == Some(p));
    let tracked (_token, mut withdrawn) = StoredOption::Protocol::<u64>::take(token);
    let tracked permission = StoredOption::__unwrap_stored(withdrawn.tracked_remove(StoredOption::__StorageKey::stored));
    cell.into_inner(Tracked(permission))
}

fn main() {
    let out = stored_option_binding_demo();
    assert(out == 9);
}

} // verus!
