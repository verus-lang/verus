//! Finite storage maps project to the actual physical permission map.
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::cell::{CellId, PCell, PointsTo};
use vstd::prelude::*;
use vstd::resource::algebra::ResourceAlgebra;
use vstd::resource::pcm::PCM;
use vstd::resource::tsm::Machine;
verus! {

broadcast use {
    vstd::map::group_map_lemmas,
    vstd::imap::group_imap_lemmas,
    vstd::iset::group_iset_lemmas,
};

verified_tokenized_state_machine! {
    #[verified_raw_tokens]

    StoredFiniteMap<T> {
        fields {
            #[sharding(constant)] pub cell:CellId,
            #[sharding(variable)] pub full:bool,
            #[sharding(variable)] pub expected:Option<PointsTo<T>>,
            #[sharding(storage_map)] pub stored:Map<nat,PointsTo<T>>,
        }
        #[invariant] pub fn stored_matches(&self)->bool {
            self.full == (self.expected is Some)
            && self.stored == match self.expected {
                Some(p)=>Map::empty().insert(0nat,p),
                None=>Map::empty(),
            }
            && (self.full ==> self.expected->Some_0.id()==self.cell)
        }
        init! { initialize(p:PointsTo<T>) {
            init cell=p.id();
            init full=true;
            init expected=Some(p);
            init stored=Map::empty().insert(0nat,p);
        } }
        transition! { take() {
            require pre.full;
            let key=0nat;
            withdraw stored -= [key=>let p];
            assert p.id()==pre.cell;
            update full=false;
            update expected=None;
        } }
        transition! { take_birds() {
            require pre.full;
            birds_eye let p=pre.stored[0nat];
            withdraw stored -= [0nat=>p];
            assert p.id()==pre.cell;
            update full=false;
            update expected=None;
        } }
        transition! { put(p:PointsTo<T>) {
            require !pre.full;
            require p.id()==pre.cell;
            let key=0nat;
            deposit stored += [key=>p];
            update full=true;
            update expected=Some(p);
        } }
        #[inductive(initialize)] fn initialize_inductive(post:Self,p:PointsTo<T>) {}
        #[inductive(take)] fn take_inductive(pre:Self,post:Self) {
            assert(post.stored =~= Map::empty());
        }
        #[inductive(take_birds)] fn take_birds_inductive(pre:Self,post:Self) {
            assert(post.stored =~= Map::empty());
        }
        #[inductive(put)] fn put_inductive(pre:Self,post:Self,p:PointsTo<T>) {}
    }
}

pub fn stored_finite_map_demo() -> (out: u64)
    ensures
        out == 9,
{
    let (cell, Tracked(permission)) = PCell::new(7u64);
    let ghost p = permission;
    let tracked mut base = IMap::tracked_empty();
    proof {
        base.tracked_insert(0nat, permission);
    }
    assert(Map::empty().insert(0nat, p).to_imap() =~= base);
    let tracked token = StoredFiniteMap::Protocol::<u64>::initialize(base, p);
    let tracked (token, mut withdrawn) = StoredFiniteMap::Protocol::<u64>::take(token);
    let tracked mut permission = withdrawn.tracked_remove(0nat);
    let before = cell.replace(Tracked(&mut permission), 9u64);
    assert(before == 7);
    let ghost p = permission;
    let tracked mut deposit = IMap::tracked_empty();
    proof {
        deposit.tracked_insert(0nat, permission);
    }
    assert(!token.fragment().full->Some_0->Exclusive_0);
    assert(token.fragment().expected->Some_0->Exclusive_0 == None);
    assert(token.fragment().cell->Some_0->Agree_0 == p.id());
    proof {
        token.fragment().op_unit();
        assert(StoredFiniteMap::Protocol::<u64>::put_requires(
            token.fragment(),
            StoredFiniteMap::Fragment::<u64>::unit(),
            deposit,
            p,
        )) by {
            assert forall|z: StoredFiniteMap::Fragment<u64>, pre: StoredFiniteMap::State<u64>|
                pre.invariant() && StoredFiniteMap::Fragment::<u64>::op(token.fragment(), z)
                    == StoredFiniteMap::Protocol::<u64>::embed(
                    pre,
                ) implies StoredFiniteMap::State::<u64>::put_enabled(pre, p) && deposit
                == StoredFiniteMap::State::<u64>::put_deposited(pre, p) by {};
        }
    }
    let tracked token = StoredFiniteMap::Protocol::<u64>::put(token, deposit, p);
    assert(token.fragment().full->Some_0->Exclusive_0);
    assert(token.fragment().expected->Some_0->Exclusive_0 == Some(p));
    let tracked (_token, mut withdrawn) = StoredFiniteMap::Protocol::<u64>::take_birds(token);
    let tracked permission = withdrawn.tracked_remove(0nat);
    cell.into_inner(Tracked(permission))
}

fn main() {
    let out = stored_finite_map_demo();
    assert(out == 9);
}

} // verus!
