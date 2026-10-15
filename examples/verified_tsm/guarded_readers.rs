//! A reader fragment borrows a stored PCell permission through a checked guard.
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::cell::{PCell, PointsTo};
use vstd::multiset::*;
use vstd::prelude::*;
use vstd::resource::algebra::ResourceAlgebra;
use vstd::resource::pcm::PCM;
use vstd::resource::tsm::Machine;
verus! {

broadcast use {vstd::multiset::group_multiset_axioms, vstd::multiset::group_multiset_properties};

verified_tokenized_state_machine! {
    #[verified_raw_tokens]

    GuardedReaders<T> {
        fields {
            #[sharding(bool)] pub writer:bool,
            #[sharding(constant)] pub slot:int,
            #[sharding(multiset)] pub readers:Multiset<PointsTo<T>>,
            #[sharding(storage_imap)] pub stored:IMap<int,PointsTo<T>>,
        }
        #[invariant] pub fn readers_agree(&self)->bool {
            forall|p:PointsTo<T>| self.readers.count(p)>0
                ==> self.stored.contains_key(self.slot)&&self.stored[self.slot]==p
        }
        init! { initialize(p:PointsTo<T>) {
            init writer=false;
            init slot=0int;
            init readers=Multiset::singleton(p);
            init stored=IMap::empty().insert(0int,p);
        } }
        property! { reader_guard(p:PointsTo<T>) {
            have readers >= {p};
            guard stored >= [pre.slot=>p];
        } }
        #[inductive(initialize)] fn initialize_inductive(post:Self,p:PointsTo<T>) {}
    }
}

pub fn borrowed_reader_demo() -> (out: u64)
    ensures
        out == 7,
{
    let (cell, Tracked(permission)) = PCell::new(7u64);
    let ghost p = permission;
    let tracked mut base = IMap::tracked_empty();
    proof {
        base.tracked_insert(0int, permission);
    }
    let tracked token = GuardedReaders::Protocol::<u64>::initialize(base, p);
    proof {
        assert(GuardedReaders::Protocol::<u64>::reader_guard_requires(token.fragment(), p)) by {
            assert forall|z: GuardedReaders::Fragment<u64>, pre: GuardedReaders::State<u64>|
                pre.invariant() && GuardedReaders::Fragment::<u64>::op(token.fragment(), z)
                    == GuardedReaders::Protocol::<u64>::embed(pre) implies GuardedReaders::State::<
                u64,
            >::reader_guard_owners_enabled(
                pre,
                token.fragment(),
                GuardedReaders::Fragment::<u64>::unit(),
                p,
            ) && GuardedReaders::State::<u64>::reader_guard_enabled(pre, p) by {
                vstd::resource::tsm_finite_multiset::finite_multiset_owned_frame(
                    token.fragment().readers,
                    z.readers,
                    pre.readers,
                    p,
                );
                token.fragment().op_unit();
            };
        }
    }
    let tracked guarded = GuardedReaders::Protocol::<u64>::reader_guard(&token, p);
    let tracked permission = guarded.tracked_borrow(0int);
    *cell.borrow(Tracked(permission))
}

fn main() {
    let out = borrowed_reader_demo();
    assert(out == 7);
}

} // verus!
