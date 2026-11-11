// EXPECTED-ERROR: a general withdrawal from storage_imap field `store` needs a finite domain
// Operands of a `storage_imap` field are tagged into the storage map
// (`IMap<__StorageKey, __StorageValue>`) and back key by key, so a general
// withdrawal and the initial value need a finite domain, which this machine
// does not state (`infinite_client` passes the total map). Compare
// `generic_tokens_tagged_imap_withdraw.rs`, which states it.
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
use vstd::tokens::*;

verified_tokenized_state_machine! {
    Mixed {
        fields {
            #[sharding(imap)]
            pub owners: IMap<int, u64>,

            #[sharding(option)]
            pub flag_owner: Option<bool>,

            #[sharding(storage_imap)]
            pub store: IMap<int, u64>,

            #[sharding(storage_option)]
            pub flag: Option<bool>,
        }

        #[invariant]
        pub fn inv(&self) -> bool {
            self.store == self.owners && self.flag == self.flag_owner
        }

        init!{
            initialize(m: IMap<int, u64>, b: bool) {
                init owners = m;
                init flag_owner = Some(b);
                init store = m;
                init flag = Some(b);
            }
        }

        transition!{
            take_many(m: IMap<int, u64>) {
                remove owners -= (m);
                withdraw store -= (m);
            }
        }

        transition!{
            take_flag(b: bool) {
                remove flag_owner -= Some(b);
                withdraw flag -= Some(b);
            }
        }

        #[inductive(initialize)]
        fn initialize_inductive(post: Self, m: IMap<int, u64>, b: bool) { }

        #[inductive(take_many)]
        fn take_many_inductive(pre: Self, post: Self, m: IMap<int, u64>) {
            assert(post.store =~= post.owners);
        }

        #[inductive(take_flag)]
        fn take_flag_inductive(pre: Self, post: Self, b: bool) { }
    }
}

verus! {

proof fn client() {
    let m = IMap::<int, u64>::empty().insert(1, 10).insert(2, 20);
    let tracked mut stored = IMap::tracked_empty();
    stored.tracked_insert(1int, 10u64);
    stored.tracked_insert(2int, 20u64);
    assert(stored =~= m);
    assert(m.dom() =~= ISet::empty().insert(1int).insert(2int));
    let tracked (Tracked(inst), Tracked(owners), Tracked(flag_owner)) =
        Mixed::Instance::initialize(m, true, stored, Some(true));
    assert(owners.map() =~= m);
    let tracked mut owners = owners;
    // Withdraw the entry for 2 (a finite part).
    let tracked two = owners.remove(2);
    let tracked mut part = Mixed::owners_map::empty(inst.id());
    part.insert(two);
    let m2 = IMap::<int, u64>::empty().insert(2, 20);
    assert(part.map() =~= m2);
    assert(m2.dom() =~= ISet::empty().insert(2int));
    // The operation consumes only a collection: it takes a unit of the instance.
    let tracked mut fo = flag_owner.tracked_unwrap();
    let tracked u = inst.unit_from_flag_owner(&mut fo);
    let tracked w = inst.take_many(m2, part, u);
    assert(w =~= m2);
    assert(w[2] == 20);
    let tracked f = inst.take_flag(true, fo);
    assert(f == true);
}

}

verus! {
/// An infinite storage_imap deposit and an infinite general withdrawal, in a
/// machine with storage fields of different payload types.
proof fn infinite_client(tracked stored: IMap<int, u64>)
    requires
        stored == IMap::<int, u64>::total(|k: int| 7u64),
{
    let m = IMap::<int, u64>::total(|k: int| 7u64);
    let tracked (Tracked(inst), Tracked(owners), Tracked(flag_owner)) =
        Mixed::Instance::initialize(m, true, stored, Some(true));
    let tracked mut fo = flag_owner.tracked_unwrap();
    let tracked u = inst.unit_from_flag_owner(&mut fo);
    assert(owners.map() =~= m);
    let tracked w = inst.take_many(m, owners, u);
    assert(w == m);
    assert(w.dom() =~= ISet::<int>::full());
}
}

fn main() {}
