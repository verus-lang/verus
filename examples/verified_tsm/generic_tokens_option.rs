//! Checked generic field tokens for `option` fields and the optional and
//! infinite-map storage strategies: a `storage_option` cell guarded by an
//! `option` token, two `storage_option` fields of one machine (indexed
//! storage keys), and a `storage_imap` field with general deposits.
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
use vstd::tokens::*;

verified_tokenized_state_machine! {
    #[verified_generic_tokens]
    Cell {
        fields {
            #[sharding(option)]
            pub owner: Option<int>,

            #[sharding(storage_option)]
            pub slot: Option<int>,

            #[sharding(storage_option)]
            pub spare: Option<int>,

            #[sharding(bool)]
            pub empty: bool,
        }

        #[invariant]
        pub fn inv(&self) -> bool {
            &&& self.owner is Some <==> self.slot is Some
            &&& self.owner is Some ==> self.slot == self.owner
            &&& self.spare is None
            &&& self.empty <==> self.owner is None
        }

        init!{
            initialize() {
                init owner = Some(0);
                init slot = Some(0);
                init spare = None;
                init empty = false;
            }
        }

        transition!{
            put(v: int) {
                remove empty -= true;
                add owner += Some(v);
                deposit slot += Some(v);
            }
        }

        transition!{
            take() {
                remove owner -= Some(let v);
                withdraw slot -= Some(v);
                add empty += true;
            }
        }

        property!{
            look(v: int) {
                have owner >= Some(v);
                guard slot >= Some(v);
            }
        }

        #[inductive(initialize)]
        fn initialize_inductive(post: Self) { }

        #[inductive(put)]
        fn put_inductive(pre: Self, post: Self, v: int) { }

        #[inductive(take)]
        fn take_inductive(pre: Self, post: Self) { }
    }
}

verified_tokenized_state_machine! {
    #[verified_generic_tokens]
    Bank {
        fields {
            #[sharding(set)]
            pub free: Set<int>,

            #[sharding(map)]
            pub claims: Map<int, int>,

            #[sharding(storage_imap)]
            pub vault: IMap<int, int>,

            #[sharding(variable)]
            pub epoch: int,
        }

        #[invariant]
        pub fn inv(&self) -> bool {
            &&& forall|k: int| #[trigger] self.claims.dom().contains(k) <==> self.vault.dom().contains(k)
            &&& forall|k: int| #[trigger] self.claims.dom().contains(k) ==> self.vault[k] == self.claims[k]
            &&& forall|k: int| #[trigger] self.free.contains(k) ==> !self.claims.dom().contains(k)
        }

        init!{
            initialize(free: Set<int>) {
                init free = free;
                init claims = Map::empty();
                init vault = IMap::empty();
                init epoch = 0;
            }
        }

        transition!{
            store(m: Map<int, int>) {
                // A general deposit into a `storage_imap` field is tagged key
                // by key: its domain is finite.
                require(m.to_imap().dom().finite());
                remove free -= (m.dom());
                add claims += (m);
                deposit vault += (m.to_imap());
            }
        }

        transition!{
            fetch(k: int) {
                remove claims -= [k => let v];
                withdraw vault -= [k => v];
            }
        }

        #[inductive(initialize)]
        fn initialize_inductive(post: Self, free: Set<int>) { }

        #[inductive(store)]
        fn store_inductive(pre: Self, post: Self, m: Map<int, int>) {
            assert forall|k: int| #[trigger] post.claims.dom().contains(k) <==> post.vault.dom().contains(k) by {
                assert(m.to_imap().dom().contains(k) == m.dom().contains(k));
            }
            assert forall|k: int| #[trigger] post.claims.dom().contains(k) implies post.vault[k] == post.claims[k] by {
                assert(m.to_imap().dom().contains(k) == m.dom().contains(k));
            }
        }

        #[inductive(fetch)]
        fn fetch_inductive(pre: Self, post: Self, k: int) { }
    }
}

verus! {
proof fn cell_client() {
    let tracked (Tracked(inst), Tracked(owner), Tracked(empty)) = Cell::Instance::initialize(Some(0), None);
    assert(empty is None);
    let tracked o = owner.tracked_unwrap();
    assert(o.value() == 0);
    let tracked (Tracked(v0), Tracked(e)) = inst.take(o);
    assert(v0 == 0);
    let tracked o = inst.put(5, 5, e);
    assert(o.value() == 5);
    let tracked g = inst.look(5, &o);
    assert(*g == 5);
    let tracked (Tracked(v), Tracked(e)) = inst.take(o);
    assert(v == 5);
}

proof fn bank_client() {
    let free = Set::<int>::empty().insert(1).insert(2).insert(3);
    let tracked (Tracked(inst), Tracked(free), Tracked(claims), Tracked(epoch)) = Bank::Instance::initialize(free, IMap::tracked_empty());
    let m = Map::<int, int>::empty().insert(1, 10).insert(2, 20);
    let tracked mut deposit = IMap::tracked_empty();
    deposit.tracked_insert(1int, 10int);
    deposit.tracked_insert(2int, 20int);
    assert(deposit == m.to_imap());
    assert(m.dom() <= free.set());
    assert(m.to_imap().dom() =~= m.dom().to_iset());
    vstd::set::lemma_to_iset_finite(m.dom());
    // The operation consumes only a token collection, so it takes a unit.
    let tracked mut epoch = epoch;
    let tracked u = inst.unit_from_epoch(&mut epoch);
    let tracked c = inst.store(m, free, deposit, u);
    assert(c.map() == m);
    let tracked mut c = c;
    let tracked c1 = c.remove(1);
    let tracked v = inst.fetch(1, c1);
    assert(v == 10);
}
}

fn main() {}
