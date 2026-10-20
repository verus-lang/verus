//! A machine with many (ten) storage fields. The storage is one
//! `IMap<__StorageKey, __StorageValue<T>>` tagged by field (the value enum is
//! over the type parameter `T`, the only one the payloads mention; `U` occurs
//! only in a non-storage field), defined per key with more than eight parts.
//! Exercised: general `storage_imap` operands (of finite domains, stated with
//! `require`), a general guard of a `storage_imap` field (`IMap<K, &V>`), two
//! guards of one `storage_map` field (`Map<K, &V>`), and optional stores.
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
use vstd::tokens::*;

verified_tokenized_state_machine! {
    Many<T, U> {
        fields {
            #[sharding(imap)]
            pub owners: IMap<int, u64>,

            #[sharding(option)]
            pub flag_owner: Option<bool>,

            #[sharding(map)]
            pub cell_owners: Map<int, T>,

            #[sharding(variable)]
            pub tag: Option<U>,

            #[sharding(variable)]
            pub stashed: bool,

            #[sharding(storage_imap)]
            pub store: IMap<int, u64>,

            #[sharding(storage_option)]
            pub flag: Option<bool>,

            #[sharding(storage_map)]
            pub cells: Map<int, T>,

            #[sharding(storage_option)]
            pub s3: Option<u64>,

            #[sharding(storage_option)]
            pub s4: Option<u64>,

            #[sharding(storage_option)]
            pub s5: Option<bool>,

            #[sharding(storage_option)]
            pub s6: Option<bool>,

            #[sharding(storage_option)]
            pub s7: Option<T>,

            #[sharding(storage_map)]
            pub s8: Map<int, u64>,

            #[sharding(storage_option)]
            pub s9: Option<u64>,
        }

        #[invariant]
        pub fn inv(&self) -> bool {
            &&& self.store == self.owners
            &&& self.flag == self.flag_owner
            &&& self.cells == self.cell_owners
            &&& self.s3 is Some <==> self.stashed
            &&& self.s8.dom().contains(7) <==> self.stashed
        }

        init!{
            initialize(m: IMap<int, u64>, b: bool, c: Map<int, T>) {
                require(m.dom().finite());
                init owners = m;
                init flag_owner = Some(b);
                init cell_owners = c;
                init tag = None;
                init stashed = false;
                init store = m;
                init flag = Some(b);
                init cells = c;
                init s3 = None;
                init s4 = None;
                init s5 = None;
                init s6 = None;
                init s7 = None;
                init s8 = Map::empty();
                init s9 = None;
            }
        }

        transition!{
            take_many(m: IMap<int, u64>) {
                require(m.dom().finite());
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

        // Deposits into and withdrawals from two further storage fields.
        transition!{
            stash(x: u64, y: u64) {
                require(!pre.stashed);
                update stashed = true;
                deposit s3 += Some(x);
                deposit s8 += [7 => y];
            }
        }

        transition!{
            unstash() {
                require(pre.stashed);
                update stashed = false;
                withdraw s3 -= Some(let _x);
                withdraw s8 -= [7 => let _y];
            }
        }

        // A general guard of the `storage_imap` field: a map of references
        // to the guarded values, for a finite domain.
        property!{
            peek_store(m: IMap<int, u64>) {
                require(m.dom().finite());
                have owners >= (m);
                guard store >= (m);
            }
        }

        // Two general guards of one `storage_map` field and a guard of another
        // field in one property.
        property!{
            peek_cells(c1: Map<int, T>, c2: Map<int, T>, b: bool) {
                have cell_owners >= (c1);
                have cell_owners >= (c2);
                have flag_owner >= Some(b);
                guard cells >= (c1);
                guard cells >= (c2);
                guard flag >= Some(b);
            }
        }

        #[inductive(initialize)]
        fn initialize_inductive(post: Self, m: IMap<int, u64>, b: bool, c: Map<int, T>) { }

        #[inductive(take_many)]
        fn take_many_inductive(pre: Self, post: Self, m: IMap<int, u64>) {
            assert(post.store =~= post.owners);
        }

        #[inductive(take_flag)]
        fn take_flag_inductive(pre: Self, post: Self, b: bool) { }

        #[inductive(stash)]
        fn stash_inductive(pre: Self, post: Self, x: u64, y: u64) { }

        #[inductive(unstash)]
        fn unstash_inductive(pre: Self, post: Self) { }
    }
}

verus! {

proof fn client(tracked stored: IMap<int, u64>, tracked cells: Map<int, u8>, tracked x: u64, tracked y: u64)
    requires
        stored == IMap::<int, u64>::empty().insert(5, 7u64),
        cells == Map::<int, u8>::empty().insert(1, 10u8),
        x == 3,
        y == 4,
{
    let m = IMap::<int, u64>::empty().insert(5, 7u64);
    let c = Map::<int, u8>::empty().insert(1, 10u8);
    let tracked (Tracked(inst), Tracked(owners), Tracked(flag_owner), Tracked(cell_owners), Tracked(tag), Tracked(stashed)) =
        Many::Instance::<u8, bool>::initialize(m, true, c, stored, Some(true), cells, None, None, None, None, None, Map::tracked_empty(), None);
    assert(owners.map() =~= m);
    assert(cell_owners.map() =~= c);
    let tracked mut fo = flag_owner.tracked_unwrap();
    // A guard of the store, borrowing a collection (and, as the machine has
    // type parameters, a unit).
    let tracked u = inst.unit_from_flag_owner(&mut fo);
    let tracked g = inst.peek_store(m, &owners, &u);
    assert(m.dom().contains(5));
    assert(*g[5] == 7u64);
    // Two guards of one map field and a guard of an option field.
    let tracked (Tracked(gf), Tracked(g1), Tracked(g2)) = inst.peek_cells(c, c, true, &fo, &cell_owners, &cell_owners);
    assert(g1.dom() =~= c.dom());
    assert(c.dom().contains(1));
    assert(*g1[1] == 10u8);
    assert(*g2[1] == 10u8);
    assert(*gf == true);
    // Deposit into and withdraw from two further storage fields.
    let tracked mut stashed = stashed;
    inst.stash(3, 4, &mut stashed, x, y);
    let tracked (Tracked(_x2), Tracked(_y2)) = inst.unstash(&mut stashed);
    // A general withdrawal.
    let tracked u = inst.unit_from_flag_owner(&mut fo);
    let tracked w = inst.take_many(m, owners, u);
    assert(w == m);
    // Withdraw the flag.
    let tracked f = inst.take_flag(true, fo);
    assert(f == true);
}

}

fn main() {}
