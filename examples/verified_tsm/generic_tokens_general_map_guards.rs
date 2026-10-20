//! Guards of general operands of `storage_map` and `storage_imap` fields
//! with other storage fields, or with other guards in one property.
//!
//! The trusted interface returns `&Map<K, V>` for `guard f >= (m)`. No map of
//! type `IMap<K, V>` exists in the guarded storage (its keys and values are
//! tagged by field), so the guard returns a map of references into the
//! storage: `Map<K, &V>` with the domain of `m` and `*out[k] == m[k]`
//! (`IMap<K, &V>` for a `storage_imap`, whose operand then needs a finite
//! domain, stated with a `require`); also with one storage field and one
//! guard (`generic_tokens_general_guards.rs`).
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
use vstd::tokens::*;

// A `storage_map` and a `storage_option` of different payload types.
// Several guards in one property.
verified_tokenized_state_machine! {
    Mixed {
        fields {
            #[sharding(map)]
            pub owners: Map<int, u64>,

            #[sharding(option)]
            pub flag_owner: Option<bool>,

            #[sharding(storage_map)]
            pub store: Map<int, u64>,

            #[sharding(storage_option)]
            pub flag: Option<bool>,
        }

        #[invariant]
        pub fn inv(&self) -> bool {
            self.store == self.owners && self.flag == self.flag_owner
        }

        init!{
            initialize(m: Map<int, u64>, b: bool) {
                init owners = m;
                init flag_owner = Some(b);
                init store = m;
                init flag = Some(b);
            }
        }

        property!{
            peek(m: Map<int, u64>) {
                have owners >= (m);
                guard store >= (m);
            }
        }

        // Two general guards of one field, and a guard of another field.
        property!{
            peek_three(m1: Map<int, u64>, m2: Map<int, u64>, b: bool) {
                have owners >= (m1);
                have owners >= (m2);
                have flag_owner >= Some(b);
                guard store >= (m1);
                guard store >= (m2);
                guard flag >= Some(b);
            }
        }

        #[inductive(initialize)]
        fn initialize_inductive(post: Self, m: Map<int, u64>, b: bool) { }
    }
}

// One `storage_map` field (the plain layout), two guards in one property.
verified_tokenized_state_machine! {
    Single {
        fields {
            #[sharding(map)]
            pub owners: Map<int, u64>,

            #[sharding(storage_map)]
            pub store: Map<int, u64>,
        }

        #[invariant]
        pub fn inv(&self) -> bool {
            self.store == self.owners
        }

        init!{
            initialize(m: Map<int, u64>) {
                init owners = m;
                init store = m;
            }
        }

        property!{
            peek_two(m1: Map<int, u64>, m2: Map<int, u64>) {
                have owners >= (m1);
                have owners >= (m2);
                guard store >= (m1);
                guard store >= (m2);
            }
        }

        #[inductive(initialize)]
        fn initialize_inductive(post: Self, m: Map<int, u64>) { }
    }
}

// Two storage fields of one payload type, including a `storage_imap` (whose
// initial value is moved into the tagged storage key by key: a finite domain).
verified_tokenized_state_machine! {
    Homogeneous {
        fields {
            #[sharding(map)]
            pub left_owners: Map<int, u64>,

            #[sharding(imap)]
            pub right_owners: IMap<int, u64>,

            #[sharding(storage_map)]
            pub left: Map<int, u64>,

            #[sharding(storage_imap)]
            pub right: IMap<int, u64>,
        }

        #[invariant]
        pub fn inv(&self) -> bool {
            self.left == self.left_owners && self.right == self.right_owners
        }

        init!{
            initialize(l: Map<int, u64>, r: IMap<int, u64>) {
                require(r.dom().finite());
                init left_owners = l;
                init right_owners = r;
                init left = l;
                init right = r;
            }
        }

        property!{
            peek_both(l: Map<int, u64>, r: IMap<int, u64>) {
                require(r.dom().finite());
                have left_owners >= (l);
                have right_owners >= (r);
                guard left >= (l);
                guard right >= (r);
            }
        }

        #[inductive(initialize)]
        fn initialize_inductive(post: Self, l: Map<int, u64>, r: IMap<int, u64>) { }
    }
}

verus! {

proof fn mixed_client() {
    let m = Map::<int, u64>::empty().insert(1, 10).insert(2, 20);
    let tracked mut stored = Map::tracked_empty();
    stored.tracked_insert(1int, 10u64);
    stored.tracked_insert(2int, 20u64);
    assert(stored =~= m);
    let tracked (Tracked(inst), Tracked(owners), Tracked(flag_owner)) =
        Mixed::Instance::initialize(m, true, stored, Some(true));
    assert(owners.map() =~= m);
    let tracked flag_owner = flag_owner.tracked_unwrap();
    let tracked g = inst.peek(m, &owners);
    assert(g.dom() == m.dom());
    assert(m.dom().contains(2));
    assert(*g[2] == 20);
    let m1 = Map::<int, u64>::empty().insert(1, 10);
    let m2 = Map::<int, u64>::empty().insert(1, 10).insert(2, 20);
    assert(m1.submap_of(owners.map()));
    assert(m2.submap_of(owners.map()));
    let tracked (Tracked(g1), Tracked(g2), Tracked(f)) = inst.peek_three(m1, m2, true, &owners, &owners, &flag_owner);
    assert(m1.dom().contains(1) && m2.dom().contains(2));
    assert(*g1[1] == 10 && *g2[2] == 20 && *f == true);
}

proof fn single_client() {
    let m = Map::<int, u64>::empty().insert(1, 10).insert(2, 20);
    let tracked mut stored = Map::tracked_empty();
    stored.tracked_insert(1int, 10u64);
    stored.tracked_insert(2int, 20u64);
    assert(stored =~= m);
    let tracked (Tracked(inst), Tracked(owners)) = Single::Instance::initialize(m, stored);
    assert(owners.map() =~= m);
    let tracked mut owners = owners;
    let tracked o2 = owners.remove(2);
    let tracked mut owners2 = MapToken::empty(inst.id());
    owners2.insert(o2);
    let m1 = Map::<int, u64>::empty().insert(1, 10);
    let m2 = Map::<int, u64>::empty().insert(2, 20);
    assert(m1 =~= owners.map());
    assert(m2 =~= owners2.map());
    let tracked (Tracked(g1), Tracked(g2)) = inst.peek_two(m1, m2, &owners, &owners2);
    assert(m1.dom().contains(1) && m2.dom().contains(2));
    assert(*g1[1] == 10 && *g2[2] == 20);
}

proof fn homogeneous_client() {
    let l = Map::<int, u64>::empty().insert(1, 10);
    let r = IMap::<int, u64>::empty().insert(5, 50);
    let tracked mut ls = Map::tracked_empty();
    ls.tracked_insert(1int, 10u64);
    let tracked mut rs = IMap::tracked_empty();
    rs.tracked_insert(5int, 50u64);
    assert(ls =~= l);
    assert(rs =~= r);
    let tracked (Tracked(inst), Tracked(lo), Tracked(ro)) = Homogeneous::Instance::initialize(l, r, ls, rs);
    assert(lo.map() =~= l);
    assert(ro.map() =~= r);
    assert(r.dom() =~= ISet::empty().insert(5));
    assert(r.dom().finite());
    let tracked (Tracked(gl), Tracked(gr)) = inst.peek_both(l, r, &lo, &ro);
    assert(l.dom().contains(1) && r.dom().contains(5));
    assert(*gl[1] == 10 && *gr[5] == 50);
}

}

fn main() {}
