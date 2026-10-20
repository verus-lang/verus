//! Guards that borrow no token, in machines with type parameters and storage.
//!
//! A guard needs a storage resource of the instance to guard from. Without a
//! borrowed token (or with only borrowed token collections, which may be
//! empty), a machine without type parameters guards from a leaked `&'static`
//! unit token held by its `Instance`. With type parameters a leaked reference
//! would need them to be `'static`, and the instance cannot own the token
//! instead (a storage token can be split but not duplicated, so the instance
//! would not be clonable). Such a guard therefore borrows a `Unit` of the
//! instance (`&Unit`, as last argument), like the operations that consume no
//! token take one, and the type parameters need no `'static` bound.
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
use vstd::tokens::*;

// A guard reading only a constant.
verified_tokenized_state_machine! {
    Fixed<T> {
        fields {
            #[sharding(constant)]
            pub val: T,

            #[sharding(storage_option)]
            pub cell: Option<T>,
        }

        #[invariant]
        pub fn inv(&self) -> bool {
            self.cell == Some(self.val)
        }

        init!{
            initialize(v: T) {
                init val = v;
                init cell = Some(v);
            }
        }

        property!{
            peek() {
                guard cell >= Some(pre.val);
            }
        }

        #[inductive(initialize)]
        fn initialize_inductive(post: Self, v: T) { }
    }
}

// A guard whose borrowed inputs are a token collection (possibly empty).
verified_tokenized_state_machine! {
    Shelf<T> {
        fields {
            #[sharding(map)]
            pub owners: Map<int, T>,

            #[sharding(storage_map)]
            pub store: Map<int, T>,
        }

        #[invariant]
        pub fn inv(&self) -> bool {
            self.store == self.owners
        }

        init!{
            initialize(m: Map<int, T>) {
                init owners = m;
                init store = m;
            }
        }

        property!{
            peek_many(m: Map<int, T>) {
                have owners >= (m);
                guard store >= (m);
            }
        }

        #[inductive(initialize)]
        fn initialize_inductive(post: Self, m: Map<int, T>) { }
    }
}

verus! {

// Generic clients: no `'static` bound on `T`.
proof fn fixed_client<T>(tracked v: T, x: T)
    requires v == x,
{
    let tracked (Tracked(inst), Tracked(unit)) = Fixed::Instance::<T>::initialize_with_unit(x, Some(v));
    assert(inst.val() == x);
    let tracked g = inst.peek(&unit);
    assert(*g == x);
}

proof fn shelf_client<T>(tracked v: T, x: T)
    requires v == x,
{
    let m = Map::<int, T>::empty().insert(1, x);
    let tracked mut stored = Map::tracked_empty();
    stored.tracked_insert(1int, v);
    assert(stored =~= m);
    let tracked (Tracked(inst), Tracked(owners), Tracked(unit)) = Shelf::Instance::<T>::initialize_with_unit(m, stored);
    assert(owners.map() =~= m);
    let tracked g = inst.peek_many(m, &owners, &unit);
    assert(g.dom() == m.dom());
    assert(m.dom().contains(1));
    assert(*g[1] == x);
}

}

fn main() {}
