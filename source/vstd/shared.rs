#![allow(non_snake_case)]

use super::prelude::*;

#[cfg(verus_keep_ghost)]
use state_machines_macros::*;

#[cfg(verus_keep_ghost)]
tokenized_state_machine_vstd!(Dupe<T> {
    fields {
        #[sharding(storage_option)]
        pub storage: Option<T>,

        #[sharding(constant)]
        pub val: T,
    }

    init!{
        initialize_one(t: T) {
            // Initialize with a single reader
            init storage = Option::Some(t);
            init val = t;
        }
    }

    #[invariant]
    pub fn agreement(&self) -> bool {
        self.storage == Option::Some(self.val)
    }

    property!{
        borrow() {
            guard storage >= Some(pre.val);
        }
    }

     #[inductive(initialize_one)]
     fn initialize_one_inductive(post: Self, t: T) { }
});

#[cfg(verus_keep_ghost)]
verus! {

/// A `tracked ghost` container that you can put a ghost object in.
/// A `Shared<T>` is duplicable and lets you get a `&T` out.
pub tracked struct Shared<T> {
    tracked inst: Dupe::Instance<T>,
}

impl<T> Shared<T> {
    pub closed spec fn view(self) -> T {
        self.inst.val()
    }

    pub proof fn new(tracked t: T) -> (tracked s: Self)
        ensures
            s@ == t,
    {
        let tracked inst = Dupe::Instance::initialize_one(t, Option::Some(t));
        Shared { inst }
    }

    pub proof fn clone(tracked &self) -> (tracked other: Self)
        ensures
            self@ == other@,
    {
        Shared { inst: self.inst.clone() }
    }

    pub proof fn borrow(tracked &self) -> (tracked t: &T)
        ensures
            *t == self@,
    {
        self.inst.borrow()
    }
}

} // verus!
