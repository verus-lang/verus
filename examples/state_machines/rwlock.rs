#[allow(unused_imports)]
use builtin::*;
use vstd::cell::*;
use vstd::multiset::*;
use vstd::prelude::*;
use vstd::{pervasive::*, *};

use state_machines_macros::tokenized_state_machine;

// TODO make T generic
#[verifier::verify]
pub struct T {
    t: u8,
}

tokenized_state_machine!(RwLock {
    fields {
        #[sharding(variable)]
        pub flags: (bool, nat),

        #[sharding(storage_option)]
        pub storage: Option<T>,

        #[sharding(option)]
        pub pending_writer: Option<()>,

        #[sharding(option)]
        pub writer: Option<()>,

        #[sharding(multiset)]
        pub pending_reader: Multiset<()>,

        #[sharding(multiset)]
        pub reader: Multiset<T>,
    }

    init!{
        initialize_empty() {
            init flags = (true, 0);
            init storage = Option::None;
            init pending_writer = Option::None;
            init writer = Option::Some(());
            init pending_reader = Multiset::empty();
            init reader = Multiset::empty();
        }
    }

    #[inductive(initialize_empty)]
    fn initialize_empty_inductive(post: Self) { }

    /// Increment the 'rc' counter, obtain a pending_reader
    transition!{
        acquire_read_start() {
            update flags = (pre.flags.0, pre.flags.1 + 1);
            add pending_reader += {()};
        }
    }

    /// Exchange the pending_reader for a reader by checking
    /// that the 'exc' bit is 0
    transition!{
        acquire_read_end() {
            require(pre.flags.0 == false);

            remove pending_reader -= {()};

            birds_eye let x: T = pre.storage.get_Some_0();
            add reader += {x};
        }
    }

    /// Decrement the 'rc' counter, abandon the attempt to gain
    /// the 'read' lock.
    transition!{
        acquire_read_abandon() {
            remove pending_reader -= {()};
            assert(pre.flags.1 >= 1);
            update flags = (pre.flags.0, (pre.flags.1 - 1) as nat);
        }
    }

    /// Atomically set 'exc' bit from 'false' to 'true'
    /// Obtain a pending_writer
    transition!{
        acquire_exc_start() {
            require(pre.flags.0 == false);
            update flags = (true, pre.flags.1);
            add pending_writer += Some(());
        }
    }

    /// Finish obtaining the write lock by checking that 'rc' is 0.
    /// Exchange the pending_writer for a writer and withdraw the
    /// stored object.
    transition!{
        acquire_exc_end() {
            require(pre.flags.1 == 0);

            remove pending_writer -= Some(());

            add writer += Some(());

            birds_eye let x = pre.storage.get_Some_0();
            withdraw storage -= Some(x);
        }
    }

    /// Release the write-lock. Update the 'exc' bit back to 'false'.
    /// Return the 'writer' and also deposit an object back into storage.
    transition!{
        release_exc(x: T) {
            remove writer -= Some(());

            update flags = (false, pre.flags.1);

            deposit storage += Some(x);
        }
    }

    /// Check that the 'reader' is actually a guard for the given object.
    property!{
        read_guard(x: T) {
            have reader >= {x};
            guard storage >= Some(x);
        }
    }

    /// Release the reader-lock. Decrement 'rc' and return the 'reader' object.
    #[transition]
    transition!{
        release_shared(x: T) {
            remove reader -= {x};

            assert(pre.flags.1 >= 1) by {
                //assert(pre.reader.count(x) >= 1);
                assert(equal(pre.storage, Option::Some(x)));
                //assert(equal(x, pre.storage.get_Some_0()));
            };
            update flags = (pre.flags.0, (pre.flags.1 - 1) as nat);
        }
    }

    #[invariant]
    pub fn exc_bit_matches(&self) -> bool {
        (if self.flags.0 { 1 } else { 0 as int }) ==
            (if self.pending_writer.is_Some() { 1 } else { 0 as int }) as int
            + (if self.writer.is_Some() { 1 } else { 0 as int }) as int
    }

    #[invariant]
    pub fn count_matches(&self) -> bool {
        self.flags.1 == self.pending_reader.count(())
            + self.reader.count(self.storage.get_Some_0())
    }

    #[invariant]
    pub fn reader_agrees_storage(&self) -> bool {
        forall |t: T| self.reader.count(t) > 0 ==>
            equal(self.storage, Option::Some(t))
    }

    #[invariant]
    pub fn writer_agrees_storage(&self) -> bool {
        self.writer.is_Some() ==> self.storage.is_None()
    }

    #[invariant]
    pub fn writer_agrees_storage_rev(&self) -> bool {
        self.storage.is_None() ==> self.writer.is_Some()
    }

    #[inductive(acquire_read_start)]
    fn acquire_read_start_inductive(pre: Self, post: Self) { }

    #[inductive(acquire_read_end)]
    fn acquire_read_end_inductive(pre: Self, post: Self) { }

    #[inductive(acquire_read_abandon)]
    fn acquire_read_abandon_inductive(pre: Self, post: Self) { }

    #[inductive(acquire_exc_start)]
    fn acquire_exc_start_inductive(pre: Self, post: Self) { }

    #[inductive(acquire_exc_end)]
    fn acquire_exc_end_inductive(pre: Self, post: Self) { }

    #[inductive(release_exc)]
    fn release_exc_inductive(pre: Self, post: Self, x: T) { }

    #[inductive(release_shared)]
    fn release_shared_inductive(pre: Self, post: Self, x: T) {
        assert(equal(pre.storage, Option::Some(x)));
    }
});

fn main() {}
