#[allow(unused_imports)]
use builtin::*;
mod pervasive;
use pervasive::*;
use pervasive::multiset::*;
use pervasive::option::*;
use pervasive::ptr::*;
use pervasive::cell::*;

use state_machines_macros::concurrent_state_machine;

// TODO make T generic
struct T {
    t: u8,
}

concurrent_state_machine!(RwLock {
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

    #[init]
    fn initialize_empty(&self) {
        init(flags, (true, 0));
        init(storage, Option::None);
        init(pending_writer, Option::None);
        init(writer, Option::Some(()));
        init(pending_reader, Multiset::empty());
        init(reader, Multiset::empty());
    }

    #[inductive(initialize_empty)]
    fn initialize_empty_inductive(post: RwLock) { }

    /// Increment the 'rc' counter, obtain a pending_reader
    #[transition]
    fn acquire_read_start(&self) {
        update(flags, (self.flags.0, self.flags.1 + 1));
        add_element(pending_reader, ());
    }

    /// Exchange the pending_reader for a reader by checking
    /// that the 'exc' bit is 0
    #[transition]
    fn acquire_read_end(&self) {
        require(self.flags.0 == false);

        remove_element(pending_reader, ());

        #[birds_eye] let x = self.storage.get_Some_0();
        add_element(reader, x);
    }

    /// Decrement the 'rc' counter, abandon the attempt to gain
    /// the 'read' lock.
    #[transition]
    fn acquire_read_abandon(&self) {
        remove_element(pending_reader, ());
        assert(self.flags.1 >= 1);
        update(flags, (self.flags.0, self.flags.1 - 1));
    }

    /// Atomically set 'exc' bit from 'false' to 'true'
    /// Obtain a pending_writer
    #[transition]
    fn acquire_exc_start(&self) {
        require(self.flags.0 == false);
        update(flags, (true, self.flags.1));
        add_some(pending_writer, ());
    }

    /// Finish obtaining the write lock by checking that 'rc' is 0.
    /// Exchange the pending_writer for a writer and withdraw the
    /// stored object.
    #[transition]
    fn acquire_exc_end(&self) {
        require(self.flags.1 == 0);

        remove_some(pending_writer, ());

        add_some(writer, ());

        #[birds_eye] let x = self.storage.get_Some_0();
        withdraw_some(storage, x);
    }

    /// Release the write-lock. Update the 'exc' bit back to 'false'.
    /// Return the 'writer' and also deposit an object back into storage.
    #[transition]
    fn release_exc(&self, x: T) {
        remove_some(writer, ());

        update(flags, (false, self.flags.1));

        deposit_some(storage, x);
    }

    /// Check that the 'reader' is actually a guard for the given object.
    #[readonly]
    fn read_guard(&self, x: T) {
        have_element(reader, x);
        guard_some(storage, x);
    }

    /// Release the reader-lock. Decrement 'rc' and return the 'reader' object.
    #[transition]
    fn release_shared(&self, x: T) {
        remove_element(reader, x);

        //assert(self.flags.1 >= 1);
        update(flags, (self.flags.0, self.flags.1 - 1));
    }

    #[invariant]
    fn exc_bit_matches(&self) -> bool {
        (if self.flags.0 { 1 } else { 0 }) ==
            (if self.pending_writer.is_Some() { 1 } else { 0 })
            + (if self.writer.is_Some() { 1 } else { 0 })
    }

    #[invariant]
    fn count_matches(&self) -> bool {
        self.flags.1 == self.pending_reader.count(())
            + self.reader.count(self.storage.get_Some_0())
    }

    #[invariant]
    fn reader_agrees_storage(&self) -> bool {
        forall(|t: T| self.reader.count(t) > 0 >>=
            equal(self.storage, Option::Some(t)))
    }

    #[invariant]
    fn writer_agrees_storage(&self) -> bool {
        self.writer.is_Some() >>= self.storage.is_None()
    }

    #[invariant]
    fn writer_agrees_storage_rev(&self) -> bool {
        self.storage.is_None() >>= self.writer.is_Some()
    }

    #[inductive(acquire_read_start)]
    fn acquire_read_start_inductive(self: RwLock, post: RwLock) { }

    #[inductive(acquire_read_end)]
    fn acquire_read_end_inductive(self: RwLock, post: RwLock) { }

    #[inductive(acquire_read_abandon)]
    fn acquire_read_abandon_inductive(self: RwLock, post: RwLock) { }

    #[inductive(acquire_exc_start)]
    fn acquire_exc_start_inductive(self: RwLock, post: RwLock) { }

    #[inductive(acquire_exc_end)]
    fn acquire_exc_end_inductive(self: RwLock, post: RwLock) { }

    #[inductive(release_exc)]
    fn release_exc_inductive(self: RwLock, post: RwLock, x: T) { }


    #[inductive(release_shared)]
    fn release_shared_inductive(self: RwLock, post: RwLock, x: T) {
        assert(equal(self.storage, Option::Some(x)));
    }
});

fn main() { }
