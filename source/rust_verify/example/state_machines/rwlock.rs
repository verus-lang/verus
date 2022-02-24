#[allow(unused_imports)]
use builtin::*;
mod pervasive;
use pervasive::*;
use pervasive::multiset::*;
use pervasive::option::*;

use state_machines_macros::concurrent_state_machine;

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

    #[transition]
    fn acquire_read_start(&self) {
        update(flags, (self.flags.0, self.flags.1 + 1));
        add_element(pending_reader, ());
    }

    #[transition]
    fn acquire_read_end(&self) {
        require(self.flags.0 == false);

        remove_element(pending_reader, ());

        let x = self.storage.get_Some_0();
        add_element(reader, x);
    }

    #[transition]
    fn acquire_read_abandon(&self) {
        remove_element(pending_reader, ());
        assert(self.flags.1 >= 1);
        update(flags, (self.flags.0, self.flags.1 - 1));
    }

    #[transition]
    fn acquire_exc_start(&self) {
        require(self.flags.0 == false);
        update(flags, (true, self.flags.1));
        add_some(pending_writer, ());
    }

    #[transition]
    fn acquire_exc_end(&self) {
        require(self.flags.1 == 0);

        remove_some(pending_writer, ());

        add_some(writer, ());

        withdraw_some(storage, self.storage.is_Some());
    }

    #[transition]
    fn release_exc(&self, x: T) {
        remove_some(writer, ());

        update(flags, (false, self.flags.1));

        deposit_some(storage, x);
    }

    #[readonly]
    fn read_guard(&self, x: T) {
        have_element(reader, x);
        guard_some(storage, x);
    }

    #[transition]
    fn release_shared(&self, x: T) {
        remove_element(reader, x);

        assert(self.flags.1 >= 1);
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
