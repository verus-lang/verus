// rust_verify/tests/example.rs
#[allow(unused_imports)]
use verus_builtin::*;
use vstd::cell::*;
use vstd::multiset::*;
use vstd::prelude::*;
use vstd::{pervasive::*, *};

use verus_state_machines_macros::verified_tokenized_state_machine;

// TODO make T generic
#[verifier::verify]
pub struct T {
    t: u8,
}

verified_tokenized_state_machine!(

    #[verified_local_ready(acquire_read_start,acquire_read_end,acquire_read_abandon,acquire_exc_start,acquire_exc_end,release_exc,release_shared)]
    RwLock {
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

verus! {

fn main() {
    proof {
        let tracked (instance, flags, pending_writer, writer, pending_reader, reader) =
            RwLock::Instance::initialize_empty();
        let tracked instance = instance.get();
        let tracked mut flags = flags.get();
        assert(pending_writer@ is None);
        assert(writer@ is Some);
        let tracked writer = writer.get().tracked_unwrap();
        assert(pending_reader@.multiset() == Multiset::empty());
        assert(reader@.multiset() == Multiset::empty());

        // A reader can begin while an exclusive owner holds the object, then abandon.
        let tracked pending_reader = instance.acquire_read_start(&mut flags);
        instance.acquire_read_abandon(&mut flags, pending_reader);
        assert(flags.value() == (true, 0nat));

        let tracked value = T { t: 7 };
        let ghost deposited_value = value;
        instance.release_exc(deposited_value, &mut flags, writer, value);
        assert(flags.value() == (false, 0nat));

        let tracked pending_reader = instance.acquire_read_start(&mut flags);
        let tracked reader = instance.acquire_read_end(&flags, pending_reader);
        let ghost value = reader.element();
        let tracked guarded = instance.read_guard(value, &reader);
        assert(*guarded == value);

        // The guard persists through another reader's start/abandon operations and
        // through publishing exclusive intent. The writer still needs reader count zero.
        let tracked pending_reader = instance.acquire_read_start(&mut flags);
        instance.acquire_read_abandon(&mut flags, pending_reader);
        let tracked pending_writer = instance.acquire_exc_start(&mut flags);
        assert(*guarded == value);

        instance.release_shared(value, &mut flags, reader);
        let tracked (writer, previous) = instance.acquire_exc_end(&flags, pending_writer);
        let tracked writer = writer.get();
        let tracked previous = previous.get();

        // Release the exclusive owner with a replacement object.
        let tracked replacement = T { t: 9 };
        let ghost replacement_value = replacement;
        instance.release_exc(replacement_value, &mut flags, writer, replacement);
        assert(flags.value() == (false, 0nat));
    }
}

} // verus!
