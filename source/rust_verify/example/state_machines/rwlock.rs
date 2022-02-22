#[allow(unused_imports)]
use builtin::*;
mod pervasive;
use pervasive::*;
use pervasive::multiset::*;

use state_machines_macros::concurrent_state_machine;

struct T {
    t: u8,
}

concurrent_state_machine!(RwLock {
    fields {
        #[sharding(variable)]
        pub flags: (bool, nat),

        #[sharding(not_tokenized)]
        pub storage: Option<T>,

        #[sharding(variable)]
        pub writer: Option<()>,

        #[sharding(multiset)]
        pub pending_reader: Multiset<()>,

        #[sharding(multiset)]
        pub reader: Multiset<T>,
    }

    #[transition]
    fn start_read(&self) {
        update(flags, (self.flags.0, self.flags.1 + 1));
        add_element(pending_reader, ());
    }

    #[transition]
    fn finish_read(&self) {
        require(self.flags.0 == false);

        remove_element(pending_reader, ());

        let x = self.storage.storage.get_Some_0();
        add_element(pending_reader, x);
    }

    #[inductive(start_read)]
    fn start_read_inductive(self: RwLock, post: RwLock) { }

    #[inductive(finish_read)]
    fn finish_read_inductive(self: RwLock, post: RwLock) { }
});

fn main() { }
