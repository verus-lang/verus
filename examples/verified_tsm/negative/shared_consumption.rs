// EXPECTED-ERROR: precondition not satisfied
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
verus! {

verified_tokenized_state_machine! {
    #[verified_raw_tokens]

    SharedTicket {
        fields { #[sharding(count)] pub available:nat, #[sharding(count)] pub used:nat, }
        #[invariant] pub fn inv(&self)->bool { self.available + self.used == 1 }
        init! { initialize() { init available=1; init used=0; } }
        transition! { consume() { remove available -= (1); add used += (1); } }
        #[inductive(initialize)] fn initialize_inductive(post:Self) {}
        #[inductive(consume)] fn consume_inductive(pre:Self,post:Self) {}
    }
}

pub proof fn borrowed_ticket_is_not_owned() {
    use vstd::resource::tsm::CountRA;
    let tracked all = SharedTicket::Protocol::initialize();
    let empty = SharedTicket::Fragment {
        available: CountRA { count: 0 },
        used: CountRA { count: 0 },
    };
    let ticket = SharedTicket::Fragment {
        available: CountRA { count: 1 },
        used: CountRA { count: 0 },
    };
    let tracked (owner, reader) = all.split(empty, ticket);
    let tracked invalid = SharedTicket::Protocol::consume_with_shared(owner, &reader);
}

} // verus!
fn main() {}
