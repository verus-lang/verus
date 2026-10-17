// EXPECTED-ERROR: verified option/map/multiset replacement must remove then add on each modifying path
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
verus! {

verified_tokenized_state_machine!(
    #[verified_raw_tokens]
WrongOrder {
    fields { #[sharding(imap)] pub entries: IMap<int, bool>, }
    init! { initialize() { init entries = IMap::empty(); } }
    transition! { wrong(key: int) {
        add entries += [key => true];
        remove entries -= [key => true];
    } }
    #[inductive(initialize)] fn initialize_inductive(post: Self) {}
    #[inductive(wrong)] fn wrong_inductive(pre: Self, post: Self, key: int) {}
});

} // verus!
fn main() {}
