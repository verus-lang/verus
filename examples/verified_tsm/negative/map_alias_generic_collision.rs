// EXPECTED-ERROR: map collection alias conflicts with a field or generic type
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
verus! {

verified_tokenized_state_machine! {  X<m_map> { fields { #[sharding(imap)] pub m: IMap<int,m_map>, } } }

fn main() {
}

} // verus!
