// EXPECTED-ERROR: map collection alias conflicts with a field or generic type
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
verus! {

verified_tokenized_state_machine! {  X<r#m_map> { fields { #[sharding(imap)] pub m: IMap<int,r#m_map>, } } }

fn main() {
}

} // verus!
