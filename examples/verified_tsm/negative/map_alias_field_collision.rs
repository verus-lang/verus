// EXPECTED-ERROR: map collection alias conflicts with a field or generic type
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
verus! {

verified_tokenized_state_machine! {  X { fields { #[sharding(imap)] pub m: IMap<int,int>, #[sharding(variable)] pub m_map: int, } } }

fn main() {
}

} // verus!
