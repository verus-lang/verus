// EXPECTED-ERROR: precondition not satisfied
//! The original Fancy transition requests the out-of-domain key m.
#[path = "../maps.rs"]
mod models;
use models::*;
use vstd::prelude::*;
use vstd::resource::tsm::Machine;
verus! {

proof fn original_withdraw_cannot_run() {
    let tracked token = Fancy::Protocol::initialize(IMap::tracked_empty(), false);
    let initial = choose|state: Fancy::State|
        Fancy::State::initialize(state, false) && state.invariant() && token.fragment()
            == Fancy::Protocol::embed(state);
    let tracked mut deposit = IMap::tracked_empty();
    deposit.tracked_insert(0int, true);
    fancy_deposit_ready(token.fragment(), 0int, deposit, true);
    let tracked token = Fancy::Protocol::do_deposit(token, deposit, true);
    let tracked (token, withdrawn) = Fancy::Protocol::do_withdraw(token, true);
}

fn main() {
}

} // verus!
