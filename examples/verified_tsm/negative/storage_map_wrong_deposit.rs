// EXPECTED-ERROR: precondition not satisfied
//! The actual tracked deposit must match the protocol's key and value.
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
verus! {

verified_tokenized_state_machine! {
    #[verified_raw_tokens]

    WrongDeposit {
        fields {
            #[sharding(variable)] pub full:bool,
            #[sharding(storage_imap)] pub stored:IMap<nat,nat>,
        }
        #[invariant] pub fn contents(&self)->bool {
            self.stored==if self.full{IMap::empty().insert(0nat,42nat)}else{IMap::empty()}
        }
        init! {initialize(){init full=false;init stored=IMap::empty();}}
        transition! {put(){require !pre.full;deposit stored +=[0nat=>42nat];update full=true;}}
        #[inductive(initialize)] fn initialize_inductive(post:Self){}
        #[inductive(put)] fn put_inductive(pre:Self,post:Self){}
    }
}

pub proof fn rejected() {
    let tracked base = IMap::tracked_empty();
    let tracked token = WrongDeposit::Protocol::initialize(base);
    let tracked mut deposit = IMap::tracked_empty();
    deposit.tracked_insert(1nat, 42nat);
    let tracked _token = WrongDeposit::Protocol::put(token, deposit);
}

} // verus!
fn main() {}
