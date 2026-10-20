// EXPECTED-ERROR: precondition not satisfied
//! Reading a storage operation's key needs an owned or shared observation.
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::prelude::*;
use vstd::resource::agree::AgreementRA;
use vstd::resource::algebra::ResourceAlgebra;
use vstd::resource::exclusive::ExclusiveRA;
use vstd::resource::pcm::PCM;
verus! {

verified_tokenized_state_machine! {
    #[verified_raw_tokens]

    KeyRead {
        fields {
            #[sharding(constant)] pub key:nat,
            #[sharding(variable)] pub full:bool,
            #[sharding(storage_imap)] pub stored:IMap<nat,nat>,
        }
        #[invariant] pub fn contents(&self)->bool {
            self.stored==if self.full{IMap::empty().insert(self.key,42nat)}else{IMap::empty()}
        }
        init! {initialize(){init key=0;init full=true;init stored=IMap::empty().insert(0nat,42nat);}}
        transition! {take(){require pre.full;withdraw stored -=[pre.key=>let p];update full=false;}}
        #[inductive(initialize)] fn initialize_inductive(post:Self){}
        #[inductive(take)] fn take_inductive(pre:Self,post:Self){
            assert(post.stored =~= IMap::empty());
        }
    }
}

pub proof fn rejected() {
    let tracked mut base = IMap::tracked_empty();
    base.tracked_insert(KeyRead::__StorageKey::stored(0nat), KeyRead::__StorageValue::stored(42nat));
    assert(base =~= KeyRead::__tag_stored(IMap::empty().insert(0nat, 42nat)));
    let tracked token = KeyRead::Protocol::initialize(base);
    let owned = KeyRead::Fragment { key: None, full: Some(ExclusiveRA::Exclusive(true)) };
    let key = KeyRead::Fragment { key: Some(AgreementRA::Agree(0nat)), full: None };
    let tracked (owned, key) = token.split(owned, key);
    let tracked _out = KeyRead::Protocol::take(owned);
}

} // verus!
fn main() {}
