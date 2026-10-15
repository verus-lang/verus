// EXPECTED-ERROR: E0277
use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::cell::*;
use vstd::imap::*;
use vstd::multiset::*;
use vstd::prelude::*;
verus! {

pub ghost struct Snapshot<T> {
    pub opt: Option<T>,
    pub map: IMap<int, T>,
    pub mset: Multiset<T>,
    pub stored: IMap<int, T>,
}

} // verus!
verified_tokenized_state_machine! {

    #[verified_local_ready(withdraw_entry)]
    Payload<T> {
        fields {
            #[sharding(variable)] pub auth:Snapshot<T>,
            #[sharding(option)] pub opt:Option<T>,
            #[sharding(imap)] pub map:IMap<int,T>,
            #[sharding(multiset)] pub mset:Multiset<T>,
            #[sharding(storage_imap)] pub stored:IMap<int,T>,
        }
        #[invariant] pub fn exact(self)->bool {
            self.auth.opt==self.opt&&self.auth.map==self.map&&self.auth.mset==self.mset
                &&self.auth.stored==self.stored&&self.auth.map==self.auth.stored
        }
        init! { initialize(initial:Snapshot<T>) {
            require initial.map==initial.stored;
            init auth=initial;init opt=initial.opt;init map=initial.map;
            init mset=initial.mset;init stored=initial.stored;
        } }
        transition! { withdraw_entry(key:int) {
            require pre.auth.map.contains_key(key);
            remove map -= (IMap::<int,T>::empty().insert(key,pre.auth.map[key]));
            withdraw stored -= (IMap::<int,T>::empty().insert(key,pre.auth.stored[key]));
            update auth=Snapshot {map:pre.auth.map.remove(key),stored:pre.auth.stored.remove(key),..pre.auth};
        } }
        #[inductive(initialize)] fn initialize_inductive(post:Self,initial:Snapshot<T>) {}
        #[inductive(withdraw_entry)] fn withdraw_entry_inductive(pre:Self,post:Self,key:int) {
            assert(post.map =~= pre.map.remove(key));
            assert(post.stored =~= pre.stored.remove(key));
        }
    }
}
fn require_trait<X: Sync>() {}
fn main() {
    require_trait::<Payload::map_collection<std::cell::RefCell<u8>>>();
}
