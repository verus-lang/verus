use verus_state_machines_macros::verified_tokenized_state_machine;
use vstd::cell::{PCell, PointsTo};
use vstd::prelude::*;
verified_tokenized_state_machine! {  Physical {
 fields {
 #[sharding(variable)] pub key:PointsTo<u64>,
 #[sharding(count)] pub caps:nat,
 #[sharding(storage_map)] pub data:Map<nat,PointsTo<u64>>,
 #[sharding(storage_option)] pub spare:Option<PointsTo<u64>>,
 }
 #[invariant] pub fn valid(&self)->bool { self.caps<=1 && (self.caps==1 ==> self.data.contains_key(0) && self.data[0]==self.key) }
 init! { new(contents:Map<nat,PointsTo<u64>>, initial:PointsTo<u64>, reserve:Option<PointsTo<u64>>) {
 require contents.contains_key(0); require contents[0]==initial; init key=initial;init caps=1;init data=contents;init spare=reserve;
 } }
 #[inductive(new)] fn new_inductive(post:Self,contents:Map<nat,PointsTo<u64>>,initial:PointsTo<u64>,reserve:Option<PointsTo<u64>>) {}
 transition! { take() { require(pre.key==pre.key); remove caps-=(1); withdraw data-=[0=>let p]; assert(p==pre.key); } }
 #[inductive(take)] fn take_inductive(pre:Self,post:Self) {}
}}
verus! {

fn main() {
    let (cell, Tracked(p)) = PCell::new(7u64);
    let tracked mut map: Map<nat, PointsTo<u64>>;
    proof {
        map = Map::tracked_empty();
        map.tracked_insert(0, p);
    }
    let tracked inst;
    let tracked key;
    let tracked caps;
    proof {
        let initial = map;
        let tracked (Tracked(i), Tracked(k), Tracked(c)) = Physical::Instance::new(
            initial,
            p,
            None,
            map,
            None,
        );
        inst = i;
        key = k;
        caps = c;
    }
    let tracked mut permission;
    proof {
        permission = inst.take(&key, caps);
    }
    let value = cell.take(Tracked(&mut permission));
    assert(value == 7);
}

} // verus!
