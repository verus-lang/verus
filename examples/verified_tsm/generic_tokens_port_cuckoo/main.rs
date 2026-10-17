#![verifier::loop_isolation(false)]

use vstd::prelude::*;

verus!{

pub mod cuckoo;

use cuckoo::*;

#[verifier::external_body]
fn print(x: Option<u64>) {
    println!("{x:?}");
}

#[verifier::external_body]
fn runtime_assert(b: bool)
    ensures b
{
    assert!(b);
}

fn main() {
    let (hm, Tracked(mut pt_map)) = cuckoo::MyHashMap::new();

    let tracked pt1 = Some(pt_map.remove(1));
    let tracked pt2 = Some(pt_map.remove(2));
    let tracked pt3 = Some(pt_map.remove(3));

    let tracked pt1_a: Option<MPointsTo> = None;
    let r = hm.read(1) atomically |upd| -> ReadAU {
        pt1_a = Some(upd(pt1.tracked_take()).get());
    };

    let tracked pt1 = pt1_a;
    assert(r === None);
    print(r);

    let tracked pt1_a: Option<MPointsTo> = None;
    let success = hm.insert(1, 17) atomically |upd| -> InsertAU {
        pt1_a = Some(upd(pt1.tracked_take()).get());
    };

    let tracked pt1 = pt1_a;

    runtime_assert(success);

    let r = hm.read(1) atomically |upd| -> ReadAU {
        pt1 = Some(upd(pt1.tracked_take()).get());
    };

    assert(r === Some(17));
    print(r);

    let tracked pt1_a: Option<MPointsTo> = None;
    let success = hm.delete(1) atomically |upd| -> DeleteAU {
        pt1_a = Some(upd(pt1.tracked_take()).get());
    };

    let tracked pt1 = pt1_a;

    let r = hm.read(1) atomically |upd| -> ReadAU {
        pt1 = Some(upd(pt1.tracked_take()).get());
    };

    assert(r === None);
    print(r);
}

}
