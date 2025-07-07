use vstd::prelude::*;

verus! {

fn add_1(v: u64) -> (r: u64)
    // requires v + 1 <= u64::MAX
    // ensures r == v + 1
{
    // assume PRE
    /* (internal) */ assume(v + 1 <= u64::MAX);
    let r = v + 1;
    // assert POST
    /* (internal) */ assert(r == v + 1);
    r
}

fn main() {
    let x = 4;

    // assert PRE of add_1
    /* (internal) */ assert(4 + 1 <= u64::MAX);
    let y = add_1(4);
    // assume POST of add_1
    /* (internal) */ assume(y == 4 + 1);
    
    assert(y == 5);
}

tracked struct VV {
    v1: nat,
    v2: nat,
}

#[verifier::external_body]
proof fn new_vv() -> VV { unreached() }

proof fn example(v: VV)
    // requires v == VV { v1: 3, v2: 4 }
{
    let mut v = v;

    /* (internal) */ assume(v == VV { v1: 3, v2: 4 });

    assert(v.v1 == 3);
    assert(v.v2 == 4);
    
    // change v1 to 6
    // keep v2 to the same value
    let ghost old_v = v;
    v = new_vv(); // havoc(v): forget everything about a variable because it's being mutated
    assume(v.v1 == 6);
    assume(v.v2 == old_v.v2);

    assert(v.v1 == 6);
    assert(v.v2 == 4);
    
}

}