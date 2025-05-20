use vstd::prelude::*;
use vstd::atomic::*;
use vstd::simple_pptr::*;
use vstd::invariant::*;

verus! {

enum Counter {
    Inactive(u32),
    Active(u32),
}

struct CCounter {
    flag: AtomicBool,
    counter: AtomicCounter,
}

fn cinc(


}
