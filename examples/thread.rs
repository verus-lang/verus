#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;
use vstd::{prelude::*, thread::*};

verus! {

fn test_calling_thread_id_twice_same_value() {
    let (tid1, Tracked(is1)) = thread_id();
    let (tid2, Tracked(is2)) = thread_id();
    proof {
        is1.agrees(is2);
    }
    assert(tid1 == tid2);
}

fn test_calling_thread_id_twice_diff_threads() {
    let (tid1, Tracked(is1)) = thread_id();
    spawn(
        move ||
            {
                let (tid2, Tracked(is2)) = thread_id();
                // This isn't allowed: Send error
                /*proof {
            is1.agrees(is2);
        }*/
            },
    );
}

} // verus!
fn main() {}
