#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;
use vstd::{prelude::*, thread::*};

verus_old_todo_no_ghost_blocks!{

fn test_calling_thread_id_twice_same_value() {
    let (tid1, is1) = thread_id();
    let (tid2, is2) = thread_id();

    proof {
        #[verifier::proof] let is1 = is1.get();
        #[verifier::proof] let is2 = is2.get();

        is1.agrees(is2);
    }

    assert(tid1 == tid2);
}

fn test_calling_thread_id_twice_diff_threads() {
    let (tid1, is1) = thread_id();

    spawn(move || {
        let (tid2, is2) = thread_id();

        // This isn't allowed: Send error
        /*proof {
            #[proof] let is1 = is1.get();
            #[proof] let is2 = is2.get();

            is1.agrees(is2);
        }*/
    });
}

}

fn main() { }
