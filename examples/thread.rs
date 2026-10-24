// rust_verify/tests/example.rs
#[allow(unused_imports)]
use verus_builtin::*;
#[allow(unused_imports)]
use verus_builtin_macros::*;
use vstd::prelude::*;
use vstd::thread::*;

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

fn test_scoped_threads_borrow_local_data() {
    let mut v: Vec<u64> = Vec::new();
    v.push(10);
    v.push(20);
    assert(v@ =~= seq![10u64, 20u64]);

    let sum = scope(
        |s| -> (r: u64)
            requires
                v@ == seq![10u64, 20u64],
            ensures
                r == 30,
            {
                // Both scoped threads borrow `v`, which is not 'static.
                let h1 = s.spawn(
                    || -> (r: u64)
                        requires
                            v@ == seq![10u64, 20u64],
                        ensures
                            r == 10,
                        { v[0] },
                );
                let h2 = s.spawn(
                    || -> (r: u64)
                        requires
                            v@ == seq![10u64, 20u64],
                        ensures
                            r == 20,
                        { v[1] },
                );

                let a = match h1.join() {
                    Result::Ok(a) => a,
                    Result::Err(_) => 10,
                };
                let b = match h2.join() {
                    Result::Ok(b) => b,
                    Result::Err(_) => 20,
                };
                a + b
            },
    );
    assert(sum == 30);

    // `v` is usable again once the scope ends.
    v.push(30);
}

} // verus!
fn main() {}
