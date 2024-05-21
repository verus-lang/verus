#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
use vstd::atomic_ghost::*;
use vstd::prelude::*;
use vstd::{pervasive::*, *};

verus! {

struct_with_invariants!{
    struct Lock<T> {
        field: AtomicBool<_, Option<T>, _>,
    }

    spec fn well_formed(&self) -> bool {
        invariant on field with () is (b: bool, t: Option<T>) {
            b === t.is_Some()
        }
    }
}

fn take<T>(lock: &Lock<T>) -> (t: Tracked<T>)
    requires
        lock.well_formed(),
{
    loop
        invariant
            lock.well_formed(),
    {
        let tracked ghost_value: Option<T>;
        let result =
            atomic_with_ghost!(
            &lock.field => compare_exchange(true, false);
            update prev -> next;
            ghost g => {
                if prev == true {
                    ghost_value = g;
                    g = Option::None;
                } else {
                    ghost_value = Option::None;
                }
            }
        );
        if let Result::Ok(_) = result {
            return Tracked(
                match ghost_value {
                    Option::Some(s) => s,
                    _ => { proof_from_false() },
                },
            );
        }
    }
}

struct VEqualG {}

impl AtomicInvariantPredicate<(), u64, u64> for VEqualG {
    closed spec fn atomic_inv(k: (), v: u64, g: u64) -> bool {
        v == g
    }
}

proof fn proof_int(x: u64) -> (tracked y: u64)
    ensures
        x == y,
{
    assume(false);
    proof_from_false()
}

pub fn main() {
    // TODO Tracked of int-literal is currently unsupported.
    // Should support it, or rewrite this example
    /*
    let ato = AtomicU64::<(), u64, VEqualG>::new(Ghost(()), 10, Tracked(10));

    // illustration of atomic_with_ghost!

    atomic_with_ghost!(ato => fetch_or(19); ghost g => {
        g = proof_int(g | 19);
    });

    atomic_with_ghost!(ato => fetch_or(23); update old_val -> new_val; ghost g => {
        assert(new_val == old_val | 23);
        assert(g == old_val);

        g = proof_int(g | 23);

        assert(g == new_val);
    });

    let res = atomic_with_ghost!(
        ato => compare_exchange(20, 25);
        update old_val -> new_val;
        returning ret;
        ghost g
    => {
        assert(imply(ret.is_Ok(), old_val == 20 && new_val == 25));
        assert(imply(ret.is_Err(), old_val != 20 && new_val == old_val
            && ret.get_Err_0() == old_val));

        g = if g == 20 { proof_int(25) } else { g };
    });

    let res = atomic_with_ghost!( ato => load();
        returning ret;
        ghost g
    => {
        assert(ret == g);
    });

    atomic_with_ghost!( ato => store(36);
        update old_val -> new_val;
        ghost g
    => {
        assert(old_val == g);
        assert(new_val == 36);
        g = proof_int(36);
    });

    atomic_with_ghost!( ato => store(36);
        update old_val -> new_val;
        ghost g
    => {
        assert(old_val == g);
        assert(new_val == 36);
        g = proof_int(36);
    });

    atomic_with_ghost!( ato => store(36);
        ghost g
    => {
        g = proof_int(36);
    });
    */
}

} // verus!
