#![allow(unused_imports)]
use builtin::*;
use builtin_macros::*;
mod pervasive;
use pervasive::*;
use crate::pervasive::{atomic_ghost::*};
use crate::pervasive::option::*;
use crate::pervasive::result::*;

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

#[verus::verifier(returns(proof))]
fn take<T>(lock: &Lock<T>) -> T {
    requires(lock.well_formed());

    loop {
        invariant(lock.well_formed());

        #[proof] let ghost_value: Option<T>;

        let result = atomic_with_ghost!(
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
            return match ghost_value {
                Option::Some(s) => s,
                _ => { proof_from_false() },
            };
        }
    }
}

struct VEqualG { }
impl AtomicInvariantPredicate<(), u64, u64> for VEqualG {
    #[spec] fn atomic_inv(k: (), v: u64, g: u64) -> bool {
        v == g
    }
}

pub fn main() {
    let ato = AtomicU64::<(), u64, VEqualG>::new((), 10, 10);

    // one macro to rule them all, with operation specified in the token stream?

    // fetch_or(ato, 19);
    // ato.fetch_or(19)
    // ato ~ fetch_or(19)

    atomic_with_ghost!(ato => fetch_or(19); ghost g => {
        g = g | 19;
    });

    atomic_with_ghost!(ato => fetch_or(23); update old_val -> new_val; ghost g => {
        assert(new_val == old_val | 23);
        assert(g == old_val);

        g = g | 23;

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

        g = if g == 20 { 25 } else { g };
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
        g = 36;
    });

    atomic_with_ghost!( ato => store(36);
        update old_val -> new_val;
        ghost g
    => {
        assert(old_val == g);
        assert(new_val == 36);
        g = 36;
    });

    atomic_with_ghost!( ato => store(36);
        ghost g
    => {
        g = 36;
    });




}
