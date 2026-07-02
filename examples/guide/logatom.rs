#![verifier::exec_allows_no_decreases_clause]
#![verifier::loop_isolation(false)]

use vstd::atomic::*;
use vstd::invariant::*;
use vstd::prelude::*;

verus! {

struct UserInv;
impl InvariantPredicate<int, PermissionU64> for UserInv {
    open spec fn inv(id: int, perm: PermissionU64) -> bool {
        &&& perm.id() == id
    }
}



// ANCHOR: reset_definition
// ANCHOR: reset_signature_1
fn reset(var: &PAtomicU64)
    atomically (atomic_update) {
        (perm: PermissionU64) -> (commit: Commit<PermissionU64>),
// ANCHOR_END: reset_signature_1
// ANCHOR: reset_signature_2
        requires
            perm@.patomic == var.id(),
// ANCHOR_END: reset_signature_2
// ANCHOR: reset_signature_3
        ensures
            commit@@.patomic == perm@.patomic,
            commit@@.value == 0,
// ANCHOR_END: reset_signature_3
// ANCHOR: reset_signature_4
        outer_mask any,
        inner_mask none,
    },
// ANCHOR_END: reset_signature_4
{
    // open atomic update and commit
    try_open_atomic_update!(atomic_update, mut perm => {
        var.store(Tracked(&mut perm), 0);
        Tracked(Commit(perm))
    });

    // verify that the atomic update had been resolved
    assert(atomic_update.resolves());
}
// ANCHOR_END: reset_definition



fn reset_client_sync() {
// ANCHOR: reset_client_sync
let (var, Tracked(mut perm)) = PAtomicU64::new(3);

reset(&var) atomically |update| {
    perm = Commit::get(update(perm));
};

assert(perm.is_for(var));
assert(perm.points_to(0));
// ANCHOR_END: reset_client_sync
}



fn reset_client_async() {
    let (var, Tracked(perm)) = PAtomicU64::new(6);
    let tracked inv = AtomicInvariant::<int, PermissionU64, UserInv>::new(
        perm.id(), perm, 235
    );

// ANCHOR: reset_client_async
let Tracked(mut credit) = vstd::invariant::create_open_invariant_credit();

reset(&var) atomically |update| {
    open_atomic_invariant!(credit => &inv => perm => {
        perm = Commit::get(update(perm));
    });
};
// ANCHOR_END: reset_client_async
}



// ANCHOR: increment_definition
// ANCHOR: increment_signature_1
fn increment(var: &PAtomicU64) -> (out: u64)
    atomically (atomic_update) {
        (perm: PermissionU64)
            -> (res: Result<PermissionU64, (PermissionU64, OpenInvariantCredit)>),
// ANCHOR_END: increment_signature_1
// ANCHOR: increment_signature_2
        requires
            perm@.patomic == var.id(),
// ANCHOR_END: increment_signature_2
// ANCHOR: increment_signature_3
        ensures match res {
            Err((p, _)) => p@ == perm@,
            Ok(p) => p@.patomic == perm@.patomic
                  && p@.value == perm@.value.wrapping_add(1),
        },
// ANCHOR_END: increment_signature_3
// ANCHOR: increment_signature_4
        outer_mask any,
        inner_mask none,
    },
// ANCHOR_END: increment_signature_4
// ANCHOR: increment_signature_5
    ensures
        out == perm@.value,
// ANCHOR_END: increment_signature_5
{
    let Tracked(credit) = vstd::invariant::create_open_invariant_credit();
    let tracked mut au = atomic_update;
    let mut curr;

    // open atomic update and abort for inital load
    let wrapped_au = try_open_atomic_update!(au, perm => {
        curr = var.load(Tracked(&perm));
        Tracked(Err((perm, credit)))
    });

    // recover `au` from the returned `Tracked(Err(au))`
    proof { au = wrapped_au.get().tracked_unwrap_err() };

    // compare exchange loop
    loop invariant au == atomic_update {
        let Tracked(credit) = vstd::invariant::create_open_invariant_credit();
        let next = curr.wrapping_add(1);
        let res;

        // open atomic update again
        let maybe_au = try_open_atomic_update!(au, mut perm => {
            res = var.compare_exchange_weak(Tracked(&mut perm), curr, next);

            // dynamically commit or abort atomic update
            // depending on `compare_exchange_weak`
            Tracked(match res {
                Ok(_) => Ok(perm),
                Err(_) => Err((perm, credit)),
            })
        });

        match res {
            Ok(_) => return curr,
            Err(new) => {
                proof { au = maybe_au.get().tracked_unwrap_err() };
                curr = new;
            },
        }
    }
}
// ANCHOR_END: increment_definition



fn increment_client_sync() {
// ANCHOR: increment_client_sync
let (var, Tracked(mut perm)) = PAtomicU64::new(3);

let prev = increment(&var) atomically loop |update|
    invariant
        perm.is_for(var),
        perm.points_to(3),
{
    match update(perm) {
        Err((p, _)) => perm = p,
        Ok(p) => { perm = p; break }
    }
};

assert(prev == 3);
assert(perm.is_for(var));
assert(perm.points_to(4));
// ANCHOR_END: increment_client_sync
}



fn increment_client_async() {
    let (var, Tracked(perm)) = PAtomicU64::new(6);
    let tracked inv = AtomicInvariant::<int, PermissionU64, UserInv>::new(
        perm.id(), perm, 235
    );

// ANCHOR: increment_client_async
let Tracked(mut credit) = vstd::invariant::create_open_invariant_credit();

increment(&var) atomically loop |update| {
    let tracked mut spare = None;
    open_atomic_invariant!(credit => &inv => perm => {
        let tracked res = update(perm);
        match res {
            Ok(p) => perm = p,
            Err((p, c)) => {
                perm = p;
                spare = Some(c);
            }
        }
    });

    match spare {
        None => break,
        Some(c) => credit = c,
    }
};
// ANCHOR_END: increment_client_async
}

}
