# Opening atomic updates

To open the atomic update, we use the `try_open_atomic_update` macro as follows:

```rs
let res_au = try_open_atomic_update!(au, ax => {
    // assume atomic pre
    // ...
    // assert atomic post
    Tracked(ay)
})
```

When we open the atomic update, we are given the input `ax: AX` and learn the atomic precondition, and at the end of the macro call, we return the output `ay: AY` and prove the atomic postcondition.

The macro outputs a value of type `Tracked<Result<(), AtomicUpdate<AX, AY, PredType>>>`.
If the atomic update is committed, as indicated by the `UpdateTry` trait, then the atomic update is consumed and we get `Ok(())`.
Otherwise, if the atomic update is aborted, we get back the same atomic update we put in `Err(au)`, allowing us to open it again later.

When the atomic update is opened and committed, it is marked as resolved, meaning the value of `au.resolves()` becomes `true`.
We must prove that the atomic update has resolved by the end of the logically atomic function.

To open the atomic update, `au.outer_mask()` must be valid in the current scope.
Inside the body of the `try_open_atomic_update` macro, `au.inner_mask()` becomes the new invariant mask.

## Running examples

Here are the full definitions of our two example functions:

```rs
pub fn reset(var: &PAtomicU64)
    atomically (atomic_update) {
        (perm: PermissionU64) -> (commit: Commit<PermissionU64>),
        requires
            perm@.patomic == var.id(),
        ensures
            commit@.patomic == perm@.patomic
            commit@.value == 0
        outer_mask any,
        inner_mask none,
    },
{
    let tracked au = atomic_update;

    // open atomic update and commit
    try_open_atomic_update!(au, perm => {
        var.store(Tracked(&mut perm), 0);
        Tracked(Commit(perm))
    });

    // verify that the atomic update had been resolved
    assert(au.resolves());
}
```

```rs
pub fn increment(var: &PAtomicU64) -> (out: u64)
    atomically (atomic_update) {
        (perm: PermissionU64)
            -> (res: Result<PermissionU64, (PermissionU64, OpenInvariantCredit)>),
        requires
            perm@.patomic == var.id(),
        ensures match res {
            Err((p, _)) => p@ == perm@,
            Ok(p) => {
                &&& p@.patomic == perm@.patomic
                &&& p@.value == perm@.value.wrapping_add(1)
            }
        },
        outer_mask any,
        inner_mask none,
    },
    ensures
        out == perm@.value,
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
```
