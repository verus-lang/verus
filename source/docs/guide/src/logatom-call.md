# Atomic function call

To call a logically atomic function, we use the following syntax:

```rs
let py = function(px) atomically loop |update| {
    // ...
    // assert atomic pre
    let ay = update(ax);
    // assume atomic post
    // ...
    break/continue
}
```

The atomic function call binds an `update` function, which represents the effects of the `try_open_atomic_update` macro to the client.
It is helpful to think of the macro as defining the `update` function, as their inputs and outputs, as well as their pre- and postcondition match precisely.
The `update` function is `proof`-mode, allowing atomic invariants to be opened around it.

Since the library function may open the atomic update multiple times, due to aborting, the client must prove that it can provide the required resources as many times as necessary, meaning the atomic function call must be a loop.

If the atomic update is committed by the library, as indicated by the `UpdateTry` implementation on the output type, the client must `break` out of the loop.
Similarly, if the library aborts the atomic update, the loop must `continue`, either explicitly or implicitly.

In cases where this aborting mechanism is not necessary (e.g. if the output type of the atomic update is `Commit<T>`), **the `loop` keyword can be removed** to disable this feature.
This is equivalent to adding a `break` to the end of the `atomically` block, except it provides slightly better proof automation and eliminates the need to loop invariants in straight line code.

## Running examples

This is how we can call our two example functions *synchronously*, meaning we have full ownership of the permission object:

```rs
let (var, Tracked(mut perm)) = PAtomicU64::new(3);

reset(&var) atomically |update| {
    perm = update(perm)
};

assert(perm.is_for(var));
assert(perm.points_to(0));
```

```rs
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
```

Here are two simple *asynchronous* clients for our example functions, where we call the functions using an atomic invariant, allowing multiple threads to use these functions concurrently.
The invariant we use in this example makes no statement about the value of the atomic, we simply assert that `perm.is_for(var)`.

```rs
let Tracked(mut credit) = vstd::invariant::create_open_invariant_credit();

reset(&var) atomically |update| {
    open_atomic_invariant!(credit => &inv => perm => {
        perm = update(perm);
    });
};
```

```rs
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
```
