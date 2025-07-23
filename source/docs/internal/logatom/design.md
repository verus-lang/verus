# Logical Atomicity
*Aaron Bies, Travis Hance, Derek Dreyer*

## Motivating Example

```rs
use std::sync::atomic::AtomicU32;
use std::sync::atomic::Ordering::Relaxed;

pub fn increment_bad(var: &AtomicU32) {
    let curr = var.load(Relaxed);
    var.store(curr + 1, Relaxed);
}

pub fn increment_good(var: &AtomicU32) {
    let mut curr = var.load(Relaxed);
    while let Err(new) = var.compare_exchange_weak(curr, curr + 1, Relaxed, Relaxed) {
        curr = new;
    }
}
```
Both functions satisfy the same naive specification:
$$
\{ v \mapsto n \}\;\;{\tt increment}(v)\;\;\{ v \mapsto n + 1 \}
$$

## Resources/Related Work

Some of the constructs needed for this project already exist in verus/vstd:

- [`vstd::invariant`](https://verus-lang.github.io/verus/verusdoc/vstd/invariant/index.html)
    - [`AtomicInvariant`](https://verus-lang.github.io/verus/verusdoc/vstd/invariant/struct.AtomicInvariant.html)
    - [`InvariantPredicate`](https://verus-lang.github.io/verus/verusdoc/vstd/invariant/trait.InvariantPredicate.html)
    - [`open_atomic_invariant`](https://verus-lang.github.io/verus/verusdoc/vstd/macro.open_atomic_invariant.html)
- [`vstd::atomic`](https://verus-lang.github.io/verus/verusdoc/vstd/atomic/index.html)
    - [`PAtomicU32`](https://verus-lang.github.io/verus/verusdoc/vstd/atomic/struct.PAtomicU32.html)
    - [`PermissionU32`](https://verus-lang.github.io/verus/verusdoc/vstd/atomic/struct.PermissionU32.html)

## Atomic pre- and post-conditions

To define a function with an atomic pre- and post-condition, we use the following syntax:

```rs
fn function(args) -> ret_ty
    atomic_spec (au_binding) {
        (old_perm_binding: X) -> (new_perm_binding: Y),
        requires pre_condition,
        ensures post_condition,
    }
    requires pre_condition,
    ensures post_condition,
{
    ..;
}
```

The atomic pre- and post-condition, specified in the `atomic_spec` block, desugars to an additional *tracked* function argument `au_binding: AtomicUpdate`, defined analogously to [`vstd::invariant::AtomicInvariant`](https://verus-lang.github.io/verus/verusdoc/vstd/invariant/struct.AtomicInvariant.html):

```rs
pub struct AtomicUpdate<X, Y, Pred> { ... }
```

Since opening an `AtomicUpdate` requires ownership and consumes the update, the type is `Send` and `Sync`, and there is no masking system like there is for invariants.

Here, the `Pred` type must implement the `UpdatePredicate` trait, which is defined as follows:

```rs
pub trait UpdatePredicate<X, Y> {
    spec fn req(x: X) -> bool;
    spec fn ens(x: X, y: Y) -> bool;
}
```

The values `x: X` and `y: Y` are the permissions immediately before and after the atomic update respectively, `req` and `ens` correspond to the predicates in the atomic `requires` and `ensures` clauses.

### Design Questions

- Should we use `perm` and `old(perm)` instead of `old_perm_binding` and `new_perm_binding`?

- Should we rename `atomic_spec` to `atomically` to reduce the number of new keywords?

## Open atomic update

To call a function with an atomic pre- and post-condition, we use the following syntax:

```rs
function(args) atomically |update| {
    open_atomic_update!(atomic_update => old_perm => {
        // assume atomic pre `atomic_update`
        // ...
        // assert atomic pre `function`
        let new_perm = update(old_perm);
        // assume atomic post `function`
        // ...
        // assert atomic post `atomic_update`
        new_perm
    });
}
```

Here, `update` is an uninterpreted function that takes ownership of `old_perm` and produces `new_perm`.
This function must be called exactly once within the `atomically |update| { ... }` block.

It has the atomic pre- and post-conditions of the function we're calling as its (private) pre- and post-conditions.
Since the function is uninterpreted, it is up to the post-condition the uniquely determine the value of `new_pred`, otherwise the value is non-deterministic.

The `open_atomic_update` macro takes an atomic update `atomic_update` as an argument and binds `old_perm` as a new variable.

### Design Questions

- Is an `atomically` block "just" the constructor for the `AtomicUpdate` type?

    ```rs
    let tracked au: AtomicUpdate<X, Y, Pred> = atomically |update| { ... };
    tunction(args, au);
    ```

    In this case, we could use `atomically` and `open_atomic_update` to "map" one `AtomicUpdate` into another:

    ```rs
    impl <X, Y, P: UpdatePredicate<X, Y>> AtomicUpdate<X, Y, P> {
        pub fn map<A, B, Q: UpdatePredicate<X, Y>>(
            self,
            lem1: impl ProofFn(A) -> X,
            lem2: impl ProofFn(Y) -> B,
        ) -> AtomicUpdate<A, B, Q> {
            atomically |update| {
                open_atomic_update!(self => perm => {
                    let perm = lem1(perm);
                    let perm = update(perm);
                    let perm = lem2(perm);
                    return perm;
                });
            }
        }
    }
    ```

## Open atomic invariant

```rs
function(args) atomically |update| {
    open_atomic_invariant!(inv => perm => {
        // ...
        now(&mut perm);       // original syntax
        perm = update(perm);  // proposed syntax
        // ...
    });
}
```

The `open_atomic_invariant` macro is already implemented in vstd, and the `atomically` block has precisely the same syntax and semantics as in the previous section, so this example is boring (which is great).

## Provide full permissions

```rs
function(args) with (&mut perm);        // original syntax
function(args) atomically (&mut perm);  // proposed syntax
```

This is a shorthand for the special case that we have full permission for the atomic we want to access.
It is equivalent to the following:

```rs
function(args) atomically |update| { perm = update(perm); };
```

### Design Question:
- Do we really need this?
- Should we allow the user to construct an `AtomicUpdate` object directly from a premission?
