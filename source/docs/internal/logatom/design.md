# Logical Atomicity
*Aaron Bies, Travis Hance, Derek Dreyer*

## Motivating Example

Here are two simple functions that increment an atomic variable.

```rs
use std::sync::atomic::{AtomicU32, Ordering::SeqCst};

pub fn increment_bad(var: &AtomicU32) {
    let curr = var.load(SeqCst);
    var.store(curr + 1, SeqCst);
}

pub fn increment_good(var: &AtomicU32) {
    let mut curr = var.load(SeqCst);
    loop {
        match var.compare_exchange_weak(curr, curr + 1, SeqCst, SeqCst) {
            Ok(_) => break,
            Err(new) => curr = new,
        }
    }
}
```

In a single-threaded context, both functions are equivalent and work as expected.

However, in a multi-threaded context, `increment_bad` can lead to a data race, whereas `increment_good` is guaranteed to increment the variable exactly once.

### Current State of Verus

The `vstd::atomic` provides wrapper types around atomic integers (e.g. [`PAtomicU32`](https://verus-lang.github.io/verus/verusdoc/vstd/atomic/struct.PAtomicU32.html)), where access to the atomics is guarded by a tracked permission type (e.g. [`PermissionU32`](https://verus-lang.github.io/verus/verusdoc/vstd/atomic/struct.PermissionU32.html)).

The `load`, `store` and `compare_exchange` operations have the following signatures (slighly simplified here):

```rs
fn load(&self, perm: Tracked<&PermissionU32>) -> u32
fn store(&self, perm: Tracked<&mut PermissionU32>, v: u32)
fn compare_exchange(&self, perm: Tracked<&mut PermissionU32>, old: u32, new: u32) -> Result<u32, u32>
```

So, to be able to load an atomic variable, we must provide proof that we have shared permission (`Tracked<&PermissionU32>`) to access the variable, and for store and compare-exchange, we must prove that we have exclusive permission (`Tracked<&mut PermissionU32>`) for the variable.

The current system allows us to prove that both functions work as expected if no other thread accesses the atomic variable.

## Resources/Related Work

We did not invent logical atomicity, here are some publications that talk about it:

- [Later Credits: Resourceful Reasoning for the Later Modality](https://plv.mpi-sws.org/later-credits/paper-later-credits.pdf)
- [The Future is Ours: Prophecy Variables in Separation Logic](https://plv.mpi-sws.org/prophecies/paper.pdf)
- [Iris: Monoids and Invariants as an Orthogonal Basis for Concurrent Reasoning](https://dl.acm.org/doi/10.1145/2676726.2676980)
- [Logical Atomicity in Iris: the Good, the Bad, and the Ugly](https://research.ralfj.de/iris/talk-iris2019.pdf)
- [TaDA: A Logic for Time and Data Abstraction](https://link.springer.com/chapter/10.1007/978-3-662-44202-9_9)

Some of the constructs needed for this project already exist in verus/vstd:

- [`vstd::invariant`](https://verus-lang.github.io/verus/verusdoc/vstd/invariant/index.html)
    - [`AtomicInvariant`](https://verus-lang.github.io/verus/verusdoc/vstd/invariant/struct.AtomicInvariant.html)
    - [`InvariantPredicate`](https://verus-lang.github.io/verus/verusdoc/vstd/invariant/trait.InvariantPredicate.html)
    - [`open_atomic_invariant`](https://verus-lang.github.io/verus/verusdoc/vstd/macro.open_atomic_invariant.html)
- [`vstd::atomic`](https://verus-lang.github.io/verus/verusdoc/vstd/atomic/index.html)
    - [`PAtomicU32`](https://verus-lang.github.io/verus/verusdoc/vstd/atomic/struct.PAtomicU32.html)
    - [`PermissionU32`](https://verus-lang.github.io/verus/verusdoc/vstd/atomic/struct.PermissionU32.html)

## The Atomic Update Type

The atomic update in encoded using a new type `AtomicUpdate`, defined analogously to [`vstd::invariant::AtomicInvariant`](https://verus-lang.github.io/verus/verusdoc/vstd/invariant/struct.AtomicInvariant.html):

```rs
pub struct AtomicUpdate<X, Y, Pred> {
    pred: Pred,
    _dummy: core::marker::PhantomData<fn(X) -> Y>,
}
```

Since the type contains `Pred` directly, `AtomicUpdate` is `Send` and `Sync` if and only if `Pred` is `Send` and `Sync` respectively.
It is contravariant in `X` and covariant in `Y` and `Pred`.

The atomic update does not have a namespace, but it has *two* masks, `mask_inner` and `mask_outer`, where:
- `mask_outer` specifies which invariants must me openable for the atomic update, and
- `mask_inner` specifies which invariants are opened around the update itself.

<details>
<summary>Mask Example</summary>

In the following example, `mask_outer` contains `inv1` and `inv2`, whereas `mask_inner` only contains `inv1`.

```rs
function(args) atomically |update| {
    open_atomic_invariant!(inv1 => perm => {
        // ...
        open_atomic_invariant!(inv2 => perm => {
            // ...
        });
        // ...
        perm = update(perm);
        // ...
    });
}
```
</details>

Here, the `Pred` type must implement the `UpdatePredicate` trait, which is defined as follows:

```rs
pub trait UpdatePredicate<X, Y> {
    spec fn req(x: X) -> bool;
    spec fn ens(x: X, y: Y) -> bool;
}
```

The values `x: X` and `y: Y` are the permissions immediately before and after the atomic update respectively, `req` and `ens` correspond to the predicates in the atomic `requires` and `ensures` clauses.

## Atomic pre- and post-conditions

To define a function with an atomic pre- and post-condition, we use the following syntax:

```rs
fn function(args: Args) -> (res: R)
    atomically (atomic_update) {
        (old_perm: OldPerm) -> (new_perm: NewPerm),
        requires atomic_pre_condition(args, old_perm),
        ensures atomic_post_condition(args, old_perm, new_perm),
    },
    requires pre_condition(args),
    ensures post_condition(args, res),
{
    ..;
}
```

The atomic pre- and post-condition, specified in the `atomic_spec` block, desugars to an additional *tracked* function argument `atomic_update: AtomicUpdate`, as follows:

```rs
struct FunctionPredicate {
    data: Args,
}

impl UpdatePredicate<OldPerm, NewPerm> for FunctionPred {
    spec fn req(self, old_perm: OldPerm) -> bool {
        let args = self.data;
        atomic_pre_condition(args, old_perm)
    }

    spec fn ens(self, old_perm: OldPerm, new_perm: NewPerm) -> bool {
        let args = self.data;
        atomic_post_condition(args, old_perm, new_perm)
    }
}

fn function(
    args: Args,
    tracked atomic_update: AtomicUpdate<OldPerm, NewPerm, FunctionPred>
) -> (res: R)
    requires pre_condition(args),
    ensures post_condition(args, res),
{
    assume(atomic_update.pred == Pred {args})
    // ...
}
```

### Design Questions

- We would like users to be able to use the automatically generated `FunctionPredicate` type directly. This means the name of the type either has to be exteremely predicatble and stable, or we allow users to specify the name themselves. What would be a good syntax for this? I'm thinking about adding an optional `as Ident` or `type Ident` somewhere to the atomically block.

## The Atomic Function Call

To call a function with an atomic pre- and post-condition, we use the following syntax:

```rs
function(args) atomically |update| {
    // ...
    // assert atomic pre `function`
    let new_perm = update(old_perm);
    // assume atomic post `function`
    // ...
}
```

Here, `update` is an uninterpreted function that takes ownership of `old_perm` and produces `new_perm`.
This function must be called exactly once within the `atomically |update| { ... }` block.

It has the atomic pre- and post-conditions of the function we're calling as its (private) pre- and post-conditions.
Since the function is uninterpreted, it is up to the post-condition the uniquely determine the value of `new_pred`, otherwise the value is non-deterministic.

For the desugaring, we have defined an auxilary function called `atomically` in the `vstd::atomic` module.
It has with the following definition:

```rs
#[doc(hidden)]
pub fn atomically<X, Y, P>(_f: impl FnOnce(fn(X) -> Y)) -> AtomicUpdate<X, Y, P> {
    arbitrary()
}
```

The desugaring done by the `verus!` macro looks like this:

```rs
function(args, ::vstd::atomic::atomically(move |update| {
    let _args = (args);
    // ...
    let new_perm = update(old_perm);
    // ...
}))
```

The generates VIR-SST looks roughtly like this:

```rs
function(args, {
    let ghost pred = FunctionPred { data: (args) };
    //
    // ...
    //
    let tracked x = old_perm;
    let tracked y = arbitrary();
    assert(UpdatePredicate::req(pred, x));
    assume(UpdatePredicate::ens(pred, x, y));
    let tracked new_perm = y;
    //
    // ...
    //
    arbitrary()
})
```

### Design Questions

- Is an `atomically` block "just" the constructor for the `AtomicUpdate` type?
    Should we allow users to construct atomic updates directly like this?

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

    **Travis commented:** This is problematic because the `atomically` block might mutate resources around the function call, so moving the block away from the call could quickly lead to unsoundness.

    We might be able to fix this by implementing the `atomically` block as a `move` closure, allowing it to capture outside resources, but defering their use until the function call.

## Open atomic update

To open an atomic update, we use the following syntax, inspired by [`vstd::open_atomic_invariant`](https://verus-lang.github.io/verus/verusdoc/vstd/macro.open_atomic_invariant.html):

```rs
open_atomic_update!(atomic_update, old_perm => {
    // assume atomic pre `atomic_update`
    // ...
    // assert atomic post `atomic_update`
    new_perm
});
```

The macro expands to the following:

```rs
#[verifier::open_au_block] {
    let old_perm = ::vstd::atomic::open_atomic_update_begin(atomic_update);
    let y = {
        // ...
        new_perm
    };

    ::vstd::atomic::open_atomic_update_end(y);
}
```

The generates VIR-SST looks roughtly as follows:

```rs
let au = atomic_update;
let x = arbitrary();

assume(AtomicUpdate::req(au, x));

let old_perm = x;
let y = {
    // ...
    new_perm
};

assert(AtomicUpdate::ens(au, x, y));
```

The `open_atomic_update` macro takes an atomic update `atomic_update` as an argument, and binds a new variable `old_perm`, which satisfies the pre-condition of the atomic update.
The new permission `new_perm` must be returned at the end of the macro, and it must satisfy the post-condition of the atomic update.

This macro is typically used in conjuction with the atomic function call, as follows:

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

This combination is effectively used to transform (or "map") one atomic update into another.

## Open atomic invariant

```rs
function(args) atomically |update| {
    open_atomic_invariant!(inv => perm => {
        // ...
        perm = update(perm);
        // ...
    });
}
```

The `open_atomic_invariant` macro is already implemented in vstd, and the `atomically` block has precisely the same syntax and semantics as in the previous section, so this example is boring (which is great).

## Provide full permissions

For cases where we have full permission for the atomic we want to access, it would be nice to have a shorthand syntax like this:

```rs
function(args) atomically (&mut perm);
```

### Design Question:

- This syntax was proposed very early on in the design process, it is unclear if this is still consistent with the current proposal.
