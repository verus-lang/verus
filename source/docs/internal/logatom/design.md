# Logical Atomicity
*Aaron Bies, Travis Hance, Derek Dreyer*

## Motivating Example

```rs
use std::sync::atomic::AtomicU32;
use std::sync::atomic::Ordering::SeqCst;

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

Both functions satisfy the same naive specification:
$$
\{ v \mapsto n \}\;\;{\tt increment}(v)\;\;\{ v \mapsto n + 1 \}
$$
...but clearly the functions are not sematically equivalent!

## Resources/Related Work

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
    }
    requires pre_condition(args),
    ensures post_condition(args, res),
{
    ..;
}
```

The atomic pre- and post-condition, specified in the `atomic_spec` block, desugars to an additional *tracked* function argument `atomic_update: AtomicUpdate`, as follows:

```rs
struct FunctionPred {}

impl UpdatePredicate<(Args, OldPerm), NewPerm> for FunctionPred {
    spec fn req((args, old_perm): (Args, OldPerm)) -> bool {
        atomic_pre_condition(args, old_perm)
    }

    spec fn ens((args, old_perm): (Args, OldPerm), (new_perm): (NewPerm)) -> bool {
        atomic_post_condition(args, old_perm, new_perm)
    }
}

fn function(
    args: Args,
    tracked atomic_update: AtomicUpdate<(Args, OldPerm), NewPerm, FunctionPred>
) -> (res: R)
    requires pre_condition(args),
    ensures post_condition(args, res),
{
    // ...
}
```

### Design Questions

- Is the atomic post-condition allowed to talk about the return value of the function?
- Is the predicate type we generate always empty?
- Should `req` and `ens` have a separate argument for the function arguments, so that the types `X` and `Y` strictly correspond to the old and new permissions?

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

<details>
<summary>Desugaring</summary>

Ideally, this language feature would desugar to something like this:

```rs
function(args, ::builtin::atomically(move |update| {
    // ...
    // assert atomic pre `function`
    let new_perm = update(old_perm);
    // assume atomic post `function`
    // ...
}))
```

...but this requires the `atomically` function to have the following signature:

```rs
fn atomically<X, Y, Pred>(f: impl FnOnce(impl FnOnce(X) -> Y)) -> AtomicUpdate<X, Y, Pred>

// with `impl Trait` expanded

fn atomically<X, Y, Pred, F>(f: F) -> AtomicUpdate<X, Y, Pred>
where
    F: for<U: FnOnce(X) -> Y> FnOnce(U),
```

...which is a higher-kinded function and sadly not supported in Rust.

After some experimentation, I (Aaron) ended up with this desugaring:

```rs
#[doc(hidden)]
pub struct UpdateTypeInject<X, Y, P> {
    _dummy: core::marker::PhantomData<(spec_fn(X) -> Y, P)>,
}

#[doc(hidden)]
#[cfg(verus_keep_ghost)]
#[verifier::external_body]
pub proof fn update_internal<X, Y, Pred: UpdatePredicate<X, Y>>(
    _update_type_inject: UpdateTypeInject<X, Y, Pred>,
    x: X,
) -> (y: Y)
    requires Pred::req(x),
    ensures Pred::ens(x, y),
{
    arbitrary()
}

#[doc(hidden)]
#[cfg(verus_keep_ghost)]
#[verifier::external_body]
pub fn atomically<X, Y, P>(
    _f: impl FnOnce(UpdateTypeInject<X, Y, P>)
) -> AtomicUpdate<X, Y, P> {
    arbitrary()
}

// --- 8< --- snip --- >8 ---

function(args, ::vstd::atomic::atomically(move |upd_ty_inj| {
    let update = move |x| ::vstd::atomic::update_internal(upd_ty_inj, x);
    // ...
    let new_perm = update(old_perm);
    // ...
}))
```

Note that with this encoding, we do not need to name the types of `X`, `Y` and `Pred` at call sight, the `atomically` function infers it from the callee through its return type, `upd_ty_inj` infers it from the `atomically` function, and `update_internal` gets it from `upd_ty_inj`.

</details>

Here, `update` is an uninterpreted function that takes ownership of `old_perm` and produces `new_perm`.
This function must be called exactly once within the `atomically |update| { ... }` block.

It has the atomic pre- and post-conditions of the function we're calling as its (private) pre- and post-conditions.
Since the function is uninterpreted, it is up to the post-condition the uniquely determine the value of `new_pred`, otherwise the value is non-deterministic.

## Open atomic update

To open an atomic update, we use the following syntax, inspired by [`vstd::open_atomic_invariant`](https://verus-lang.github.io/verus/verusdoc/vstd/macro.open_atomic_invariant.html):

```rs
open_atomic_update!(atomic_update => old_perm => {
    // assume atomic pre `atomic_update`
    // ...
    // assert atomic post `atomic_update`
    return new_perm;
});
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

    **Travis commented:** This is problematic because the `atomically` block might mutate resources around the function call, so moving the block away from the call could quickly lead to unsoundness.

    We might be able to fix this by implementing the `atomically` block as a `move` closure, allowing it to capture outside resources, but defering their use until the function call.

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
