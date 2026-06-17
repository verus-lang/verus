# Atomic specifications

We can declare a function to be logically atomic by adding an `atomically` block to its specification.
The atomic specification has the following general shape:

```rs
exec fn function(px: PX) -> (py: PY)
    atomically (atomic_update) {
        type PredType,

        (ax: AX) -> (ay: AY),

        requires atomic_pre(px, ax),
        ensures atomic_post(px, ax, ay),

        outer_mask [...],
        inner_mask [...],
    },

    requires private_pre(px),
    ensures private_post(px, ax, ay, py),
```

Inside the `atomically` block, we find the `requires` and `ensures` clauses which denote the *atomic* pre- and postcondition, which describe the state of the program just before/after the linearization point (LP) respectively.

To attach resources to the atomic pre- and postcondition, we can use the arrow `(ax: AX) -> (ay: AY)`.
In what follows, we will refer to `ax: AX` as the "input type" of the atomic update, and `ay: AY` as the output type.
Both `ax` and `ay` are always tracked-mode.

This atomic specification binds an additional variable called `atomic_update` which has type `AtomicUpdate<AX, AY, PredType>`.
The predicate type can be given a name using the optional `type PredType` clause as seen above.

The final two clauses `outer_mask` and `inner_mask` specify the invariant masks of the atomic update.
We will see what they do in later sections.

## The abort case

The output type of the atomic update (`AY` above) must implement the `UpdateTry` trait.
This trait allows us to determine if a specific output value indicates that the atomic update has been committed or aborted.

```rs
pub enum UpdateControlFlow {
    Commit,
    Abort,
}

pub trait UpdateTry {
    spec fn branch(self) -> UpdateControlFlow;
}
```

The Verus standard library provides implementations of this trait for two types:

- `AY = Result<T, E>` specifies an atomic update which can be committed by outputting `Ok(t)` and aborted using `Err(e)`, this is equivalent to the atomic update as it can be found in Iris, except that we do not force `AX` and `E` to be the same.

- `AY = Commit<T>` specifies an atomic update that cannot be aborted.

In cases where one wants to differentiate between multiple different commit or abort cases, it can be helpful to implement this trait for custom types.

It is possible to define an abort-only type `Abort<T>` analogously to `Commit<T>`, though such an output type would prevent both the library function and the atomic function call from terminating, which is typically undesirable for a logically atomic function.

## The predicate type

The atomic update object bound by the above specification has type `AtomicUpdate<AX, AY, PredType>`.
Similar to the invariant types in Verus, there is just one `AtomicUpdate` type provided by `vstd` that is *configured* using its last type argument (which we call the **predicate type**) using a trait implementation.

The predicate type and it's trait implementation is generated automatically by Verus when the user writes an atomic specification.
For the specification above, we generate (roughly) the following:

```rs
struct PredType { px: Ghost<PX> }

impl UpdatePredicate<AX, AY> for PredType {
    open spec fn req(self, x: X)       -> bool { atomic_pre  }
    open spec fn ens(self, x: X, y: Y) -> bool { atomic_post }

    open spec fn outer_mask(self) -> ISet<int> { [...] }
    open spec fn inner_mask(self) -> ISet<int> { [...] }
}

impl PredType {
    open spec fn args(self, px: PX) -> bool { self.px == px }
}
```

We store the function arguments in the predicate type to allow the atomic pre- and postcondition to depend on them.

## Running examples

This is what the atomic specification for our two example functions may look like:

```rs
pub fn reset(var: &PAtomicU64)
    atomically (atomic_update) {
        (perm: PermissionU64) -> (commit: Commit<PermissionU64>),

        requires
            perm@.patomic == var.id(),

        ensures
            commit@.patomic == perm@.patomic,
            commit@.value == 0,

        outer_mask any,
        inner_mask none,
    },
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
```
