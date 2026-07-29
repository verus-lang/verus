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
In what follows, we will refer to `ax: AX` as the *input type* of the atomic update, and `ay: AY` as the *output type*.
Both `ax` and `ay` are always tracked-mode.

This atomic specification binds an additional variable of type `AtomicUpdate<AX, AY, PredType>`.
While the name of this `tracked` variable is user-defined, we will call it `atomic_update` throughout this guide for consistency.
The predicate type can be given a name using the optional `type PredType` clause as seen above. For more information, see the [section on the predicate type](#the-predicate-type) below.

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

- `AY = Result<T, E>` specifies an atomic update which can be committed by outputting `Ok(t)` and aborted using `Err(e)`; this is equivalent an Iris atomic update, except that we do not force `AX` and `E` to be the same.

- `AY = Commit<T>` specifies an atomic update that cannot be aborted.

To differentiate between multiple different commit or abort cases, it can be helpful to implement this trait for a custom output type.

It is possible to define an abort-only type `Abort<T>` analogously to `Commit<T>`, though such an output type would prevent both the library function and the atomic function call from terminating, which is typically undesirable for a logically atomic function.

## The predicate type

The atomic update object bound by the above specification has type `AtomicUpdate<AX, AY, PredType>`.
Similar to the invariant types in Verus, there is just one `AtomicUpdate` type provided by `vstd` that is *configured* using its last type argument (which we call the **predicate type**) using a trait implementation.

The predicate type and its trait implementation is generated automatically by Verus when the user writes an atomic specification.
For the specification above, we generate (roughly) the following:

```rs
struct PredType { px: Ghost<PX> }

impl UpdatePredicate<AX, AY> for PredType {
    open spec fn req(self, ax: AX)         -> bool { atomic_pre  }
    open spec fn ens(self, ax: AX, ay: AY) -> bool { atomic_post }

    open spec fn outer_mask(self) -> ISet<int> { [...] }
    open spec fn inner_mask(self) -> ISet<int> { [...] }
}

impl PredType {
    open spec fn args(self, px: PX) -> bool { self.px == px }
}
```

We store the function arguments in the predicate type to allow the atomic pre- and postcondition to depend on them.
If the atomic update is moved across function boundaries,
or around loops (especially when [loop isolation is enabled](./reference-attributes.html#verifierloop_isolation)),
it is sometimes necessary to reassert the value of the function arguments.
This can be done with `au.pred().args(...)`, using the `PredType::args` predicate defined above.

It is currently not possible to use a custom or pre-existing predicate type to define a logically atomic function.
This also means it is not useful to implement the `UpdatePredicate` trait by hand.

## Running examples

This is what the atomic specification for our two example functions may look like:

```rs
{{#include ../../../../examples/guide/logatom.rs:reset_signature_1}}

{{#include ../../../../examples/guide/logatom.rs:reset_signature_2}}

{{#include ../../../../examples/guide/logatom.rs:reset_signature_3}}

{{#include ../../../../examples/guide/logatom.rs:reset_signature_4}}
```

Here, we specify that the atomic update takes a `PermissionU64` for the atomic variable `var` as its input, and the output is a permission object with the same ID (i.e. for the same variable), with a value of zero.
The output of the atomic update is wrapped in a `Commit<...>` which specifies that this AU cannot abort.

```rs
{{#include ../../../../examples/guide/logatom.rs:increment_signature_1}}

{{#include ../../../../examples/guide/logatom.rs:increment_signature_2}}

{{#include ../../../../examples/guide/logatom.rs:increment_signature_3}}

{{#include ../../../../examples/guide/logatom.rs:increment_signature_4}}

{{#include ../../../../examples/guide/logatom.rs:increment_signature_5}}
```

This specification is a bit more interesting.
Here, the output is a `Result<...>` which means that the atomic update can be aborted.
The atomic postcondition specifies that when the AU is aborted (that is, when `res` is `Err`), the ID and value of the permission stays the same;
otherwise when the AU is committed, the value increases by one.
When the AU is aborted, we also pass an `OpenInvariantCredit` from the library to the client.
This allows the client to open an invariant multiple times in the atomic function call.
We will see more about this later.
Finally, the function returns the previous value of the atomic variable, as specified by the function postcondition.
