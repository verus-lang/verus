# Invoking the linearization point

To invoke the linearization point in the definition of a logically atomic function, we must "open" the atomic update object we were given by the atomic specification.
To do so, we can use the `try_open_atomic_update` macro as follows:

```rs
let res_au = try_open_atomic_update!(au, mut? ax => {
    // assume atomic pre
    // ...
    // assert atomic post
    Tracked(ay)
})
```

When we open the atomic update, the macro consumes the atomic update. In the body of the macro call, we are then given the input `ax: AX` and learn the atomic precondition, and at the end of the macro call, we return the output `ay: AY` and prove the atomic postcondition.

The macro outputs a value of type `Tracked<Result<(), AtomicUpdate<AX, AY, PredType>>>`.
If the atomic update is committed, as indicated by the `UpdateTry` trait, then the atomic update is consumed and we get `Ok(())`.
Otherwise, if the atomic update is aborted, we get back the same atomic update we put in `Err(au)`, allowing us to open it again later.

## The resolves check

Verus requires the body of a logically atomic function to prove that the atomic update has been opened and committed by the time the function returns.
We enforce this requirement using the prophecy variable `au.resolves()`.
Initially, the value of `au.resolves()` is unknown;
when the atomic update is resolved by the `try_open_atomic_update!` macro, the value of `au.resolves()` becomes `true`.
The user must then prove that `au.resolves()` when the function returns.

## Invariant masks

To open the atomic update, its outer mask must be valid in the current scope, that is, we must be able to open every invariant namespace in the set `au.outer_mask()` at the current program point.
Inside the body of the `try_open_atomic_update` macro, we can only open the invariant namespaces in the set `au.inner_mask()`.
The difference between the outer and inner mask is precisely the set of invariants which the client is allowed to open [in the atomic function call](./logatom-call.md).

## Running examples

Here are the full definitions of our two example functions:

```rs
{{#include ../../../../examples/guide/logatom.rs:reset_definition}}
```

```rs
{{#include ../../../../examples/guide/logatom.rs:increment_definition}}
```
