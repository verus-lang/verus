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

Verus requires the body of a logically atomic function (like `reset` or `increment` in our running example) to prove that the atomic update has been opened and committed by the time the function returns.
We enforce this requirement using the prophecy variable `au.resolves()`.
Initially, the value of `au.resolves()` is known;
when the atomic update is resolved by the `try_open_atomic_update!` macro, the value of `au.resolves()` becomes `true`.

To open the atomic update, `au.outer_mask()` must be valid in the current scope.
Inside the body of the `try_open_atomic_update` macro, `au.inner_mask()` becomes the new invariant mask.

## Running examples

Here are the full definitions of our two example functions:

```rs
{{#include ../../../../examples/guide/logatom.rs:reset_definition}}
```

```rs
{{#include ../../../../examples/guide/logatom.rs:increment_definition}}
```
