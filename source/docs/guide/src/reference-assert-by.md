# assert ... by

The `assert ... by` statement is used to encapsulate a proof. For a boolean `spec` expression, `P`, one writes:

```rust
assert(P) by {
    // ... proof here
}
// ... remainder
```

Verus will validate the proof and then attempt to use it to prove the P.
The contents of the proof, however, will not be included in the context used to
prove the remainder.
Only `P` will be introduced into the context for the remainder.
