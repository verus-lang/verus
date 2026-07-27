# assert ... by

The `assert ... by` statement is used to encapsulate a proof. 

### Syntax

```verus-grammar
V@[assert_by_stmt] ::= assert ( V@[spec_expr] ) by { V@[proof_stmt]* }
```

### Proof operation

For a boolean predicate `P`:

```rust
assert(P) by {
    // ... proof here
}
// ... remainder
```

Verus will validate the proof and then attempt to use it to prove `P`.
The contents of the proof, however, will not be included in the context used to
prove the remainder.
Only `P` will be introduced into the context for the remainder.
