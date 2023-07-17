# assert forall ... by

The `assert forall ... by` statement is used to write a proof of a `forall` expression
while introducing the quantified variables into the context.

```rust
assert forall |idents| P by {
    // ... proof here
}
// ... remainder
```

Much like an ordinary [`assert ... by`](./reference-assert-by.md) statement, the proof
inside the body does not enter the context for the remainder of the proof.
Only the `forall |idents| P` expression enters the context.
Furthermore, within the proof body, the variables in the `idents` may be 

Note that the **parentheses _must_ be left off**, in contrast to other kinds of `assert` statements.

For convenience, you can use `implies` to introduce a hypothesis automatically into
the proof block:

```rust
assert forall |idents| H implies P by {
    // ... proof here
}
// ... remainder
```

This will make `H` available in the proof block, so you only have to prove `P`.
In the end, the predicate `forall |idents| H ==> P` will be proved.
