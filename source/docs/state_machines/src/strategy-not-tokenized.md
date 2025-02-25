# not_tokenized

The `not_tokenized` strategy can be applied to fields of any type `V`.

```rust
fields {
    #[sharding(not_tokenized)]
    pub field: V,
}
```

This results in **no** token types associated to the field `field`.

It is often useful as a convenient alternative when you would otherwise need an
existential variable in the VerusSync invariant.

## Manipulation of the field

### Initializing the field

Initializing the field is done with the usual `init` statement (as it for all strategies).

```rust
init field = v;
```

Of course, the instance-init function does not emit any tokens for this instruction.

### Reading the field

Reading the field can be done by writing `pre.field`. Notably, this causes the resulting
operation to be non-deterministic in its input arguments. Therefore, `pre.field` can 
only be accessed in a [`birds_eye` context](./birds-eye.md).

### Updating the field

The field can always be updated with an `update` statement in any `transition!` operation.

```rust
update field = v;
```

This does not result in any token inputs or token outputs, and it has no effect on the
signature of the token operation. The `update` instruction may be required in order to
preserve the system invariant.

## Example

TODO
