# returns

The `returns` clause is syntactic sugar for an `ensures` clause of a certain form.
The `returns` clause can be provided instead of or in addition to an `ensures` clause.

The following:

```rust
fn example() -> return_type
    returns $expr
{
  ...
}
```

is equivalent to:

```rust
fn example() -> (return_name: return_type)
    ensures return_name == $expr
{
  ...
}
```

## With the `#![verifier::allow_in_spec]` attribute

The [`#![verifier::allow_in_spec]` attribute](./reference-attributes.md#verifierallowinspec) attribute can be applied to an executable function with a [`returns` clause](./reference-returns.md).  This allows the function to be used in spec mode, where it is interpreted as equivalent to the specified return-value.
