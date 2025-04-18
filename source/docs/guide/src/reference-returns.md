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
