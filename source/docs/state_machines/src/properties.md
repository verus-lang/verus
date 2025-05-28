# Properties

The `property!` operation is not actually a transition.  Instead, it allows you to export
useful facts from the state-machine view of the world to thread-local reasoning in your 
implementation.

For example, suppose your state machine has:
```rust
fields {
    #[sharding(bool)]
    pub waiting: bool,

    #[sharding(variable)]
    pub num_remaining: nat,

    ...
}
```
where `num_remaining` corresponds to an atomic U32 counting the number of
threads that still need to perform an operation.  You could represent this by
maintaining a state-machine level invariant that `self.waiting ==>
self.num_remaining > 0`.  However, that fact is not available in your code by
default.  Hence, if your code needs to prove, say, that when it decreases the
atomic U32, the value does not wrap around, you can establish this via a
property:

```rust
property! {
  waiting_means_positive() {
    assert(self.waiting ==> self.num_remaining > 0);
  }
}
```
Verus will check that the invariant establishes this property, and then it will make
`waiting_means_positive` available to the code as a lemma that can be invoked on the
state-machine's `Instance`.

You can also use a `property!` to establish a proof-by-contradiction. Continuing the example
above, suppose you also maintain an invariant that `num_remaining < 10`.  In your implementation,
perhaps your code contains a function that receives a token `tok` representing
`num_remaining` but doesn't know how large the contained value might be.  To prove that the value
isn't too large, you can use a property like this:
```rust
property! {
  in_bounds() {
    have num_remaining >= (10);
    assert(false);
  }
}
```
Again, Verus will check that the invariant establishes this property, and then
it will make `in_bounds` available to the code as a lemma that can be invoked
on the state-machine's `Instance`.  Invoking that lemma with a shared reference
to `tok` will allow the code to conclude that the value in `tok` must be less
than 10.

Finally, when working with storage strategies (e.g.,
[storage_option](strategy-storage-option.md) or
[storage_map](strategy-storage-map.md)), to obtain a shared permission to the
stored value, you can use the `guard` operation inside a property.  For
instance, if your state machine has:
```rust
fields {
  #[sharding(bool)]
  pub deposited: bool,

  #[sharding(storage_option)]
  pub perm: Option<Perm>,

    ...
}
```
then you can write a property like this:
```rust
property! {
  get_perm_ref(x: Perm) {
    have deposited >= (true);
    guard perm >= (Some(x));
  }
}
```
Verus will check that your invariant implies that `perm` is `Some` (e.g.,
perhaps your invariant says `self.deposited ==> self.perm.is_some()`).
VerusSync will make `get_perm_ref` available to the code as a lemma that can be
invoked on the state-machine's `Instance`.  Invoking that lemma with a shared
reference to a token for `deposited` and the ghost value of `perm` will
produce a shared reference to the value in `perm`.

