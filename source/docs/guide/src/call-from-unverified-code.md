# Calling verified code from unverified code

Of course, the correctness of Verus code depends on meeting the assumptions as provided
in its specification. If you call verified code from unverified code, Verus won't be
able to check that these contracts are upheld at each call-site, so the responsibility
is on the developer to meet them.

The developer needs to meet these assumptions:

 * Any `requires` clauses on the function being called
 * Any trait implementation used to meet the function's trait bounds are implemented
   according to the trait specifications.

Let me give an example of the latter. Suppose **V** is the verified source code, which declares
a trait `Trait` and a function with a trait bound, `f<T: Trait>`.
Also suppose `Trait` has a function `trait_fn` with an `ensures` clause.

Now suppose we have unverified source **U**, which defines a type `X` and a trait impl
`impl Trait for X`.

Then, in order for **U** to safely call `f`, the developer needs to make sure that
`X::trait_fn` correctly meets the `ensures` specification that **V** demands.

## Requirements on the Drop trait

_Note: We hope to simplify or remove this requirement in the future._

Note that the [`Drop` trait](https://doc.rust-lang.org/std/ops/trait.Drop.html) has some special considerations. Specifically, Verus treats `drop`
as if it has the following signature:

```
fn drop(&mut self)
    opens_invariants none
    no_unwind
```

(See [`opens_invariants`](./reference-opens-invariants.md) and [`no_unwind`](./reference-unwind-sig.md).)

For any _verified_ implementation of `Drop`, Verus checks that it meets this criterion.
For unverified implementations of drop, this onus is on the user to meet this criterion.

# Warning

As discussed in [the last chapter](./memory-safety.md), the memory safety of a verified
program is conditional on verification. **Therefore, calling verified code from unverified
code could be non-memory-safe if the unverified code fails to uphold these contracts.**
