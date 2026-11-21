# Calling verified code from unverified code

Of course, the correctness of Verus code depends on meeting the assumptions as provided
in its specification. If you call verified code from unverified code, Verus won't be
able to check that these contracts are upheld at each call-site, so the responsibility
is on the developer to meet them.

The developer needs to meet these assumptions:

 * Any `requires` clauses on the function being called
 * Any trait implementations used to meet the function's trait bounds are implemented
   according to the trait specifications.

Let's consider an example of the latter. Suppose **V** is the verified source code, which declares
a trait `Trait` and a function with a trait bound, `f<T: Trait>`.
Also suppose `Trait` has a function `trait_fn` with an `ensures` clause.

Now suppose we have unverified source **U**, which defines a type `X` and a trait impl
`impl Trait for X`.

Then, in order for **U** to safely call `f`, the developer needs to make sure that
`X::trait_fn` correctly meets the `ensures` specification that **V** demands.

## Defensive programming

To be sure that your verified code remains correct when called from unverified code,
you should check that your public API (both the functions *and* the trait functions you define)
has no `requires` clauses, since you cannot count on unverified code to uphold
those preconditions.  If you have an API function with a precondition, you may
be able to shift the precondition into an implication in the postcondition.
In other words, instead of saying `requires P, ensures Q`, you can write
`ensures P ==> Q`.  If you need to require `P` for safety, e.g., your code will panic
if passed `None`, then you can consider writing a wrapper function that dynamically
checks the argument and only calls your verified code when the value is `Some`.

To systematically enforce this defensive programming discipline,
Verus provides the (experimental) command-line flag: `-V check-api-safety`.

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
For unverified implementations of `Drop`, this onus is on the user to meet this criterion.

# Warning

As discussed in [the last section](./memory-safety.md), the memory safety of a verified
program is conditional on verification. **Therefore, calling verified code from unverified
code could be non-memory-safe if the unverified code fails to uphold these contracts.**
