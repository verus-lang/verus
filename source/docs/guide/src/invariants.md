# Devising Invariants for Loops and Recursion

Below, we develop several examples that show how to work through
the process of devising invariants for loops
and for recursive functions.


## Example 1: Fibonacci

Suppose our goal is to compute values in the [Fibonacci sequence](https://en.wikipedia.org/wiki/Fibonacci_sequence).
We use a `spec` function `fib` to mathematically define our specification using `nat`s
and a recursive description:
```rust
{{#include ../../../rust_verify/example/guide/invariants.rs:fib_spec}}
```

Our goal is to write a more efficient iterative implementation as the `exec`
function `fib_impl`.  To keep things simple, we'll add a precondition to
`fib_impl` saying that the result needs to fit into a `u64` value.
We connect the correctness of `fib_impl`'s return value
to our mathematical specification in `fib_impl`'s `ensures` clause.
```rust
{{#include ../../../rust_verify/example/guide/invariants.rs:fib_impl_no_proof}}
```
However, if we ask Verus to verify this code, it reports two errors:
```
error: postcondition not satisfied
   |
   |           result == fib(n as nat),
   |           ----------------------- failed this postcondition
```
and 
```
error: possible arithmetic underflow/overflow
   |
   |         let new_cur = cur + prev;
   |                       ^^^^^^^^^^
```












We also need to translate the knowledge that the final `fib` result fits into a `u64`
into the knowledge that each individual step of computing the result won't overflow,
i.e., that computing `new_cur = cur + prev` won't overflow.  We can do this by showing
that `fib` is monotonic; i.e., if you increase the argument to `fib`, the result increases too.
Showing this property requires an inductive proof.  We cover [inductive proofs](induction.md)
later; the important thing here is that we can do this proof using a `proof` function
(`lemma_fib_is_monotonic`).  To call this lemma in our `exec` implementation, we employ
a `proof {}` block and pass in the relevant arguments.  At the call site, Verus will check
that the preconditions for `lemma_fib_is_monotonic` hold and then assume that the postdconditions hold.

Finally, our implementation uses a while loop, which means it requires some [loop invariants](while.md),
which we cover later.


















Here's the final version that verifies properly:
```rust
{{#include ../../../rust_verify/example/guide/invariants.rs:fib_final}}
```

