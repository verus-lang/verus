# Putting It All Together

To show how `spec`, `proof`, and `exec` code work together, consider the following
(classic) example of computing values in the [Fibonacci sequence](https://en.wikipedia.org/wiki/Fibonacci_sequence)
shown below.
We use a `spec` function `fib` to mathematically define our specification using `nat`s
and a recursive description.  We then write a more efficient iterative implementation
as the `exec` function `fib_impl` (recall that `exec` is the default mode for functions;
we include the annotation here for clarity).  We connect the correctness of `fib_impl`'s
return value to our mathematical specification in `fib_impl`'s `ensures` clause.

However, to successfully verify `fib_impl`, we need a few more things.  First, in executable
code, we have to worry about the possibility of overflow.  To keep things simple here,
we add a precondition to `fib_impl` saying that the result needs to fit into a `u64` value.
We do this through another `spec` function (`fib_fits_u64`) for clarity and in case other
code wants to impose a similar requirement.

We also need to translate the knowledge that the final `fib` result fits into a `u64`
into the knowledge that each individual step of computing the result won't overflow,
i.e., that computing `new_cur = cur + prev` won't overflow.  We can do this by showing
that `fib` is monotonic, i.e., if you increase the argument to `fib` the result grows.
Showing this property requires an inductive proof.  We cover [inductive proofs](induction.md)
later; the important thing here is that we can do this proof using `proof` function
`lemma_fib_is_monotonic`.  To use this lemma in our `exec` implementation, we employ
a `proof {}` block and pass in the relevant arguments.  

Finally, our implementation uses a while loop, which means it requires some [loop invariants](while.md),
which we cover later.

```rust
{{#include ../../../rust_verify/example/guide/modes.rs:fib}}
```

