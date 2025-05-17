# Putting It All Together

To show how `spec`, `proof`, and `exec` code work together, consider the example
below of computing the n-th [triangular number](https://en.wikipedia.org/wiki/Triangular_number).
We'll cover this example and the features it uses in more detail in [Chapter 4](recursion_loops.md),
so for now, let's focus on the high-level structure of the code.

We use a `spec` function `triangle` to mathematically define our specification using natural numbers (`nat`)
and a recursive description.  We then write a more efficient iterative implementation
as the `exec` function `loop_triangle` (recall that `exec` is the default mode for functions).
We connect the correctness of `loop_triangle`'s return value to our mathematical specification 
in `loop_triangle`'s `ensures` clause.

However, to successfully verify `loop_triangle`, we need a few more things.  First, in executable
code, we have to worry about the possibility of arithmetic overflow.  To keep things simple here,
we add a precondition to `loop_triangle` saying that the result needs to be less than one million,
which means it will certainly fit into a `u32`.

We also need to translate the knowledge that the final `triangle` result fits in a `u32`
into the knowledge that each individual step of computing the result won't overflow,
i.e., that computing `sum = sum + idx` won't overflow.  We can do this by showing
that `triangle` is monotonic; i.e., if you increase the argument to `triangle`, the result increases too.
Showing this property requires an [inductive proof](induction.md).  We cover inductive proofs
later; the important thing here is that we can do this proof using a `proof` function
(`triangle_is_monotonic`).  To invoke the results of our proof in our `exec` implementation, 
we [assert](proof_functions.md#assert-by) that the new sum fits, and as
justification, we  an invoke our proof with the relevant arguments.  At the
call site, Verus will check that the preconditions for `triangle_is_monotonic`
hold and then assume that the postconditions hold.

Finally, our implementation uses a while loop, which means it requires some [loop invariants](while.md),
which we cover later.

```rust
{{#include ../../../../examples/guide/recursion.rs:spec}}
```

```rust
{{#include ../../../../examples/guide/recursion.rs:mono}}
```

```rust
{{#include ../../../../examples/guide/recursion.rs:loop}}
```



