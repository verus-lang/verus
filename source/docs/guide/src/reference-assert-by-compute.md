# assert ... by(compute) / by(compute_only)

See [this section of the tutorial](./assert_by_compute.md) for motivation and an example.

A statement of the form:

```
assert(P) by(compute_only);
```

Will evaluate the expression `P` as far a possible, and Verus accepts the result if it
evaluates to the boolean expression `true`. It unfolds function definitions and evaluates
arithmetic expressions. It is capable of some symbolic manipulation, but it does not handle
algebraic laws like `a + b == b + a`, and it works best when evaluating constant expressions.

Note that it will **not** substitute local variables, instead treating them as
symbolic values.

This statement:

```
assert(P) by(compute);
```

Will first run the interpreter as above, but if it doesn't succeed, it will then attempt
to finish the problem through the normal solver. So for example, if after expansion
`P` results in a trivial expression like `a+b == b+a`, then it should be solved
with `by(compute)`.

### Memoization

The [`#[verifier::memoize]` attribute](./reference-attributes.md#verifiermemoize) can be used to mark
certain functions for [memoizing](https://en.wikipedia.org/wiki/Memoization).
This will direct Verus's internal interpreter to only evaluate the function once for any
given combination of arguments. This is useful for functions that would be impractical
to evaluate naively, as in this example:

```rust
{{#include ../../../rust_verify/example/guide/assert_by_compute.rs:fibonacci_memoize}}
```
