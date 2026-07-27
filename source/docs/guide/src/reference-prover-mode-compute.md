# The compute mode

> [!TIP]
> See the [guide page](./assert_by_compute.md) for practical tips on using this feature.

### Methods of invocation

**By assertion.**
The `nonlinear_arith` solver can be invoked via an [`assert-by` statement](./reference-assert-by-prover.md):

```
assert(Q) by(compute_only);
```

Proves `Q` by simplifying it via the interpreter and checking
if the result is the boolean value `true`.

```
assert(Q) by(compute);
```

Proves `Q` by simplifying it via the interpreter to an expression `Q'` and replacing
the statement with `assert(Q);`.

### Interpreter operation

The interpreter unfolds function definitions and evaluates
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

### Configurating the evaluation strategy

The [`#[verifier::memoize]` attribute](./reference-attributes.md#verifiermemoize) can be used to mark
certain functions for [memoizing](https://en.wikipedia.org/wiki/Memoization).
This will direct Verus's internal interpreter to only evaluate the function once for any
given combination of arguments. This is useful for functions that would be impractical
to evaluate naively, as in this example:

```rust
{{#include ../../../../examples/guide/assert_by_compute.rs:fibonacci_memoize}}
```
