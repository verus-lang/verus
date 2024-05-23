# Proofs by Computation

## Motivation
Some proofs should be "obvious" by simply computing on values.  For example,
given a function `pow(base, exp)` defining exponentiation, we would like it to
be straightforward and deterministic to prove that `pow(2, 8) == 256`.
However, in general, to keep recursive functions like `pow` from overwhelming
the SMT solver with too many unrollings, Verus defaults to only unrolling such
definitions once.  Hence, to make the assertion above go through, the developer
needs to carefully adjust the amount of "fuel" provided to unroll `pow`.  Even
with such adjustment, we have observed cases where Z3 does "the wrong thing",
e.g., it does not unroll the definitions enough, or it refuses to simplify
non-linear operations on statically known constants.  As a result, seemingly
simple proofs like the one above don't always go through as expected.

## Enter Proof by Computation

Verus allows the developer to perform such proofs via computation, i.e.,
by running an internal interpreter over the asserted fact.  The developer
can specify the desired computation using `assert(e) by (compute)` (for some
expression `e`).  Continuing the example above, the developer could
write:

```rust
{{#include ../../../rust_verify/example/guide/assert_by_compute.rs:pow_concrete}}
```

In Assertion 1, Verus will internally reduce the left-hand side to 256 by repeatedly evaluating
`pow` and then simplify the entire expression to `true`.

When encoded to the SMT solver, the result will be (approximately):
```
assert(true);
assume(pow(2, 8) == 256);
```
In other words, in the encoding, we assert whatever remains after
simplification and then assume the original expression.  Hence, even if
simplification only partially succeeds, Z3 may still be able to complete the
proof.  Furthermore, because we assume the original expression, it is still
available to trigger other ambient knowledge or contribute to subsequent facts.
Hence Assertion 2 will succeed, since Z3 will unfold the definition of `pow`
once and then use the previously established fact that `pow(2,8) == 256`.

If you want to ensure that the entire proof completes through computation and
leaves no additional work for Z3, then you can use `assert(e) by
(compute_only)` as shown in Assertion 3.  Such an assertion will fail unless
the interpreter succeeds in reducing the expression completely down to `true`.
This can be useful for ensuring the stability of your proof, since it does not
rely on any Z3 heuristics.

Important note: An assertion using proof by computation does not inherit any context
from its environment.  Hence, this example:

```rust
{{#include ../../../rust_verify/example/guide/assert_by_compute.rs:let_fails}}
```

will fail, since `x` will be treated symbolically, and hence the assertion will
not simplify all the way down to `true`.  This can be remedied either
by using `assert(e) by (compute)` and allowing Z3 to finish the proof, or by moving 
the `let` into the assertion, e.g., as:

```rust
{{#include ../../../rust_verify/example/guide/assert_by_compute.rs:let_passes}}
```

While proofs by computation are most useful for concrete values, the interpreter
also supports symbolic values, and hence it can complete certain proofs 
symbolically.  For example, given variables `a, b, c, d`, the following succeeds:

```rust
{{#include ../../../rust_verify/example/guide/assert_by_compute.rs:seq_example}}
```

To prevent infinite interpretation loops (which can arise even when the code is
proven to terminate, since the termination proof only applies to concrete
inputs, whereas the interpreter may encounter symbolic values), Verus limits
the time it will spend interpreting any given proof by computation.
Specifically, the time limit is the number of seconds specified via the
`--rlimit` command-line option.

By default, the interpreter does not cache function call results based on the 
value of the arguments passed to the function.  Experiments showed this typically
hurts performance, since it entails traversing the (large) AST nodes representing
the arguments.  However, some examples need such caching to succceed (e.g., computing
with the naive definition of Fibonacci).  Such functions can be annotated with
`#[verifier::memoize]`, which will cause their results to be cached during computation.

## Current Limitations

0. As mentioned above, the expression given to a proof by computation is
   interpreted in isolation from any surrounding context.
1. The expression passed to a proof-by-computation assertion must be in spec mode,
   which means it cannot be used on proof or exec mode functions.
2. The interpreter is recursive, so a deeply nested expression (or
   series of function calls) may cause Verus to exceed the process'
   stack space.

## See Also

1. The [test suite](https://github.com/verus-lang/verus/blob/main/source/rust_verify_test/tests/assert_by_compute.rs) has a variety of small examples.
2. We also have several [more complex examples](https://github.com/verus-lang/verus/blob/main/source/rust_verify/example/assert_by_compute.rs).
