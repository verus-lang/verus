# Proofs by Computation

## Motivation
Some proofs should be "obvious" by simplying computing on values.  For example,
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
can specify the desired computation using `assert_by_compute`.  E.g., continuing
the example above, the developer could write:
```
assert_by_compute(pow(2, 8) == 256);
```
Verus will internally reduce the left-hand side to 256 by repeatedly evaluating
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
For example, if the developer then writes:
```
assert(pow(2, 9) == 512);
```
This will succeed, since Z3 will unfold the definition of `pow` once and then
use the previously established fact that `pow(2,8) == 256`.

If you want to ensure that the entire proof completes through computation
and leaves no additional work for Z3, then you can use:
```
assert_by_compute_only(pow(2, 8) == 256);
```
which will fail unless the interpreter succeeds in reducing the expression
completely down to `true`.  This can be useful for ensuring the stability
of your proof, since it does not rely on any Z3 heuristics.

Important note: An `assert_by_compute` expression does not inherit any context
from its environment.  Hence, this example:
```
let x = 2;
assert_by_compute_only(pow(2, x) == 4);
```
will fail, since `x` will be treated symbolically.  This can be remedied either
by using `assert_by_compute` and allowing Z3 to finish the proof, or by moving 
the `let` into the assertion, e.g., as:
```
assert_by_compute_only({
  let x = 2;
  pow(2, x) == 4
});
```

While `assert_by_compute` is most useful for concrete values, the interpreter
also supports symbolic values, and hence it can complete certain proofs 
symbolically.  For example, given variables `a, b, c, d`, the following succeeds:
```
assert_by_compute_only(seq![a, b, c, d].ext_equal(seq![a, b].add(seq![c, d])));
```

To prevent infinite interpretation loops (which can arise even when the code is
proven to terminate, since the termination proof only applies to concrete
inputs, whereas the interpreter may encounter symbolic values), Verus limits
the time it will spend interpreting any given `assert_by_compute`.
Specifically, the time limit is the number of seconds specified via the
`rlimit` command-line option.

## Current Limitations

0. As mentioned above, the expression given to `assert_by_compute` is
   interpreted in isolation from any surrounding context.
1. The expression passed to `assert_by_compute` must be in spec mode,
   which means it cannot be used on proof or exec mode functions.
2. The interpreter is recursive, so a deeply nested expression (or
   series of function calls) may cause Verus to exceed the process'
   stack space.
3. The interpreter currently caches function call results based on the 
   value of the arguments passed to the function.  This enables examples
   like (naive) Fibonacci to succeed, but it comes at the cost of somewhat 
   slower performance.  Potential future work would be to add support for
   a `#[memoize]` or `#[memoize_for_compute]` annotation, so that only 
   functions with that annotation would be memoized.

## See Also

1. The [test suite](../../rust_verify/tests/assert_by_compute.rs) has a variety of small examples.
2. We also have several [more complex examples](../../rust_verify/example/assert_by_compute.rs).
