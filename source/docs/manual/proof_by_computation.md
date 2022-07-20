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
assert_by_compute(pow(2, 8) == 256)
```

[More discussion here]



## Current Limitations


## See Also


