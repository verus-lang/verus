# assert ... by(nonlinear_arith)

Invoke Z3's nonlinear solver to prove the given predicate.

```
assert(P) by(bit_vector);
```

```
assert(P) by(bit_vector)
  requires Q;
```

The solver uses Z3's theory of nonlinear arithmetic. This can often solve problems
that involve multiplication or division of symbolic values. For example,
commutativity axioms like `a * b == b * a` are accessible in this mode.

The prover does not have access to any prior context except that which is given in
the `requires` clause, if provided. If the `requires` clause is provided, then the
bit vector solver attempts to prove `Q ==> P`. Verus will also check (using its normal solver)
that `Q` holds from the prior proof context.
