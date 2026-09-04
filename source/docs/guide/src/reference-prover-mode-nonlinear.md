# The nonlinear solver

> [!TIP]
> See the [guide page](./nonlinear.md) for practical tips on using the `nonlinear_arith` solver.

### Methods of invocation

**By assertion.**
The `nonlinear_arith` solver can be invoked via an [`assert-by` statement](./reference-assert-by-prover.md):

```
assert(Q) by(nonlinear_arith);
```

Proves `Q` via the the `nonlinear_arith` solver.

```
assert(Q) by(nonlinear_arith) requires P;
```

Proves `P ==> Q` via the the `nonlinear_arith` solver.

**As a proof function.**
The `nonlinear_arith` solver can be invoked with a `by(nonlinear_arith)` on a [proof function](./reference-proof-signature.md).

```
proof fn example(...) by(nonlinear_arith)
    requires P
    ensures Q
{ }
```

This proves `P ==> Q` via the `bit_vector` solver.

## Solver operation

The solver uses Z3's theory of nonlinear arithmetic. This can often solve problems
that involve multiplication or division of symbolic values. For example,
commutativity axioms like `a * b == b * a` are accessible in this mode.
