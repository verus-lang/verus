# The `integer_ring` solver

> [!NOTE]
> The `integer_ring` solver requires the Singular tool to be installed. This is not included by default in the Verus binary release. See [the installation details](./install-singular.md).

> [!TIP]
> See the [guide page](./nonlinear.md#2-proving-ring-based-properties-integer_ring) for practical tips on using the `integer_ring` solver.

### Methods of invocation

**As a proof function.**
The `integer_ring` solver can be invoked with a `by(integer_ring)` on a [proof function](./reference-proof-signature.md).

```
proof fn example(...) by(integer_ring)
    requires P
    ensures Q
{ }
```

This proves `P ==> Q` via the `integer_ring` solver.

### Supported predicates

The `integer_ring` mode only supports basic arithmetic: `+`, `-`, `*`, `%`, and `/`, `==`,
and `!=`.

Verus checks that the `requires` clause include terms that all divisors are nonzero.

### Solver operation

The given predicate is reduced to an integer ring problem, which is proved by the Singular
theorem prover.
