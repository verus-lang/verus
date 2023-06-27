# assert ... by(bit_vector)

Invoke Z3's bitvector solver to prove the given predicate.

```
assert(P) by(bit_vector);
```

```
assert(P) by(bit_vector)
  requires Q;
```

The solver uses a technique called _bit-blasting_, which represents each numeric variable
by its binary representation as a bit vector, and every operation as a boolean circuit.

The prover does not have access to any prior context except that which is given in
the `requires` clause, if provided. If the `requires` clause is provided, then the
bit vector solver attempts to prove `Q ==> P`. Verus will also check (using its normal solver)
that `Q` holds from the prior proof context.

The expressions `P` and `Q` may only contain expressions that the bit solver understands.
The only types allowed are booleans and fixed-width unsigned integer types.
The allowed operations are bitwise (`&`, `|`, `^`, `!`, `<<`, `>>`) and arithmetic
(`add`, `sub`, `mul`, `/`, and `%`).

Note that `+`, `-`, and `*` return `int` or `nat` types when they are used as spec expressions.
Since the bit vector solver does not handle the infinite-width type `int`, it cannot
handle `+`, `-`, or `*`.
Function calls are also disallowed.
