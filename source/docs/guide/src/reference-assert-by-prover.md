# assert ... by(...)

The `assert ... by` statement is used to invoke a specialized _prover mode_ for proving
the given assertion.

### Syntax

We divide the prover modes into "solver modes" (which invoke a solver) and "interpreter modes" (which invoke the interpreter).

```verus-grammar
V@[assert_by_prover_stmt] ::=
    assert ( V@[spec_expr] ) by ( V@[assert_by_solver_mode] ) V@[assert_by_prover_requires]? ;
  | assert ( V@[spec_expr] ) by ( V@[assert_by_interpreter_mode] );

V@[assert_by_solver_mode] ::= nonlinear_arith | bit_vector;
V@[assert_by_interpreter_mode] ::= compute | compute_only;

V@[assert_by_prover_requires] ::=
    requires (V@[spec_expr],)+
```

> [!NOTE]
> At present, the [`integer_ring`](./reference-prover-mode-integer-ring.md) prover mode may only
> be used in a [proof function declaration](./reference-proof-signature.md),
> not in an assert-by.

### Proof operation

**Solver modes.**
For `nonlinear_arith` and `bit_vector` modes,
Verus attempts to prove the given predicate via the specified solver
(the [`nonlinear_arith` solver](./reference-prover-mode-nonlinear.md)
or the [`bit_vector` solver](./reference-prover-mode-bit-vector.md)).
The predicate is proved in isolation, absent any surrounding context.

Specifically, for a statement
<code>assert ( Q ) by ( V@[assert_by_solver_mode] )</code>,
Verus tries to prove `Q` using the solver, and then assumes `Q` for the subsequent code.

If a `requires P` clause is additionally provides, then Verus:

 * Proves `P` using the default solver (with full context available)
 * Proves `P ==> Q` using the specified solver (in isolation)
 * And finally assumes `Q` for subsequent code.

**Interpreter modes.**
For `compute` and `compute_only` modes, Verus uses its [specification interpreter](./reference-prover-mode-compute.md) to simplify the expression `P` as much as possible, yielding an expression `P'`.

 * For `compute_only`, Verus will check that `P'` is the boolean value `true`, and then assumes
   the given predicate for all subsequent code.
 * For `compute`, Verus will replace the assert-by statement with `assert(P')`, which then behaves
   like an ordinary [`assert`](./reference-assert.md).
