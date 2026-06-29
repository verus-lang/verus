# assert ... by(...)

The `assert ... by` statement is used to invoke a specialized _prover mode_ to prove
the given expression.

### Syntax

```verus-grammar
V@[assert_by_prover_stmt] ::= assert ( V@[spec_expr] ) by { V@[proof_stmt]* }
```


> [!NOTE]
> At present, the [`integer_ring`](./reference-prover-mode-integer-ring.md) prover mode may only
> be used in a [proof function declaration](./reference-proof-signature.md),
> not in an assert-by.


### Proof operation

