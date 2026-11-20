# assert forall ... by

The `assert forall ... by` statement is used to write a proof of a `forall` expression
while introducing the quantified variables into the context.

### Syntax

```verus-grammar
V@[assert_by_forall_stmt] ::=
    assert forall |R@[binders]| (V@[spec_expr] implies)? V@[spec_expr] by { V@[proof_stmt]* }
```

Note the lack of parentheses, in contrast to the ordinary `assert` statements.

### Typing

The spec expressions and proof body may refer to variables bound in the R@[binders].
The spec expressions must have type `bool`.

### Proof operation

For an `assert forall` statement of the form `assert forall |binders| P implies Q`,
the predicate `P` is introduced as a hypothesis for the proof body, and the objective of the proof
body is to prove `Q`. In the end, the predicate `forall |binders| P ==> Q` is proved,
which is available in the context for the remainder of the proof.

The simplified form `assert forall |binders| Q` is equivalent to
`assert forall |binders| true implies Q`.

Much like an ordinary [`assert ... by`](./reference-assert-by.md) statement, the proof
inside the body does not enter the context for the remainder of the proof.
