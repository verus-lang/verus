# Extensional equality (`=~=` and `=~~=`)

The **shallow extensional equality operator** `=~=` 
and **deep extensional equality operator** `=~~=` are both equivalent to
[spec equality (`==`)](./spec-equality.md).

These operators are distinguished only by their impact on the proof search.
Specifically, the use of the `=~=` and `=~~=` operators will trigger the application of
"extensional equality" operators.

See [the guide page](extensional_equality.md) for an introductory explanation with motivation.

### Syntax

```verus-grammar
V@[ext_eq_expr] ::= V@[spec_expr] =~=  V@[spec_expr]
              | V@[spec_expr] =~~= V@[spec_expr]
```

### Typing

The extensional equality operator requires both the left-hand side and right-hand side
to have the same type. The expression returns a [`bool`](./reference-types#bool).

### Semantics

The operator is equivalent to [spec equality](./spec-equality.md).
