# Chained operators

### Syntax

```verus-grammar
V@[chained_expr] ::= V@[spec_expr] (V@[cmp_op] V@[spec_expr])+
V@[cmp_op]       ::= < | <= | > | >= | ==
```

### Typing

All operands in a chained expression must be [integer types](./reference-types.md#integer-types).
The expression returns `bool`.

Chained operators are only available in spec mode.

### Semantics

A chained comparison desugars into the conjunction of all adjacent pairs, with each
intermediate value shared between consecutive comparisons:

```
a op1 b op2 c op3 d  ≡  a op1 b && b op2 c && c op3 d
```

For example, `a <= b < c` is equivalent to `a <= b && b < c`.

The supported operators are `<`, `<=`, `>`, `>=`, and `==`, and they may be mixed
freely within a single chain.
