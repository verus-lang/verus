# Chained operators

## Syntax

```verus-grammar
V@[chained_expr] ::= V@[spec_expr] (V@[cmp_op] V@[spec_expr])+
V@[cmp_op]       ::= < | <= | > | >= | ==
```

In spec code, equality and inequality operators can be chained. For example,
`a <= b < c`
is equivalent to
`a <= b && b < c`.

Chained inequalities support `<`, `<=`, `>`, `>=`, and `==`, and support sequences of chained
operators of arbitrary length.
