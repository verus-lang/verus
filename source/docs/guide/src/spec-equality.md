# Spec equality (`==`)

For an introduction, see [Equality](./equality.md).

## Syntax

```verus-grammar
V@[equality_expr] ::= V@[spec_expr] == V@[spec_expr]
                    | V@[spec_expr] != V@[spec_expr]
```

In spec mode, `==` is mathematical equality — it is not the same as `==` in exec code,
which dispatches to the [`PartialEq`](https://doc.rust-lang.org/std/cmp/trait.PartialEq.html) trait.
The `!=` operator is its negation.
