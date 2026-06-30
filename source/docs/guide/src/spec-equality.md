# Spec equality (`==`)

> [!DIFF]
> In spec mode, `==` is mathematical equality — it is not the same as `==` in exec code,
which dispatches to the [`PartialEq`](https://doc.rust-lang.org/std/cmp/trait.PartialEq.html) trait.

For an introduction, see [Equality](./equality.md).

### Syntax

```verus-grammar
V@[equality_expr] ::= V@[spec_expr] == V@[spec_expr]
                | V@[spec_expr] != V@[spec_expr]
```

### Typing

The expression is well-typed if both the left-hand side and right-hand side have the same type.

In some cases, Verus may also accept `==` as well-typed when both sides have the same
[mathematical interpretation](./reference-types.md). For example:

 * Two [integer types](./reference-types.md#integer-types) can always be compared.
 * `T` can be compared to `&T`.

### Semantics

The `==` operator returns `true` iff the two sides are equivalent in their [mathematical interpretation](./reference-types.md). The `!=` operator is the negation.
