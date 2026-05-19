# Spec quantifiers (`forall`, `exists`)

For an intuition-guided introduction to quantifiers and triggers, see the
[Quantifiers](quants.md) tutorial, specifically [forall and triggers](forall.md)
and [exists and choose](exists.md).

Both `forall` and `exists` are **spec-mode only** expressions.

### Syntax

```verus-grammar
V@[forall_expr] ::= forall |R@[binders...]| V@[spec_expr]
V@[exists_expr] ::= exists |R@[binders...]| V@[spec_expr]
```

The body V@[spec_expr] may be preceded by [trigger annotations](./trigger-annotations.md).

### Typing

The body V@[spec_expr] must have type `bool`. The bound variables are available as spec-mode
variables within the body. Both `forall` and `exists` expressions have type `bool`.

### Semantics

`forall|x: T| P(x)` is `true` if and only if `P(x)` is `true` for every value `x` of type `T`.

`exists|x: T| P(x)` is `true` if and only if there exists at least one value `x` of type `T`
such that `P(x)` is `true`. The two are duals, and because Verus uses classical logic:

```
exists|x: T| P(x)  ≡  !forall|x: T| !P(x)
```

Both quantifiers support binding multiple variables simultaneously, which is equivalent to
nesting single-variable quantifiers:

```rust
// These two are equivalent:
forall|i: int, j: int| i < j ==> f(i) <= f(j)
forall|i: int| forall|j: int| i < j ==> f(i) <= f(j)
```

### Triggers

Because quantifiers range over infinite domains, the SMT solver does not enumerate all
possible instantiations. Instead it uses *triggers*: syntactic patterns that, when matched
by terms in the proof context, cause the quantifier to be instantiated with the matching values.

Every quantifier must have at least one trigger group. Verus can choose triggers
automatically, or they can be specified explicitly using annotations on the quantifier body:

| Annotation | Meaning |
|---|---|
| `#[trigger]` on a sub-expression | That sub-expression is a trigger (grouped with other `#[trigger]` annotations) |
| `#[trigger(n)]` on a sub-expression | That sub-expression is part of trigger group `n` |
| `#![trigger expr1, expr2, ...]` at the root of the body | `expr1, expr2, ...` form a single trigger group |
| `#![auto]` at the root of the body | Use automatic trigger selection and suppress the trigger-logging note |
| `#![all_triggers]` at the root of the body | Use aggressive automatic trigger selection |

For full details on how Verus selects and validates trigger groups, see
[Trigger annotations](./trigger-annotations.md).
