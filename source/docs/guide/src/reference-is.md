# The `is` operator

### Syntax

```verus-grammar
V@[is_expr] ::= V@[spec_expr]  is R@[ident]
          | V@[spec_expr] !is R@[ident]
```

### Typing

The left hand side should be an expression with some enum type, and the right hand side should
be an (unqualified) identifier of a variant of that enum. The V@[is_expr] has type `bool`.

### Semantics

An `is` expression returns `true` if the left hand side matches the named variant.
A `!is` expression returns the negation.

### Example

```rust
fn test() {
    let x = Some(5);
    assert(x is Some);
    assert(x !is None);
}
```
