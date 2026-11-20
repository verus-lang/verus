# The `matches` operator

### Syntax

```verus-grammar
V@[matches_expr] ::= V@[spec_expr] matches R@[pattern] &&  V@[spec_expr]
               | V@[spec_expr] matches R@[pattern] ==> V@[spec_expr]
```

### Typing

The left-hand side should be of a type that matches the R@[pattern], while the right-hand
side should have type `bool`.
The right-hand side may reference variables bound by the pattern.

The V@[matches_expr] as a whole has type `bool`.

### Semantics

The "matches-and" expression `expr matches pat && condition` is equivalent to:

```rust
match expr {
    pat => condition,
    _ => false,
}
```

The "matches-implies" expression `expr matches pat ==> condition` is equivalent to:

```rust
match expr {
    pat => condition,
    _ => true,
}
```
