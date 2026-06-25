# Implication (`==>`, `<==`, and `<==>`)
### Syntax

```verus-grammar
V@[implies_expr] ::= V@[spec_expr] ==>  V@[spec_expr]
V@[explies_expr] ::= V@[spec_expr] <==  V@[spec_expr]
V@[iff_expr]     ::= V@[spec_expr] <==> V@[spec_expr]
```

### Typing

All three operators require both sides to have type `bool` and return `bool`.

### Semantics

`P ==> Q`, read _P implies Q_, is `true` whenever `P` is `false` or `Q` is `true`:

```
P ==> Q  ≡  !P || Q
```

`P <== Q` (_P is implied by Q_) is the converse: it is equivalent to `Q ==> P`. It is
sometimes useful for readability when the consequent is more naturally written first.

`P <==> Q` (_P if and only if Q_) is true when both sides have the same truth value:

```
P <==> Q  ≡  P == Q
```

Note that `<==>` has the same syntactic [precedence](./spec-operator-precedence.md) as `==>`
rather than the tighter precedence of `==`, so it can often be used without extra parentheses
in contexts where `==` would require them.
