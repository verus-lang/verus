# The `has` operator

### Syntax

```verus-grammar
V@[has_expr] ::= V@[spec_expr]  has V@[spec_expr]
           | V@[spec_expr] !has V@[spec_expr]
```

### Desugaring

In spec code, the expression `expr1 has expr2` desguars to `expr1.spec_has(expr2)`, which is resolved as normal via Rust's [method resolution](https://doc.rust-lang.org/reference/expressions/method-call-expr.html).

Likewise, the expression `expr1 !has expr2` desugars to `!expr1.spec_has(expr2)`.

### Use cases

For example:

 * [`spec_has` for a `Set`](https://verus-lang.github.io/verus/verusdoc/vstd/set/struct.Set.html#method.spec_has)
 * [`spec_has` for a `Multiset`](https://verus-lang.github.io/verus/verusdoc/vstd/multiset/struct.Multiset.html#method.spec_has)
