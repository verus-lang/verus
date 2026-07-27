# The `has` operator

### Syntax

```verus-grammar
V@[has_expr] ::= V@[spec_expr]  has V@[spec_expr]
           | V@[spec_expr] !has V@[spec_expr]
```

### Desugaring

In spec code, the expression `expr1 has expr2` desguars to `expr1.spec_has(expr2)`, which is resolved as normal via Rust's standard [method resolution](https://doc.rust-lang.org/reference/expressions/method-call-expr.html).

Likewise, the expression `expr1 !has expr2` desugars to `!expr1.spec_has(expr2)`.

### Examples

We typically use the has operator to indicate that a collection
contains a particular element.
The `vstd` library provides several container types with `spec_has` functions defined,
e.g.,
[`Set::spec_has`](https://verus-lang.github.io/verus/verusdoc/vstd/set/struct.Set.html#method.spec_has)
and
[`Multiset::spec_has`](https://verus-lang.github.io/verus/verusdoc/vstd/multiset/struct.Multiset.html#method.spec_has).

Example:

```rust
proof fn test_set() {
    let s: Set<int> = set![1, 2];
    assert(s has 1);
    assert(s has 2);
    assert(s !has 3);
}

proof fn test_multiset() {
    let s: Multiset<int> = Multiset::empty().insert(1).insert(1).insert(2);
    assert(s has 1);
    assert(s has 2);
    assert(s !has 3);
}
```
