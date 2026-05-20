# Spec index operator []

### Syntax

```verus-grammar
V@[spec_index_expr] ::= V@[spec_expr] [ V@[spec_expr] ]
```

### Desugaring

In spec code, the expression `expr[i]` desguars to `expr.spec_index(i)`, which is resolved as normal via Rust's [method resolution](https://doc.rust-lang.org/reference/expressions/method-call-expr.html).

> **Note:** This is different than the index operator in executable code,
> where it is either a [place expression](https://doc.rust-lang.org/reference/expressions.html#place-expressions-and-value-expressions) indexing into a slice or an array, or is overloaded via the [`Index`](https://doc.rust-lang.org/std/ops/trait.Index.html) or [`IndexMut`](https://doc.rust-lang.org/std/ops/trait.IndexMut.html) traits.

### Use cases

For example:

 * [`spec_index` for a Seq](https://verus-lang.github.io/verus/verusdoc/vstd/seq/struct.Seq.html#method.spec_index)
 * [`spec_index` for a Map](https://verus-lang.github.io/verus/verusdoc/vstd/map/struct.Map.html#method.spec_index)
 * [`spec_index` for a slice](https://verus-lang.github.io/verus/verusdoc/vstd/slice/trait.SliceAdditionalSpecFns.html#tymethod.spec_index)
