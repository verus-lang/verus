# Spec index operator []

In spec expressions, the index operator is treated differently than
in exec expressions, where it corresponds to the [usual Rust index operator](https://doc.rust-lang.org/std/ops/trait.Index.html).

Specifically, in a spec expression, the expression `expr[i]` is a shorthand for
`expr.spec_index(i)`. This is a purely syntactic transformation, and there is no
particular trait.

For example:

 * [`spec_index` for a Seq](https://verus-lang.github.io/verus/verusdoc/vstd/seq/struct.Seq.html#method.spec_index)
 * [`spec_index` for a Map](https://verus-lang.github.io/verus/verusdoc/vstd/map/struct.Map.html#method.spec_index)
 * [`spec_index` for a slice](https://verus-lang.github.io/verus/verusdoc/vstd/slice/trait.SliceAdditionalSpecFns.html#tymethod.spec_index)
