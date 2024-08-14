# `decreases_to!`

The expression <code>decreases_to!(e<sub>1</sub>, e<sub>2</sub>, ..., e<sub>n</sub> => f<sub>1</sub>, f<sub>2</sub>, ..., f<sub>n</sub>)</code> is a bool indicating
if the left-hand sequence
<code>e<sub>1</sub>, e<sub>2</sub>, ..., e<sub>n</sub></code>
_lexicographically-decreases-to_
the right-hand sequence
<code>f<sub>1</sub>, f<sub>2</sub>, ..., f<sub>n</sub></code>

The lexicographic-decreases-to
is used to check the `decreases` measure for spec functions.

See [this tutorial chapter](./lex_mutual.md) for an introductory discussion of
lexicographic-decreases.

## Definition

We say that
<code>e<sub>1</sub>, e<sub>2</sub>, ..., e<sub>n</sub></code>
_lexicographically-decreases-to_
<code>f<sub>1</sub>, f<sub>2</sub>, ..., f<sub>n</sub></code>
if there exists a `k` where `1 <= k <= n` such that:

 * <code>e<sub>k</sub></code> decreases-to <code>f<sub>k</sub></code>.
 * For each `i` where `1 <= i < k`,
    <code>e<sub>i</sub> == f<sub>i</sub></code>.

The _decreases-to_ relation is a partial order on _all_ values; values of different types
_are_ comparable. The relation permits, but is not necessarily limited to:

 * If `x` and `y` are integers, where `x > y >= 0`, then `x` _decreases-to_ `y`.
 * If `a` is a datatype (struct, tuple, or enum) and `f` is one of its "potentially recursive" fields, then `a` _decreases-to_ `a.f`.
   * For a datatype `X`, a field is considered "potentially recursive" if it either mentions `X` or a generic type parameter of `X`.
 * If `f` is a `spec_fn`, then `f` _decreases-to_ `f(i)`.
 * If `s` is a `Seq`, then `s` _decreases-to_ `s[i]`.
 * If `s` is a `Seq`, then `s` _decreases-to_ `s.subrange(i, j)` if the given range is strictly smaller than `0 .. s.len()`. 
   * [`axiom_seq_len_decreases`](https://verus-lang.github.io/verus/verusdoc/vstd/seq/fn.axiom_seq_len_decreases.html) provides a more general axiom; it must be invoked explicitly.
 * If `v` is a `Vec`, then `v` _decreases-to_ [`v@`](./reference-at-sign.md).

These axioms are triggered when the relevant expression (e.g., `x.f`, `x->f`, `s[i]`, `v@`) is used as part of a `decreases-to` expression.

### Notes

 1. Tuples are _not_ compared lexicographically; tuples are datatypes, which are compared
    as explained above, e.g., `a` _decreases_to_ `a.0`.
    Only the "top level" sequences in a `decreases_to!` expression are compared lexicographically.

 2. Sequences are not compared on `len()` alone. However, you can always use `s.len()` as a decreases-measure instead of `s`.

### Examples

```rust
{{#include ../../../rust_verify/example/guide/recursion.rs:example_decreases_to}}
```
