# `decreases_to!`

The expression <code>decreases_to!(e<sub>1</sub>, e<sub>2</sub>, ..., e<sub>n</sub> => f<sub>1</sub>, f<sub>2</sub>, ..., f<sub>n</sub>)</code> is a bool indicating
if the left-hand sequence
<code>e<sub>1</sub>, e<sub>2</sub>, ..., e<sub>n</sub></code>
_lexicographically-decreases-to_
the right-hand sequence
<code>f<sub>1</sub>, f<sub>2</sub>, ..., f<sub>n</sub></code>

The lexicographic-decreases-to
is used to check the `decreases` measure for spec functions.

See [this tutorial chapter](./lex_mutual.md) for an example introduction of lexicographic
decreases.

## Definition

We say that
<code>e<sub>1</sub>, e<sub>2</sub>, ..., e<sub>n</sub></code>
_lexicographically-decreases-to_
<code>f<sub>1</sub>, f<sub>2</sub>, ..., f<sub>n</sub></code>
if there exists a `k` where `1 <= k <= n` such that:

 * <code>e<sub>k</sub></code> decreases-to <code>f<sub>k</sub></code>.
 * For each `i` where `1 <= i < k`,
    <code>e<sub>i</sub> == f<sub>i</sub></code>.

The _decreases-to_ relation is a partial order on all values where:

 * If `x` and `y` are integers, `x` decreases-to `y` if `x >= y` and `y >= 0`.
 * If `a` is a datatype (struct or enum)
    and `b` is the value of one of its fields, then `a` decreases-to `b`.
 * If `a` is a `spec_fn`, then `a` decreases-to `a(i)`.
 * If `a` is a `Seq`, then `a` decreases-to `a[i].

Note that values of different types _are_ comparable. For example, if struct `X` has a field
of type `Y`, then a value of type `X` may decrease-to a value of type `Y`.

### Note about tuples

Tuples are _not_ compared lexicographically; tuples are datatypes, which are compared
as explained above.
Only the "top level" sequences in a `decreases_to!` expression are compared lexicographically.
