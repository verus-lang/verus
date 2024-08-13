# Expressions and operators for specifications

Though Verus's specification language primarily emulates Rust syntax,
Verus also includes additional notation for common specification needs.
For example:

```rust
forall|i: int, j: int| 0 <= i <= j < len ==> f(i, j)
```

This snippet illustrates:

 * the `forall` quantifier, which we will [cover later](./forall.md)
 * chained operators
 * implication operators

Here, we'll discuss the last two, along with other common notation.

## Chained inequalities

In specifications, you can chain together multiple `<=`, `<`, `>=`, and `>` operations.
For example,
`0 <= i <= j < len` as a shorthand for `0 <= i && i <= j && j < len`.

Initially, the chaining notation may seem to raise questions like,
"Is the middle element of `a <= b <= c` executed twice?"
or, "Does short-circuiting occur?"
However, since
specification expressions are always _pure_, and they do not need to be executable,
these questions are inconsequential for the chain-operator syntax.

## Logical implication

Verus supports an _implication_ operator, `a ==> b`. This is equivalent to
`!a || b`, though usually it is clearer in specification contexts.
It is usually read as "`a` implies `b`".

For example, this expression:

```
forall|i: int, j: int| 0 <= i <= j < len ==> f(i, j)
```

Would be read as "for every pairs `i` and `j` such that `0 <= i <= j < len`,
we have `f(i, j)`".

Verus also has two-way implication (`<==>`), which means that
both sides are equal as boolean values.
It also has backwards implication (`<==`), read "explies".

Note that `==>` has lower precedence that most other spec operations.
For example, `a ==> b && c` means `a ==> (b && c)`.
See [the reference for a full description of precedence
in Verus](./spec-operator-precedence.md).

## Conjunction and disjunction

Because `&&`, `||`, and `==>` are so common in Verus specifications, it is often desirable to have
low precedence versions of `&&` and `||`. Verus also supports "triple-and" (`&&&`) and
"triple-or" (`|||`) which are equivalent to `&&` and `||` except for their precedence.
Implication `==>` binds more tightly than either `&&&` or `|||`.
`&&&` and `|||` are also convenient for the "bulleted list" form:

```
&&& a ==> b
&&& c
&&& d ==> e && f
```

This will parse the same as: `(a ==> b) && c && (d ==> (e && f))`.

## Accessing fields of a `struct` or `enum`

Verus has convenient syntax for accessing fields
of [`struct`](datatypes_struct.md)s
and [`enum`](datatypes_enum.md)s.
