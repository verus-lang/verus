# Expressions and operators for specifications

Verus extends Rust's syntax with additional operators and expressions
useful for writing specifications.
For example:

```rust
forall|i: int, j: int| 0 <= i <= j < len ==> f(i, j)
```

This snippet illustrates:

 * the `forall` quantifier, which we will [cover later](./forall.md)
 * chained operators
 * implication operators

Here, we'll discuss the last two, along with Verus notation for conjunction, disjunction, and field access.

## Chained inequalities

Specifications can chain together multiple `<=`, `<`, `>=`, and `>` operations.
For example,
`0 <= i <= j < len` has the same meaning as `0 <= i && i <= j && j < len`.

## Logical implication

To make specifications more readable, Verus supports an _implication_ operator `==>`.
The expression `a ==> b` (pronounced "`a` implies `b`") is logically equivalent to `!a || b`.
As an example, the expression

```
forall|i: int, j: int| 0 <= i <= j < len ==> f(i, j)
```

means that for every pair `i` and `j` such that `0 <= i <= j < len`, `f(i, j)` is true.

Note that `==>` has lower precedence that most other boolean operations.
For example, `a ==> b && c` means `a ==> (b && c)`.
Verus also supports two-way implication for booleans (`<==>`) with even lower precedence,
so that `a <==> b && c` is equivalent to `a == (b && c)`.
See [the reference for a full description of precedence
in Verus](./spec-operator-precedence.md).

## Conjunction and disjunction

Because `&&`, `||`, and `==>` are so common in Verus specifications, it is often desirable to have
low precedence versions of `&&` and `||`. Verus also supports "triple-and" (`&&&`) and
"triple-or" (`|||`) which are equivalent to `&&` and `||` except for their precedence.
Implication `==>` and equivalence `<==>` bind more tightly than either `&&&` or `|||`.
`&&&` and `|||` are also convenient for the "bulleted list" form:

```
&&& a ==> b
&&& c
&&& d <==> e && f
```

This has the same meaning as `(a ==> b) && c && (d <==> (e && f))`.

## Accessing fields of a `struct` or `enum`

Verus has `->`, `is`, and `matches` syntax for accessing fields
of [`struct`](datatypes_struct.md)s
and matching variants of [`enum`](datatypes_enum.md)s.
