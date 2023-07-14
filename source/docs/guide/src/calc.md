# Structured Proofs by Calculation

## Motivation

Sometimes, you need to establish some relation `R` between two expressions, say,
`a_1` and `a_n`, where it might be easier to do this in a series of steps, `a_1`
to `a_2`, `a_2` to `a_3`, ... all the way to `a_n`. One might do this by just
doing all the steps at once, but as mentioned in the section on
[assert-by](./assert_by.md), a better approach might be to split it into a
collection of restricted contexts. This is better, but still might not be ideal,
since you need to repeat each of the intermediate expressions at each point.

## `calc!`ulations, to Reduce Redundant Redundancy

The `calc!` macro supports structured proofs through calculations.

In particular, one can show `a_1 R a_n` for some transitive relation `R` by performing a series
of steps `a_1 R a_2`, `a_2 R a_3`, ... `a_{n-1} R a_n`. The calc macro provides both convenient
syntax sugar to perform such a proof conveniently, without repeating oneself too often, or
exposing the internal steps to the outside context.

The expected usage looks like:

```rust
calc! {
  (R)
  a_1; { /* proof that a_1 R a_2 */ }
  a_2; { /* proof that a_2 R a_3 */ }
   ...
  a_n;
}
```

For example,

```rust
{{#include ../../../rust_verify/example/guide/calc.rs:simple}}
```

which is equivalent to proving `a <= 5` using `a <= b <= 5`. In this case, each
of the intermediate proofs are trivial, thus have an empty `{}` block, but in
general, can have arbitrary proofs inside their blocks.

Notice that you mention `a_1`, `a_2`, ... `a_n` only once each. Additionally,
the proof for each of the steps is localized, and restricted to only its
particular step, ensuring that proof-context is not polluted.

The body of the function where this `calc` statement is written only gets to see
`a_1 R a_n`, and not any of the intermediate steps (or their proofs), further
limiting proof-context pollution.

Currently, the `calc!` macro supports common transitive relations for `R` (such
as `==` and `<=`). This set of relations may be extended in the future.

## Relating Relations to Relations

While a relation like `<=` might be useful to use like above, it is possible
that not every intermediate step needs a `<=`; sometimes one might be able to be
more precise, and maintaining this (especially for documentation/readability
reasons) might be useful. For example, one might want to say `a_1 <= a_2 == a_3
<= a_4 < a_5 <= ...`.

This is supported by `calc` by specifying the extra intermediate relations
inline (with the default being the high-level relation). These relations are
checked to be consistent with the top-level relation, in order to maintain
transitivity (so for example, using `>` in the above chain would be caught and
reported with a helpful message).

A simple example of using intermediate relations looks like the following:

```rust
{{#include ../../../rust_verify/example/guide/calc.rs:transitive}}
```

This example is equivalent to saying `x <= y` using `x == 5 - 3 < 5 <= y`.
