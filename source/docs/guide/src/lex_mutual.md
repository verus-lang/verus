# Lexicographic decreases clauses

For some recursive functions,
it's difficult to specify a single value that decreases
in each recursive call.
For example, the [Ackermann function](https://en.wikipedia.org/wiki/Ackermann_function)
has two parameters `m` and `n`,
and neither `m` nor `n` decrease in all 3 of the recursive calls:

```rust
{{#include ../../../rust_verify/example/guide/recursion.rs:ackermann}}
```

For this situation, Verus allows the `decreases` clause to contain multiple expressions,
and it treats these expressions as
[lexicographically ordered](https://en.wikipedia.org/wiki/Lexicographic_order).
For example, `decreases m, n` means that one of the following must be true:
- m stays the same, and n decreases,
  which happens in the call `ackermann(m, (n - 1) as nat)`
- m decreases and n may increase or decrease arbitrarily,
  which happens in the two calls of the form `ackermann((m - 1) as nat, ...)`

# Mutual recursion

Functions may be mutually recursive,
as in the following example where `is_even` calls `is_odd` recursively
and `is_odd` calls `is_even` recursively:

```rust
{{#include ../../../rust_verify/example/guide/recursion.rs:even}}
```

The recursion here works for both positive and negative `i`;
in both cases, the recursion decreases `abs(i)`, the absolute value of `i`.

An alternate way to write this mutual recursion is:

```rust
{{#include ../../../rust_verify/example/guide/recursion.rs:even2}}
```

In this alternate version, the recursive call `!is_even(i)` doesn't
decrease `abs(i)`, so we can't just use `abs(i)` as the `decreases` clause by itself.
However, we can employ a trick with lexicographic ordering.
If we write `decreases abs(i), 1`,
then the call to `!is_even(i)` keeps the first expression `abs(i)` the same,
but decreases the second expression from `1` to `0`,
which satisfies the lexicographic requirements for decreasing.
The call `is_odd(i - 1)` also obeys lexicographic ordering,
since it decreases the first expression `abs(i)`,
which allows the second expression to increase from `0` to `1`.
