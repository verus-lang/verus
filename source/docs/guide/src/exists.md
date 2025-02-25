# exists and choose

`exists` expressions are the dual of `forall` expressions.
While `forall|i: int| f(i)` means that `f(i)` is true for all `i`,
`exists|i: int| f(i)` means that `f(i)` is true for at least one `i`.
To prove `exists|i: int| f(i)`,
an SMT solver has to find one value for `i` such that `f(i)` is true.
This value is called a *witness* for `exists|i: int| f(i)`.
As with `forall` expressions, proofs about `exists` expressions are based on triggers.
Specifically, to prove an `exists` expression,
the SMT solver uses the `exists` expression's trigger to try to find a witness.

In the following example, the trigger is `is_even(i)`:

```rust
{{#include ../../../rust_verify/example/guide/quants.rs:test_exists_succeeds}}
```

There are three expressions that match the trigger:
`is_even(4)`, `is_even(5)`, and `is_even(6)`.
Two of them, `is_even(4)` and `is_even(6)` are possible witnesses
for `exists|i: int| #[trigger] is_even(i)`.
Based on these, the assertion succeeds, using either `i = 4` or `i = 6` as a witness.

By contrast, the same assertion fails in the following code,
since no expressions matching `is_even(i)` are around:

```rust
{{#include ../../../rust_verify/example/guide/quants.rs:test_exists_fails}}
```

## choose

The proofs above try to prove that an `exists` expression is true.
Suppose, though, that we already know that an `exists` expression is true,
perhaps because we assume it as a function precondition.
This means that some witness to the `exists` expression must exist.
If we want to get the witness, we can use a `choose` expression.

A `choose` expression `choose|i: int| f(i)` implements
the Hilbert choice operator
(sometimes known as [epsilon](https://en.wikipedia.org/wiki/Epsilon_calculus)):
it chooses some value `i` that satisfies `f(i)` if such a value exists.
Otherwise, it picks an arbitrary value for `i`.

The following example assumes `exists|i: int| f(i)` as a precondition.
Based on this, the SMT solver knows that there is at least one witness `i`
that makes `f(i)` true,
and `choose` picks one of these witnesses arbitrarily:

```rust
{{#include ../../../rust_verify/example/guide/quants.rs:test_choose_succeeds}}
```

If, on the other hand, we don't know `exists|i: int| f(i)`,
then `choose` just returns an arbitrary value that might not satisfy `f(i)`
(as discussed in [ghost vs exec code](./ghost_vs_exec.md),
ghost code can create an arbitrary value of any type):

```rust
{{#include ../../../rust_verify/example/guide/quants.rs:test_choose_fails}}
```

Regardless of whether we know `exists|i: int| f(i)` or not,
the `choose|i: int| f(i)` expression always returns the same value:

```rust
{{#include ../../../rust_verify/example/guide/quants.rs:test_choose_same}}
```

You can also choose multiple values together,
collecting the values in a tuple:

```rust
{{#include ../../../rust_verify/example/guide/quants.rs:test_choose_succeeds2}}
```

In this example, the SMT solver can prove
`exists|i: int, j: int| less_than(i, j)`
because the expression `less_than(3, 7)` matches the
automatically chosen trigger `less_than(i, j)` when `i = 3` and `j = 7`,
so that `i = 3, j = 7` serves as a witness.
