# Quantifiers

Suppose that we want to specify that all the elements of a sequence are even.
If the sequence has a small, fixed size,
we could write a specification for every element separately:

```rust
{{#include ../../../rust_verify/example/guide/quants.rs:quants_finite}}
```

Clearly, though, this won't scale well to larger sequences or sequences of unknown length.

We could write a recursive specification:

```rust
{{#include ../../../rust_verify/example/guide/quants.rs:quants_recursion}}
```

However, using a recursive definition will lead to many proofs by induction,
which can require a lot of programmer effort to write.

Fortunately, Verus and SMT solvers support the
[universal and existential quantifiers](https://en.wikipedia.org/wiki/Quantifier_(logic))
`forall` and `exists`,
which we can think of as infinite conjunctions or disjunctions:

```
(forall|i: int| f(i)) = ... f(-2) && f(-1) && f(0) && f(1) && f(2) && ...
(exists|i: int| f(i)) = ... f(-2) || f(-1) || f(0) || f(1) || f(2) || ...
```

With this, it's much more convenient to write a specification about all elements of a sequence:

```rust
{{#include ../../../rust_verify/example/guide/quants.rs:quants_use_forall}}
```

Although quantifiers are very powerful, they require some care,
because the SMT solver's reasoning about quantifiers is incomplete.
This isn't a deficiency in the SMT solver's implementation,
but rather a deeper issue:
it's an undecidable problem to figure out whether a formula
with quantifiers, functions, and arithmetic is valid or not,
so there's no complete algorithm that the SMT solver could implement.
Instead, the SMT solver uses an incomplete strategy based on *triggers*,
which instantiates quantifiers when expressions match trigger patterns.

This chapter will describe how to use `forall` and `exists`,
how triggers work,
and some related topics on `choose` expressions and closures.
