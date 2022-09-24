# Proofs about forall and exists

The previous sections emphasized the importance of triggers
for `forall` and `exists` expressions.
Specifically, if you know `forall|i| f(i)`,
then the SMT solver will instantiate `i` by looking at triggers,
and if you want to prove `exists|i| f(i)`,
then the SMT solver will look at triggers to find a witness `i` such that `f(i)` is true.
In other words, *using* a `forall` expression relies on triggers
and *proving* an `exists` expression relies on triggers.
We can write these cases in the following table:

|        | proving                                 | using                                |
|--------|-----------------------------------------|--------------------------------------|
| forall | usually just works; otherwise assert-by | triggers                             |
| exists | triggers                                | usually just works; otherwise choose |

What about the other two cases,
proving a `forall` expression and using an `exists` expression?
These cases are actually easier to automate and do not rely on triggers.
In fact, they often just work automatically,
as in the following examples:

```rust
{{#include ../../../rust_verify/example/guide/quants.rs:just_works}}
```

In these examples, the triggers play no role.
To emphasize this, we've used a `dummy` function for the trigger
that doesn't even appear anywhere else in the examples,
and the SMT solver still verifies the functions with no difficulty.
(Note, though, that if you called one of the functions above,
then the caller would have to prove the `exists` expression
or use the `forall` expression,
and the caller would have to deal with triggers.)

If you want some intuition for why the SMT solver doesn't
rely on triggers to verify the code above,
you can think of the verification as being similar to the verification of the following code,
where the quantifiers are eliminated and the quantified variables
are hoisted into the function parameters:

```rust
{{#include ../../../rust_verify/example/guide/quants.rs:hoist}}
```

## Proving forall with assert-by

Sometimes a proof doesn't "just work" like it does in the simple examples above.
For example, the proof might rely on a lemma that is proved by induction,
which the SMT solver cannot prove completely automatically.
Suppose we have a lemma that proves `f(i)` for any even `i`:

```rust
spec fn f(i: int) -> bool { ... }

proof fn lemma_even_f(i: int)
    requires
        is_even(i),
    ensures
        f(i),
{ ... }
```

Now suppose we want to prove that `f(i)` is true for all even `i`:

```rust
{{#include ../../../rust_verify/example/guide/quants.rs:test_even_f_fail1}}
```

The proof above fails because it doesn't call `lemma_even_f`.
If we try to call `lemma_even_f`, though, we immediately run into a problem:
we need to pass `i` as an argument to the lemma,
but `i` isn't in scope:

```rust
{{#include ../../../rust_verify/example/guide/quants.rs:test_even_f_fail2}}
```

To deal with this, Verus supports a special form of `assert ... by`
for proving `forall` expressions:

```rust
{{#include ../../../rust_verify/example/guide/quants.rs:test_even_f}}
```

Inside the body of the `assert ... by`,
the variables of the `forall` are in scope
and the left-hand side of the `==>` is assumed.
This allows the body to call `lemma_even_f(i)`.

## Using exists with choose

The example above needed to bring a `forall` quantifier variable into scope
in order to call a lemma.
A similar situation can arise for `exists` quantifier variables.
Suppose we have the following lemma to prove `f(i)`:

```rust
spec fn g(i: int, j: int) -> bool { ... }

proof fn lemma_g_proves_f(i: int, j: int)
    requires
        g(i, j),
    ensures
        f(i),
{ ... }
```

If we know that there exists some `j` such that `g(i, j)` is true,
we should be able to call `lemma_g_proves_f`.
However, we run into the problem that `j` isn't in scope:

```rust
{{#include ../../../rust_verify/example/guide/quants.rs:test_g_proves_f_fails}}
```

In this situation,
we can use `choose` (discussed in the [previous section](./exists.md))
to extract the value `j` from the `exists` expression:

```rust
{{#include ../../../rust_verify/example/guide/quants.rs:test_g_proves_f}}
```
