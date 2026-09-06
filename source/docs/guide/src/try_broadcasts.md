# `try_broadcasts`: Automatically completing proofs using broadcast lemmas

Completing proofs involving data structures such as sequences, sets, and maps
often involves finding the right lemmas that exist in the standard library.
Since `vstd` provides a large number of lemmas that is expected to grow over
time, identifying which lemmas may be useful during a proof development becomes
a tedious, manual task.

To simplify this task, Verus provides the `#[verifier::try_broadcasts]`
attribute, inspired by the [Sledgehammer
tool](https://isabelle.in.tum.de/doc/sledgehammer.pdf) provided by the
[Isabelle](https://isabelle.in.tum.de/) theorem prover.

`try_broadcasts` is an *experimental* feature that attempts to automatically complete
a proof attempt by using relevant lemmas using the
[broadcast](broadcast_proof.md) mechanism. For example, consider the following
example:

```rust
{{#include ../../../../examples/guide/try_broadcasts.rs:set_example_fails}}
```

This function fails to prove without additional annotations. Suppose however,
that elsewhere in the project, someone already proved a helpful lemma:

```rust
{{#include ../../../../examples/guide/try_broadcasts.rs:set_example_lemma}}
```

The proof of `union_three_sets` automatically succeeds when `broadcast use
union_len;` is added to its body. However, this requires both knowing the name
of this lemma, and enabling it via `broadcast use`.

To simplify finding relevant lemmas, Verus provides the
`#[verifier::try_broadcasts]` annotation to search for existing `broadcast`
lemmas that would complete a proof. The feature can be used to identify the
missing lemma as follows:

```rust
{{#include ../../../../examples/guide/try_broadcasts.rs:set_example_try_broadcasts}}
```

Running Verus on this example now prints the following message:

```
note: try_broadcasts found a proof with 5 lemmas, minimizing..
  --> ../examples/guide/try_broadcasts.rs:26:7
   |
26 | proof fn union_three_sets<A>(xs: Set<A>, ys: Set<A>, zs: Set<A>)
   |       ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

note: try_broadcasts found a proof with 1 lemma:
      broadcast use union_len;
  --> ../examples/guide/try_broadcasts.rs:26:7
   |
26 | proof fn union_three_sets<A>(xs: Set<A>, ys: Set<A>, zs: Set<A>)
   |       ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
```

This message indicates that inserting `broadcast use union_len;` is sufficient
to complete the proof of `union_three_sets`. Copy-pasting this statement into
the function yields a proof that no longer requires the `try_broadcasts` attribute:

```
{{#include ../../../../examples/guide/try_broadcasts.rs:set_example_done}}
```

The `#[verifier::try_broadcasts]` attribute can be applied to `proof` and `exec`
mode functions. After finding a proof with `try_broadcasts,` the
`#[verifier::try_broadcasts]` attribute should afterwards be removed from the
function to avoid rerunning the proof search on every Verus invocation.

**Note:** `try_broadcasts` can only discover proofs using lemmas marked as
`broadcast`. Additionally, `try_broadcasts's` proof attempts may time out, even
though a proof with the right subset of relevant lemmas would succeed.

## Proof Minimization

By default, `try_broadcasts` will minimize a proof; in the above example,
`try_broadcasts` initially found a proof that used 5 lemmas, but then determined
that only one lemma is actually necessary. However, in some case, minimizing a
successful proof is time-consuming. During development, it may be enough to know
that a proof exists, while leaving minimization of this proof for later.

`try_broadcasts` supports skipping proof minimization by passing `false` to the
attribute:


```rust
{{#include ../../../../examples/guide/try_broadcasts.rs:set_example_try_broadcasts_no_min}}
```

In this case, try_broadcasts produces a proof containing additional, unnecessary
lemmas:

```
note: try_broadcasts found proof with 5 lemmas:
      broadcast use union_len;
      broadcast use vstd::set::axiom_set_contains_len;
      broadcast use vstd::set::axiom_set_ext_equal;
      broadcast use vstd::set::axiom_set_union;
      broadcast use vstd::set::axiom_set_union_finite;
```
