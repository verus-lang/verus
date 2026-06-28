# Sledgehammer: Automatically completing proofs using broadcast lemmas

Completing proofs involving data structures such as sequences, sets, and maps
often involves finding the right lemmas that exist in the standard library.
Since `vstd` provides a large number of lemmas that is expected to grow over
time, identifying which lemmas may be useful during a proof development becomes
a tedious, manual task.

To simplify this task, Verus provides *Sledgehammer*, inspired by the [eponymous
tool](https://isabelle.in.tum.de/doc/sledgehammer.pdf) provided by
the [Isabelle](https://isabelle.in.tum.de/) theorem prover.

Sledgehammer is an *experimental* feature that attempts to automatically complete
a proof attempt by automatically using relevant lemmas using the
[broadcast](broadcast_proof.md) mechanism. For example, consider the following
example:

```rust
{{#include ../../../../examples/guide/sledgehammer.rs:set_example_fails}}
```

This function fails to prove without additional annotations. Suppose however,
that elsewhere in the project, someone already proved a helpful lemma:

```rust
{{#include ../../../../examples/guide/sledgehammer.rs:set_example_lemma}}
```

The proof of `union_three_sets` automatically succeeds when adding `broadcast
use union_len;` to its body. However, this requires identifying both knowing the
name of this lemma, and enabling it via `broadcast use`.

To simplifying finding relevant lemmas, Verus provides the
`#[verifier::sledgehammer]` annotation to search for existing `broadcast` lemmas
that would complete a proof. The feature can be used to identify the missing
lemma as follows:

```rust
{{#include ../../../../examples/guide/sledgehammer.rs:set_example_sledgehammer}}
```

Running Verus on this example now prints the following message:

```
note: Sledgehammer found proof with 5 lemmas, minimizing..
  --> ../examples/guide/sledgehammer.rs:26:7
   |
26 | proof fn union_three_sets<A>(xs: Set<A>, ys: Set<A>, zs: Set<A>)
   |       ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

note: Sledgehammer found proof with 1 lemmas:
      broadcast use union_len;
  --> ../examples/guide/sledgehammer.rs:26:7
   |
26 | proof fn union_three_sets<A>(xs: Set<A>, ys: Set<A>, zs: Set<A>)
   |       ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^
```

This message indicates that inserting `broadcast use union_len;` is sufficient
to complete the proof of `union_three_sets`. Copy-pasting this statement into
the function yields a proof that no longer requires the Sledgehammer attribute:

```
{{#include ../../../../examples/guide/sledgehammer.rs:set_example_done}}
```

The `#[verifier::sledgehammer]` attribute can be applied to `proof` and `exec`
mode functions. After finding a proof with Sledgehammer, the
`#[verifier::sledgehammer]` attribute should afterwards be removed from the
function to avoid rerunning the proof search on every Verus invocation.

**Note:** Sledgehammer can only discover proofs using lemmas marked as
`broadcast`. Additionally, Sledgehammer's proof attempts may time out, even
though a proof with the right subset of relevant lemmas would succeed.

## Proof Minimization

By default, Sledgehammer will minimize a proof; in the above example,
Sledgehammer initially found a proof that used 5 lemmas, but then determined
that only one lemma is actually necessary. However, in some case, minimizing a
successful proof is time-consuming. During development, it may be enough to know
that a proof exists, while leaving minimization of this proof for later.

Sledgehammer supports skipping proof minimization by passing `false` to the
attribute:


```rust
{{#include ../../../../examples/guide/sledgehammer.rs:set_example_sledgehammer_no_min}}
```

In this case, Sledgehammer produces a proof containing additional, unnecessary
lemmas:

```
note: Sledgehammer found proof with 5 lemmas:
      broadcast use union_len;
      broadcast use vstd::set::axiom_set_contains_len;
      broadcast use vstd::set::axiom_set_ext_equal;
      broadcast use vstd::set::axiom_set_union;
      broadcast use vstd::set::axiom_set_union_finite;
```

## Limitation: Lemmas from other crates

Due to technical limitations, Sledgehammer only takes into account lemmas that
are either are defined in or referenced by the current crate. For example,
absent any other references to `vstd::Seq::lemma_flatten_push`, Sledgehammer
fails to find a proof in the following example:

```rust
{{#include ../../../../examples/guide/sledgehammer.rs:requires_vstd_lemma}}
```

However, the `vstd::Seq::lemma_flatten_push` would be sufficient to complete the
proof. When referencing this lemma anywhere in the current project, Sledgehammer
is able to complete the proof. Adding the following `broadcast group` results in
a successful proof search:

```rust
{{#include ../../../../examples/guide/sledgehammer.rs:vstd_lemma_reference}}
```

```
note: Sledgehammer found proof with 1 lemmas:
      broadcast use vstd::seq::Seq::lemma_flatten_push;
  --> ../examples/guide/sledgehammer.rs:51:7
   |
51 | proof fn my_proof() {
   |       ^^^^^^^^^^^^^
```

Any reference to `lemma_flatten_push`, including via a `broadcast group` that
contains it, is sufficient to make this lemma visible to Sledgehammer. It can be
helpful to include large lemma groups such as
`vstd::seq_lib::group_seq_properties` and `vstd::set_lib::group_set_properties`
in `broadcast group sledgehammer_hints` to ensure that a lot of common
properties are available to Sledgehammer. Similarly, for library code intended
to be reused by Verus projects, providing a `broadcast group` including all
`broadcast` lemmas may be helpful for consumers of the library.

This shortcoming will be addressed in future Verus versions.