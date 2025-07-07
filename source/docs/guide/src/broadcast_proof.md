# Adding Ambient Facts to the Proof Environment with `broadcast`

In a typical Verus project,
a developer might prove a fact 
(e.g., pushing an element into a sequence does not change the elements already in the sequence)
in a proof function, e.g.,
```rust
pub proof fn seq_contains_orig_elems_after_push<A>(s:Seq<A>, v:A, x:A)
    requires s.contains(x)
    ensures s.push(v).contains(x)
{
  ...
}
```
To make use of this fact, the developer must explicitly invoke the proof function,
e.g.,
```rust
proof fn example<A>(s: Seq<A>, v: A, x: A) {
    assume(s.contains(x));
    let t = s.push(v);
    // assert(t.contains(x)); // FAILS
    seq_contains_orig_elems_after_push(s, v, x); // Adds the proof's fact to the proof environment
    assert(t.contains(x)); // SUCCEEDS
  }
```
However, in some cases, a proof fact is so useful that a developer always
wants it to be in scope, without manually invoking the corresponding proof.
For example, the fact that an empty sequence's length is zero is so "obvious"
that most programmers will expect Verus to always know it.
This feature should be used with caution, however, as every extra ambient
fact slows the prover's overall performance.

Suppose that after considering the impact on the solver's performance, the
programmer decides to make the above fact about `push` ambient.  To do so,
they can add the `broadcast` modifier in the
definition of `seq_contains_orig_elems_after_push`: `pub broadcast proof fn seq_contains_orig_elems_after_push<A>(s: Seq<A>, v:A, x:A)`.
The effect is to introduce the following
quantified fact to the proof environment:
```rust
forall |s: Seq<A>, v: A, x: A| s.contains(x) ==> s.push(v).contains(x)
```
Because this introduces a quantifier, Verus will typically ask you to
explicitly choose a trigger, e.g., by adding a `#[trigger]` annotation.
Hence, the final version of our example might look like this:
```rust
pub broadcast proof fn seq_contains_orig_elems_after_push<A>(s:Seq<A>, v:A, x:A)
    requires s.contains(x)
    ensures #[trigger] s.push(v).contains(x)
{
    ...
}
```

To bring this ambient lemma into scope, for a specific proof, or for an entire
module, you can use `broadcast use seq_contains_orig_elems_after_push;`.

Some of these broadcast-ed lemmas are available in the verus standard library `vstd`,
some as part of broadcast "groups", which combine a number of properties into a single
group name, which can be brought into scope with `broadcast use broadcast_group_name;`.
For example, the example above can all be automatically proved from `broadcast use vstd::seq_lib::group_seq_properties;`.
We are working on extending the discoverability of these groups in the standard library
documentation: they currently appear as regular functions.

## Experimental broadcast lemma usage information

You can use the `-V axiom-usage-info` experimental flag to obtain an overapproximation
of the broadcasted axioms and lemmas that were used in the verification of each function.
For large projects, use `--verify-only-module` and possibly `--verify-function` to limit the
amount of output.

As an example, using `-V axiom-usage-info` on [examples/broadcast_proof.rs](https://github.com/verus-lang/verus/blob/main/examples/broadcast_proof.rs) produces this information for the `increase_twice` function:

```
note: checking this function used these broadcasted lemmas and broadcast groups:
        - (group) broadcast_proof::multiple_broadcast_proof::Multiple::group_properties,
        - broadcast_proof::multiple_broadcast_proof::Multiple::lemma_add_aligned
   --> ../examples/broadcast_proof.rs:161:11
    |
161 |       proof fn increase_twice(
    |  ___________^
162 | |         p1: Multiple, v: Multiple, p2: Multiple)
    | |________________________________________________^
```

indicating that the `group_properties` group enabled the use of `lemma_add_aligned`, which was
likely used in the proof.