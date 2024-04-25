# Adding Ambient Facts to the Proof Environment with `broadcast`

In a typical Verus project,
a developer might prove a fact 
(e.g., that reversing a sequence preserves its length)
in a proof function, e.g.,
```rust
pub proof fn seq_reverse_len<A>(s: Seq<A>)
    ensures
        reverse(s).len() == s.len(), 
{
  ...
}
```
To make use of this fact, the developer must explicitly invoke the proof function,
e.g.,
```rust
fn example(s: Seq<bool>) {
  let t = reverse(s);
  // assert(t.len() == s.len()); // FAILS
  seq_reverse(s);                // Adds the proof's fact to the proof environment
  assert(t.len() == s.len());    // SUCCEEDS
}
```
However, in some cases, a proof fact is so useful that a developer always
wants it to be in scope, without manually invoking the corresponding proof.
For example, the fact that an empty sequence's length is zero is so "obvious"
that most programmers will expect Verus to always know it.
This feature should be used with caution, however, as every extra ambient
fact slows the prover's overall performance.

Suppose that after considering the impact on the solver's performance, the
programmer decides to make the above fact about `reverse` ambient.  To do so,
they can add the `broadcast` modifier in the
definition of `seq_reverse_len`: `pub broadcast proof fn seq_reverse_len<A>(s: Seq<A>)`.
The effect is to introduce the following
quantified fact to the proof environment:
```rust
forall |s| reverse(s).len() == s.len()
```
Because this introduces a quantifier, Verus will typically ask you to
explicitly choose a trigger, e.g., by adding a `#[trigger]` annotation.
Hence, the final version of our example might look like this:
```rust
pub broadcast proof fn seq_reverse_len<A>(s: Seq<A>)
    ensures
        #[trigger] reverse(s).len() == s.len(), 
{
  ...
}
```

To bring this ambient lemma into scope, for a specific proof, or for an entire
module, you can use `broadcast use seq_reverse_len;`.

Some of these broadcast-ed lemmas are available in the verus standard library `vstd`,
some as part of broadcast "groups", which combine a number of properties into a single
group name, which can be brought into scope with `broadcast use broadcast_group_name;`.
We are working on extending the discoverablility of these groups in the standard library
documentation: they currently appear as regular functions.