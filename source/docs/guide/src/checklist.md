# Checklist: What to do when proofs go wrong

**A proof is failing and I don't expect it to. What's going wrong?**

 * Try running Verus with `--expand-errors` to get more specific information about what's failing.
 * Check Verus's output for `recommends`-failures and other notes.
 * Add more `assert` statements. This can either give you more information about what's failing, or even just fix the proof. See [this guide](./develop_proofs.md).
 * Are you using quantifiers? Make sure you understand [how triggers work](./forall.md).
 * Are you using nonlinear arithmetic? Try one of the strategies for [nonlinear arithmetic](./nonlinear.md).
 * Are you using bitwise arithmetic or `as`-truncation? Try [the bit_vector solver](./bitvec.md).
 * Are you relying on the equality of a container type (like `Seq` or `Map`)? Try [extensional equality](./extensional_equality.md).
 * Are you using a recursive function? Make sure you understand [how fuel works](./recursion.md#fuel-and-reasoning-about-recursive-functions).

**The verifier says "rlimit exceeded". What can I do?**

 * Try [the quantifier profiler](./profiling.md) to identify a problematic trigger-pattern.
 * Try [breaking the proof into pieces](./breaking_proofs_into_pieces.md).
 * Try [increasing the `rlimit`](./reference-attributes.md#verifierrlimitn-and-verifierrlimitinfinity). Sometimes a proof really is just kind of big and you want Verus to spend a little more effort on it.

**My proof is "flaky": it sometimes works, but then I change something unrelated, and it breaks.**

 * Try adding `#[verifier::spinoff_prover]` to the function. This can make it a little more stable.
 * Try [breaking the proof into pieces](./breaking_proofs_into_pieces.md).
