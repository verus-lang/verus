# SMT solving and automation

Sometimes an assertion will fail even though it's true. At a high level, Verus
works by generating formulas called "verification conditions" from a program's
assertions and specifications (`requires` and `ensures` clauses); if these
verification conditions are always true, then all of the assertions and
specifications hold. The verification conditions are checked by an SMT solver
(Z3), and therefore Verus is limited by Z3's ability to prove generated
verification conditions.

This section walks through the reasons why a proof might fail.

The first reason why a proof might fail is that the statement is wrong! If
there is a bug in a specification or assertion, then we hope that Z3 will not
manage to prove it. We won't talk too much about this case in this document,
but it's important to keep this in mind when debugging proofs.

The core reason for verification failures is that proving the verification
conditions from Verus is an _undecidable_ task: there is no algorithm that can
prove general formulas true. In practice Z3 is good at proving even complex
formulas are true, but there are some features that lead to inconclusive
verification results.

**Quantifiers:** Proving theorems with quantifiers (`exists` and `forall`) is
in general undecidable. For Verus, we rely on Z3's pattern-based instantiation
of quantifiers ("triggers") to use and prove formulas with quantifiers. See the
section on [forall and triggers](forall.md) for more details.

**Opaque and closed functions:** Verification conditions by default hide the
bodies of opaque and closed functions; revealing those bodies might make
verification succeed, but Verus intentionally leaves this to the user to
improve performance and allow hiding where desired.

**Inductive invariants:** Reasoning about recursion (loops, recursive lemmas)
requires an inductive invariant, which Z3 cannot in general come up with.

**Extensional equality assertions:** If a theorem requires extensional equality
(eg, between sequences, maps, or spec functions), this typically requires
additional assertions in the proof. The key challenge is that there are many
possible sequence expressions (for example) in a program that Z3 could attempt
to prove are equal. For performance reasons Z3 cannot attempt to prove all
pairs of expressions equal, both because there are too many (including the
infinitely many _not_ in the program at all) and because each proof involves
quantifiers and is reasonably expensive. The result is that a proof may start
working if you add an equality assertion: the assertion explicitly asks Z3 to
prove and use an equality.
See [extensional equality](extensional_equality.md) for how to use the
extensional equality operators `=~=` and `=~~=`.

**Incomplete axioms:** The standard library includes datatypes like `Map` and
`Seq` that are implemented using axioms that describe their expected
properties. These axioms might be incomplete; there may be a property that you
intuitively expect a map or sequence to satisfy but which isn't implied by the
axioms, or which is implied but requires a proof by induction.
If you think this is the case, please open an issue or a pull request adding
the missing axiom.

**Slow proofs:** Z3 may be able to find a proof but it would simply take too
long. We limit how long Z3 runs (using its resource limit or "rlimit" feature
so that this limit is independent of how fast the computer is), and consider it
a failure if Z3 runs into this limit. The philosophy of Verus is that it's
better to improve solver performance than rely on a slow proof. [Improving SMT
performance]() talks more about what you can do to diagnose and fix poor
verification performance.
