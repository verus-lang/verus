# Detecting Vacuous Proofs in Verus

## Overview

A proof is *vacuous* when it succeeds not because the conclusion follows from the assumptions, but because the assumptions themselves are contradictory. Any conclusion follows from a contradiction, so a vacuous proof provides no assurance that the code is correct.

Verus detects vacuous proofs using the SMT solver's *unsat core* feature, following the approach used in Dafny/Boogie. The key idea: after a proof succeeds, check whether the proof actually needed the goal. If the goal wasn't needed, the assumptions alone are contradictory.

## The Algorithm

When `-V check-vacuity` is enabled, Verus runs two SMT queries per function:

**Query 1: Normal verification** (unchanged). If it fails, report the error. If it succeeds, proceed to query 2.

**Query 2: Vacuity check.** This uses a modified WP (weakest precondition) encoding where every assumption and assertion gets a *tracking variable*:

- `assume H` becomes `(v ==> H) ==> rest` — the variable `v` gates the assumption
- `assert G` becomes `(a ∧ G) ∧ rest` — the variable `a` gates the goal
- Local axioms (from `requires`, trait bounds, type invariants) become `(v ==> axiom)` — also gated

Each tracking variable is declared as a boolean and asserted as true with a `:named` tag:

```smt
(declare-const v Bool)
(assert (! v :named vacuity$v))
```

The entire tracked WP is negated and checked for satisfiability. If unsat, the solver is asked for the *unsat core* — the subset of named assertions that were needed for the proof.

**The check:** If any assertion's tracking variable is NOT in the unsat core, that assertion was proved without needing the goal — the assumptions are contradictory.

## Why IMPLIES for Assumptions and AND for Assertions

The WP for `assume H; assert G` is `H ==> (G ∧ true)`. Assumptions appear in the antecedent (left of `==>`), assertions in the consequent (right). Negation preserves the antecedent and negates the consequent:

```
not(H ==> (G ∧ true)) = H ∧ ¬G
```

This asymmetry determines which encoding gives the solver freedom to exclude a tracking variable from the unsat core.

**Assumptions use IMPLIES** because they are in the antecedent. With tracking: `(v ==> H) ==> rest`. Negated: `(v ==> H) ∧ ...`. If `v` is free (dropped from the core), the solver sets `v = false`, making `v ==> H` trivially true — the assumption is disabled. The solver only keeps `v` when the assumption is genuinely needed.

**Assertions use AND** because they are in the consequent. With tracking: `H ==> ((a ∧ G) ∧ true)`. Negated: `H ∧ (¬a ∨ ¬G)`. If `a` is free (dropped from the core), the solver sets `a = false`, making `¬a` true — the goal is disabled. The solver only keeps `a` when the goal is genuinely needed.

**Using the wrong encoding fails.** Consider the vacuous example `requires x > 10, x < 5; ensures x == 42`:

- If assertions used IMPLIES (`a ==> G`), the negated formula would contain `a ∧ ¬G`. The negation of the implication forces `a = true` — the solver has no choice. The tracking variable is always needed, so it is always in the unsat core. Vacuity is undetectable.

- If assumptions used AND (`v ∧ H`), the negated formula would contain `¬v ∨ ¬H`. Setting `v = true` gives `¬H` — the assumption is *negated* instead of asserted. The assumption `x > 10` becomes `x ≤ 10`. The proof breaks entirely.

## Example 1: Contradictory Requires (Local Axioms)

```rust
proof fn bad(x: int)
    requires x > 10, x < 5,
    ensures x == 42,
{}
```

The AIR statement tree after lowering:

```
local axioms: (x > 10), (x < 5), fuel_defaults
assertion: assert (x == 42)
```

**Query 1 (normal verification):** The axioms `x > 10` and `x < 5` are asserted unconditionally. The negated WP `not(label ==> (x == 42))` is asserted. Z3 returns unsat — proof "succeeds."

**Query 2 (vacuity check):** In a fresh scope:

```smt
;; Tracked axioms (gated, named)
(declare-const v_ax0 Bool)
(assert (! v_ax0 :named vacuity$v_ax0))
(assert (=> v_ax0 (> x 10)))

(declare-const v_ax1 Bool)
(assert (! v_ax1 :named vacuity$v_ax1))
(assert (=> v_ax1 (< x 5)))

(declare-const v_ax2 Bool)
(assert (! v_ax2 :named vacuity$v_ax2))
(assert (=> v_ax2 fuel_defaults))

;; Tracked assert (AND encoding, named)
(declare-const a0 Bool)
(assert (! a0 :named vacuity$a0))

;; Negated tracked WP
(assert (not (and (and a0 (= x 42)) true)))

(check-sat)       ;; → unsat
(get-unsat-core)  ;; → (vacuity$v_ax0 vacuity$v_ax1)
```

The unsat core contains `vacuity$v_ax0` and `vacuity$v_ax1` (the contradictory requires) but NOT `vacuity$a0` (the assertion). The proof did not need the goal. **Vacuity detected.**

## Example 2: Consistent Proof with If-Then-Else

```rust
proof fn good(x: int)
    requires x > 0,
{
    if x > 10 {
        assert(x > 5);
    } else {
        assert(x <= 10);
    }
}
```

The AIR statement tree after lowering:

```
local axioms: (x > 0), fuel_defaults
assertion:
  Block([
    Snapshot(PRE),
    Switch([
      Block([Assume(x > 10), Assert(x > 5)]),
      Block([Assume(!(x > 10)), Assert(x <= 10)])
    ])
  ])
```

The tracked WP for the body (Switch produces a conjunction of both branches):

```
WP = ((v1 ==> x>10) ==> (a1 ∧ x>5))
   ∧ ((v2 ==> ¬(x>10)) ==> (a2 ∧ x≤10))
```

Where `v1`, `v2` track the branch conditions and `a1`, `a2` track the assertions.

**Query 2 (vacuity check):**

```smt
;; Tracked axiom: x > 0
(declare-const v_ax0 Bool)
(assert (! v_ax0 :named vacuity$v_ax0))
(assert (=> v_ax0 (> x 0)))

;; Tracking variables for body
(assert (! v1 :named vacuity$v1))     ;; assume(x > 10)
(assert (! a1 :named vacuity$a1))     ;; assert(x > 5)
(assert (! v2 :named vacuity$v2))     ;; assume(!(x > 10))
(assert (! a2 :named vacuity$a2))     ;; assert(x <= 10)

;; Negated tracked WP
(assert (not
  (and
    (=> (=> v1 (> x 10)) (and (and a1 (> x 5)) ...))
    (=> (=> v2 (not (> x 10))) (and (and a2 (<= x 10)) ...))
  )))

(check-sat)       ;; → unsat
(get-unsat-core)  ;; → (vacuity$v_ax0 vacuity$v1 vacuity$a1 vacuity$v2 vacuity$a2)
```

The unsat core includes BOTH `vacuity$a1` and `vacuity$a2` — both assertions were needed. The proof genuinely depends on the goals. **No vacuity.**

## Example 3: Contradictory external_body Postconditions

```rust
#[verifier::external_body]
proof fn magic(x: int) -> (r: int)
    ensures r > x, r < x,
{ unimplemented!() }

proof fn test() {
    let r = magic(5);
    assert(false);
}
```

Here the contradictory assumptions come from the call postconditions (inside the body, not local axioms). The tracked WP wraps the `assume(ens_magic(5, r))` with a tracking variable:

```smt
;; Tracked assume: postcondition of magic()
(assert (! v_post :named vacuity$v_post))

;; Tracked assert: assert(false)
(assert (! a0 :named vacuity$a0))

;; Negated tracked WP
(assert (not
  (=> (=> v_post (ens_magic 5 r))
      (and (and a0 false) ...))))

(check-sat)       ;; → unsat
(get-unsat-core)  ;; → (vacuity$v_post) — a0 is ABSENT
```

The postcondition `ens_magic(5, r)` encodes `r > 5 ∧ r < 5`, which is contradictory. Z3 does not need `a0`. **Vacuity detected.**

## Soundness

- **No false positives:** If the check reports vacuity, the assumptions truly are contradictory — the unsat core without the assertion label is still unsatisfiable.
- **Possible false negatives:** Z3's unsat cores are not guaranteed to be minimal. The solver might include an assertion label even when it is not needed. In practice this is rare.
