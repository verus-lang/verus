# Mutation model and tools

Read `rules.md` first. `explain-survivor.md` and `propose-kill.md` use the terms and commands below.

## Terms

- **Mutant.** A small planted fault in the Verus source (vir, rust_verify, builtin_macros): delete a
  statement, skip a `return Err(..)`, force a condition true or false, negate a returned bool, shift a
  constant by one, replace `Some(x)` by `None`, swap an enum variant, and so on. One row of
  `$MCDC_MAP/mutants.tsv` per mutant: id, file, function, line range, operator, class, the decision that
  guards it, the static guard chain, and the text before and after.
- **Build A** (`$MCDC_BUILD_A`): original behavior. **Build B** (`$MCDC_BUILD_B`): same source, every
  mutant compiled in and off. `MUTANT_ID=N` switches mutant N on; `MUTANT_BITSET=FILE` switches on the set
  written by `mcdc mutgen --map $MCDC_MAP/mutants.tsv --id N --out FILE` (other selectors: `--ids`,
  `--file`, `--fn`, `--loc FILE:LINE`, `--class`, `--random SEED:RATE`, `--stdin`).
- **Guard stack and active path.** Every guarded body in a mutated file (then and else blocks, loop
  bodies, match arms) pushes (decision, outcome) on a thread-local stack while it runs; with
  `MUTANT_LOG=DIR` the process writes which mutation points ran under which stack. A mutant is on the
  active path of a test when the test's run reaches it with the test's target (decision, outcome) on the
  stack. A test is charged only for mutants on its active path.
- **Infected.** The mutant's code ran and its alternative differs from the original value or effect at
  least once (for a deleted statement or a skipped error return, reaching it is enough).
- **Killed.** With the mutant on, the run differs from the run without it on build B: exit status,
  verified and error counts, the set of error messages, the panic location, or the output of the compiled
  binary. A hang or panic does not count as a kill when the original run already panics.

## Commands

- `scripts/mutrun.py check TEST.rs --target D:I:O [--cap N]`: runs TEST on build B with no mutant and the path log,
  computes the mutants in the cone of the target (atom mutants of decision D, atom I; mutants guarded by
  (D, O) in the same function and, from earlier baseline logs, in callees), keeps those the run reached
  under the target guard and infected, runs TEST on build B under each, and prints the infected
  survivors with file, function, line and before/after text. `O` is 1 (T), 0 (F), a match arm index, or
  `*` for both sides. Without `--target`, the targets come from the `// target:` header.
- `scripts/mutrun.py vet TEST.rs`: check 1 on build A (the observed verdict matches `// expected:`, and a
  verifying program with a non-empty `fn main` runs cleanly when compiled); check 2 on build B (`check`).
  A disagreement in check 1 is a finding about Verus, not a test failure.

## Why an infected mutant on the path can survive

1. **Polarity.** A weakening mutant (drops an obligation or a check, skips an error) is detected only by a
   program that Verus must reject exactly at that obligation or check; a correct program verifies with or
   without it. A strengthening mutant (drops an assumption, an axiom, fuel, a definition) is detected only
   by a program that verifies only thanks to that fact.
2. **Masked by an earlier check.** The test is rejected by another check (unsupported feature, a mode
   error, a rustc error) before or regardless of the mutated code.
3. **Redundant.** The same check or fact is enforced elsewhere (cite file:line): the mutant is equivalent.
4. **No observable effect.** Diagnostic text, logging, profiling, caches, state never read again, an order
   that does not matter (sets, sums, fixpoints).
5. **Oracle too coarse.** The verdict stays "rejected" but the error moves or changes; only an exact
   comparison of messages and positions sees it.
6. **Needs a combination.** The mutated value matters only together with another condition or another
   mutant; name it.
