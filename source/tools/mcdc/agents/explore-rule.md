# Explore translation rules from random seeds

Read `rules.md` first. You search for soundness bugs over a long session, one seed at a time. Diversity
matters: follow your seeds and do not drift to familiar cases.

## Inputs

- A seed list from the launching prompt. Each seed is `{rule, fn, pattern, features}`: a match arm or
  decision (file:line) in a translation function `fn` (for example in `rust_to_vir_expr.rs`,
  `ast_to_sst.rs`, `sst_to_air.rs`, `modes.rs`), a syntactic pattern, and three language features to
  combine with it. A seed list can be drawn from the decisions of the MC/DC manifest, weighted toward
  decisions with uncovered atoms in `GAPS.tsv`.
- A list of known issues (from the launching prompt) that must not be reported as new.

## Method, per seed

1. Read the rule (about 80 lines around `rule`) and the code it calls. Write in one or two lines what the
   rule assumes about its input and what it produces.
2. Imagine an input that stresses that assumption and combines the rule with all three features.
3. Write a program (up to 80 lines) whose claims are false if the rule mistranslates that input: a proof of
   `false`, or an exec function with an `ensures` that the real Rust semantics violate. Header:
   `// seed: <n>`, `// rule: <file:line>`, `// hypothesis: <one line>`, and the `expected` line of `rules.md`.
4. Run Verus (build A). If the program verifies and has exec code, apply the ground-truth rule.
5. If the program fails for a syntax or setup reason, fix it (at most 2 fixes) so that the hypothesis is
   tested; record "untested" otherwise.

A CANDIDATE is a program Verus accepts while its claim is false (a proof of `false`, a binary that
contradicts a verified fact, a verified exec function that panics). Minimize it and write a control that
Verus rejects.

## Syntax notes

- Labeled blocks (`'a: { ... break 'a v; }`) are not supported; `loop` with a value `break` needs loop
  isolation.
- `decreases` takes a list (`decreases a, b`), not a tuple.
- Verus reports only the first failing assertion per function: put each false claim in its own function.
- Ghost arithmetic on machine integers is typed as `int`; use exec code or casts to reach machine-integer
  rules.
- Not bugs (trusted by design): `external_body` items whose specification is wrong, `when_used_as_spec`
  mismatches, Euclidean spec division against truncating exec division.

## Output

In your output directory: `progs/` (every program run), `results.tsv` (seed, rule, hypothesis, expected,
observed results line, runtime output, status: rejected-as-expected, verified-as-expected, CANDIDATE,
crash, untested, incompleteness), `candidates/` (reproducer and control), `crashes/` (program and first
panic line). Final message: seeds done, counts per status, and each candidate (file, claim, results line,
runtime output).
