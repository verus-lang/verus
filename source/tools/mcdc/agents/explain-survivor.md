# Task EXPLAIN: why does a mutant survive?

Read `rules.md` and `mutants.md` first.

## Inputs

- A queue of mutant ids (from the launching prompt), each infected on the active path of at least one test
  and killed by none.
- For each mutant, the tests that reached and infected it (from the baseline of `scripts/mutrun.py`).

## Method, per mutant

1. Read the mutated code (60 lines around the mutant's line) and the before/after text in `mutants.tsv`.
2. Read the tests that reached and infected it.
3. Decide why none of them kills it, using mechanisms 1 to 6 of `mutants.md`.
4. Use at most 2 Verus runs per mutant, only to confirm a claim (for example: run an infecting test on
   build B with `MUTANT_ID=<id>` and compare with build A).

## Output

`explain.tsv` in your output directory, one row per mutant:
`id  mechanism  evidence  killing_test`

- `mechanism`: POLARITY-WEAKENING, POLARITY-STRENGTHENING, MASKED-BY-EARLIER-CHECK, REDUNDANT, NO-EFFECT,
  ORACLE-TOO-COARSE, NEEDS-COMBINATION, OTHER.
- `evidence`: file:line and one sentence (for REDUNDANT, where the same check is; for NEEDS-COMBINATION,
  with what).
- `killing_test`: what program would kill it ("a program that Verus must reject at <construct>", "a
  program that verifies only with <fact>"), or "none: equivalent" with the dead-branch argument of
  `rules.md`.

Final message: rows done, counts per mechanism, and any program whose verdict was unsound (BUG, with
control and runtime witness).
