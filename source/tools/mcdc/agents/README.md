# Agent prompts for coverage and mutation search

These prompts drive coding agents that raise MC/DC coverage and mutation kills of the Verus verifier by
writing test programs, and that treat every program as a soundness probe. They assume a measurement pass
of `tools/mcdc` has been run (see `../README.md`): build A (`mcdc instrument`), build B (`mcdc mutate`),
the gap report `GAPS.tsv` from `tools/mcdc.sh`, and, for the mutation tasks, the baseline of
`scripts/mutrun.py`.

## Launching

Give the agent the task file and `rules.md` (and `mutants.md` for the mutation tasks), set the
environment variables `MCDC_BUILD_A`, `MCDC_BUILD_B` and `MCDC_MAP`, and add to the prompt:

- the assignment: files, decision ids, mutant ids or a seed list;
- an output directory the agent owns;
- the run command and limits for this machine (timeout per Verus run, how many runs in flight);
- the list of known issues not to report again, if any.

Several agents can work in parallel on disjoint assignments. Each writes only to its own output directory.
Merge their programs into the corpus after review, then re-run `tools/mcdc.sh` and `scripts/mutrun.py` to
measure them.

## Prompts

`rules.md`: shared by every prompt. Inputs, the test program header (`target`, `kills`, `expected`,
`verus-args`, `runtime`), the ground-truth rule (the compiled binary settles what a program does), how to
report a finding with a control and a runtime witness, and the dead-branch argument format (PINNED,
UNREACHABLE, COUPLED-INFEASIBLE, FEATURE-GATED, EQUIVALENT, OPEN).

`gap-target.md`: closes MC/DC gaps. Input: rows of `GAPS.tsv` for the assigned files. For each atom, the
agent writes a program that produces the missing evaluation, checks it with `tools/mcdc.sh delta`, and
writes an adversarial probe for each decision that protects a check, an obligation or an encoding choice.
Produces `corpus/`, `probes/`, `control/` and `COVERAGE.md` (a final class per atom).

`review.md`: tries to break dead-branch arguments written by other agents, by mechanical enumeration of
assignment sites and call paths, then programs for every site the argument misses. Produces `REVIEW.md`
with CONFIRMED, REFUTED, WEAKENED, CLOSED or STILL-OPEN per atom.

`mutants.md`: not a task. The mutation model (mutant, the two builds, guard stack and active path,
infected, killed), the `scripts/mutrun.py check` and `vet` commands, and the six reasons an infected
mutant survives.

`explain-survivor.md` (task EXPLAIN): for each surviving mutant on some test's active path, the agent
decides why no test kills it (polarity, masking, redundancy, no effect, coarse oracle, combination).
Produces `explain.tsv`.

`propose-kill.md` (task PROPOSE): for each polarity gap, the agent writes a test with the needed polarity
and validates it in three steps (expected verdict on build A with the binary agreeing, a different
outcome on build B under the mutant, the mutant reached on the path). Produces `kills/`, `propose.tsv`
and `findings/`.

`explore-rule.md`: seed-driven search over translation rules, without a coverage target. For each seed
(a rule, a pattern, three features), the agent writes a program whose claims are false if the rule
mistranslates its input. Produces `progs/`, `results.tsv`, `candidates/` and `crashes/`.
