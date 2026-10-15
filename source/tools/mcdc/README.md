# mcdc: MC/DC coverage and mutation testing for the Verus verifier

`mcdc` rewrites the source of the verifier crates (`vir`, `rust_verify`, `air`, `builtin_macros`,
`state_machines_macros`) in a scratch worktree. It instruments every boolean decision so that each
evaluation records which conditions were evaluated and their values (MC/DC). It can also plant
mutants in a list of files as mutant schemata: every mutation site reads one activation bit from a
bitset loaded at startup, so one build holds all mutants and a run switches any subset on. Each run
can log the path conditions (the stack of enclosing branch outcomes) under which every site
executed. Details of every command, format and limit are in [docs/REFERENCE.md](docs/REFERENCE.md).

## MC/DC

A decision is a boolean expression built from `&&` and `||`; its leaves are atoms. An atom is
MC/DC-covered when two recorded evaluations differ in the decision outcome and in that atom, and
every other atom is equal or not evaluated in one of them (unique-cause MC/DC with short-circuit
don't-cares). For `a && b`, three evaluations cover both atoms:

| evaluation | a | b | outcome |
|---|---|---|---|
| E1 | T | T | T |
| E2 | T | F | F |
| E3 | F | - | F |

E1/E3 is the independence pair of `a`, E1/E2 the pair of `b`. Branch coverage is complete with E1
and E3 alone, while `b` is never shown to matter. `mcdc report` gives MC/DC, condition and
decision coverage; `mcdc gaps` lists every atom without a pair and the evaluation that would
complete it.

## Mutation

`mcdc mutate` plants mutants in the files of [mutate-files.txt](mutate-files.txt) (23 files of
mode checking, well-formedness, lowering to SST and AIR, pruning, recursion checks, the frontend
and `builtin_macros/src/syntax.rs`). At upstream 6d85179 it plants 19,725 mutants:

| class | operators | mutants |
|---|---|---:|
| condition | cond-true 2,645, cond-false 2,645, cond-negate 2,116, decision-negate 841, and-or-swap 644, while-false 12 | 8,903 |
| datapath-delete | delete-stmt 3,027, skip-err-return 270 | 3,297 |
| datapath-const | const-plus1 1,041, const-minus1 1,041, index-plus1 203, index-minus1 203 | 2,488 |
| container | container-iter-rev 747, container-len-plus1 396, container-len-minus1 396, container-contains-negate 58, container-first-last 21, container-insert-absent 21, container-is-empty-negate 10, container-retain-negate 6, container-remove-absent 2 | 1,657 |
| enum | enum-variant 1,026 | 1,026 |
| option | option-some-none 757, option-get-none 148, option-unwrap-or-default 8 | 913 |
| datapath-return | ret-true 179, ret-negate 179, ret-false 179 | 537 |
| datapath-error | drop-try 379, err-to-ok 18 | 397 |
| datapath-compare | rel-boundary 175, eq-flip 122 | 297 |
| datapath-vec | vec-remove 210 | 210 |
| total | | 19,725 |

Counts: `build.sh mutants` (last `mcdc mutate` output in `OUT/map`, `cut -f8 mutants.tsv | sort | uniq -c`).
`mcdc mutgen` selects mutants by id, file, function, line, operator class or a seeded random sample
and writes the bitset; the verifier reads it from `MUTANT_BITSET`. A mutant is killed by a test when
the observed outcome under the mutant differs from the outcome without it: verdict, error messages
and their positions, or the output of the compiled binary. A test is scored only on the mutants that
lie on its active target path: the mutants of its target decision and the mutants its run reaches
with the target outcome on the guard stack.

## The loop

Coverage and mutation drive the generation of new tests:

```
measure ──> target ──> generate ──> validate (2 gates) ──> keep + minimize
   ^                                                             |
   └─────────────────────────────────────────────────────────────┘
```

1. **Measure.** The MC/DC report lists the atom outcomes no test produces. The mutation pass lists
   the surviving mutants on covered paths, with the path conditions under which each test reached
   them.
2. **Target.** Either an uncovered atom outcome, or a survivor whose mechanism is a polarity gap:
   no test has the polarity the mutant needs. A weakening mutant (a check removed, an error
   skipped) needs a program that Verus must reject at that check; a strengthening mutant (a fact
   dropped from the encoding) needs a program that verifies only thanks to the removed fact.
3. **Generate.** An agent writes a Verus program that drives the decision to that outcome, or has
   that polarity, with its expected verdict in a header.
4. **Validate, gate 1 (ground truth).** On the build without mutants the program gives its expected
   verdict, and for exec code the compiled binary agrees with it (a verified program whose binary
   fails is a finding about Verus, not a test).
5. **Validate, gate 2 (kill).** On the build with mutants, the targeted mutants change the outcome.
6. **Keep and minimize.** Only programs that pass both gates are kept; a weighted set cover then
   selects the smallest set of tests that keeps every kill.
7. **Dead branches.** An atom outcome that remains uncovered gets a written argument (pinned,
   unreachable, infeasible combination, feature-gated or equivalent), which a reviewer checks.

Both signals are needed. Coverage alone accepts a test that reaches a branch and checks nothing: in
the campaign that produced the tests of the companion PR, 31 tests that closed
MC/DC gaps killed no mutant on their target path. Kill rate alone misses branches that no test
reaches, because a mutant that no test executes cannot be killed or reported as a survivor.

## Results

Coverage at upstream 6d85179 (817 decisions, 1949 atoms), from `tools/mcdc.sh` runs with `--test`
lists, merged with `mcdc compact` and reported with `mcdc report` and `mcdc gaps`:

| test set | MC/DC | condition | decision outcomes |
|---|---:|---:|---:|
| upstream suite (vstd build + rust_verify_test) | 54.1% (1054 atoms) | 58.2% | 78.2% |
| upstream + the 220 tests of the companion PR | 64.8% (1262) | 67.0% | 84.3% |
| upstream + all 463 campaign programs (not committed) | 85.7% (1671) | 86.9% | 94.8% |

The 220 tests are the mutation-minimal subset of the campaign programs: they were selected to keep
every mutant kill, not for coverage. The 85.7% needs the full campaign program set, which is not part
of this change. The test files and the dead-branch arguments are in the companion PR. 210 of the
remaining atoms have a dead-branch argument (unreachable, pinned or an infeasible combination); excluding the 209 argued infeasible, MC/DC is 72.5% with the 220 tests and
96.0% with all campaign programs.

| mutation | value | source |
|---|---:|---|
| mutants planted at 6d85179 | 19,725 | `build.sh mutants` (count in `OUT/map/mutants.tsv`) |
| killed by the upstream suite | TO BE MEASURED at 6d85179 (campaign at 1d72e6d: 1,979 of the 2,753 mutants any program killed) | `mutrun.py mutants` + `report` over the upstream programs |
| killed by the 220 new tests and by no upstream test | TO BE MEASURED at 6d85179 (campaign at 1d72e6d: 719) | the same with the new tests, then `cover.py --free` |
| tests kept by the cover | 220 | `cover.py` on the campaign kill matrix (measured at 1d72e6d; lower bound 220) |


## Running a measurement pass

From `source/`, with `vargo` and `z3` set up as for a normal build:

```
./tools/mcdc.sh                                         # build A, vstd + rust_verify_test, MC/DC report and GAPS
tools/mcdc/scripts/build.sh mutants out-B               # build B: MC/DC + mutants (disable loop)
export MCDC_BUILD_A=mcdc-out/build/source/target-verus/release/verus
export MCDC_BUILD_B=out-B/build/source/target-verus/release/verus MCDC_MAP=out-B/map
tools/mcdc/scripts/mutrun.py tests PROGRAM_DIR && tools/mcdc/scripts/mutrun.py baseline
target-verus/release/mcdc mutgen --map out-B/map/mutants.tsv --class datapath --random 1:0.05 --list > ids.txt
tools/mcdc/scripts/mutrun.py mutants ids.txt results.jsonl && tools/mcdc/scripts/mutrun.py report results.jsonl
```

## Agents and reference

- [agents/](agents/README.md): prompts for the agent search that raises coverage and kills.
  `gap-target.md` closes MC/DC gaps; `propose-kill.md` writes a test that kills a survivor;
  `explain-survivor.md` classifies why a mutant survives; `review.md` checks dead-branch arguments;
  `explore-rule.md` searches translation rules from seed programs; `rules.md` and `mutants.md` are
  shared by all of them.
- [docs/REFERENCE.md](docs/REFERENCE.md): commands, file formats (manifest, records, mutants.tsv,
  bitset, path log), the scripts, the rewriting, cost and limits.
