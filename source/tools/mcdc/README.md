# mcdc: MC/DC coverage and mutation testing for the Verus verifier

`mcdc` rewrites the source of the verifier crates (`vir`, `rust_verify`, `air`, `builtin_macros`,
`state_machines_macros`) in a scratch worktree. It instruments every boolean decision so that each
evaluation records which conditions were evaluated and their values (MC/DC). It can also plant
mutants, in every file or in a list of files, as mutant schemata in the same build: every mutation
site reads one activation bit from a bitset loaded at startup, so one build holds all mutants and a
run switches any subset on. Each run
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

`mcdc mutate` plants mutants in every file of the instrumented crates, in the same build as the
MC/DC instrumentation: a mutated file keeps the MC/DC instrumentation of build A, so one build gives
the MC/DC records of build A and switchable mutants. `--files` restricts the mutated files;
[mutate-files.txt](mutate-files.txt) lists 23 priority files (mode checking, well-formedness,
lowering to SST and AIR, pruning, recursion checks, the frontend and
`builtin_macros/src/syntax.rs`). At upstream 09d09ee2 it plants 38,128 mutants in 160 of the 171
files of the five crates, 19,804 of them in the 23 priority files:

| class | operators (all files) | all files | priority files |
|---|---|---:|---:|
| condition | cond-true 5,017, cond-false 5,017, cond-negate 3,942, decision-negate 1,548, and-or-swap 1,084, while-false 38 | 16,646 | 8,977 |
| datapath-delete | delete-stmt 5,785, skip-err-return 460 | 6,245 | 3,305 |
| datapath-const | const-plus1 2,291, const-minus1 2,291, index-plus1 366, index-minus1 366 | 5,314 | 2,494 |
| container | container-iter-rev 1,532, container-len-plus1 802, container-len-minus1 802, container-contains-negate 112, container-first-last 89, container-insert-absent 36, container-is-empty-negate 34, container-retain-negate 11, container-remove-absent 6 | 3,424 | 1,653 |
| option | option-some-none 1,503, option-get-none 288, option-unwrap-or-default 32 | 1,823 | 894 |
| datapath-return | ret-true 438, ret-negate 438, ret-false 438 | 1,314 | 540 |
| enum | enum-variant 1,183 | 1,183 | 1,036 |
| datapath-error | drop-try 964, err-to-ok 137 | 1,101 | 398 |
| datapath-compare | rel-boundary 359, eq-flip 212 | 571 | 297 |
| datapath-vec | vec-remove 507 | 507 | 210 |
| total | | 38,128 | 19,804 |

Counts: `tools/mcdc/scripts/build.sh mutants OUT` (no `FILES`), then `cut -f8 OUT/map/mutants.tsv |
tail -n +3 | sort | uniq -c` (`-f7` for operators); the priority column keeps the rows whose `file`
column is in mutate-files.txt. Per crate: vir 15,681, rust_verify 10,878, builtin_macros 5,764,
air 3,006, state_machines_macros 2,799.

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

Coverage was not measured again at 09d09ee2. At that commit `mcdc instrument` finds 818 decisions
and 1951 atoms: the let-chain in a match guard that was skipped before is now instrumented, and
`vir/src/resolution_inference.rs` changed upstream.

**Mutation kills at upstream 09d09ee2.** The measurement covers the 19,804 mutants of the 23
priority files, in the build that plants all 38,128. The oracle is the rust_verify_test result: a
mutant is killed when a test that passes without it fails, crashes or times out under it. A test is
run on a mutant only if its baseline run infected the mutant (the mutation site ran and the mutant
would have changed a value or effect there), fastest test first, until one fails. Reach and
infection come from one baseline run of every test, so the not-reached and not-infected counts are
exact. Running every infected mutant was too long for the time available (the infected tests of a
mutant number up to 4,766), so the killed and survived counts are estimated from a seeded
uniform random sample of the priority-file mutants (`mcdc mutgen --random 20261015:0.05`, 934
mutants, 805 of them infected), each given at most 120 s of test runs; a mutant still alive when the
next batch of tests would exceed that is survived-capped. The estimates scale the sample fractions
of the infected mutants to the exact infected count, with 95% Wilson intervals.

| priority-file mutants (19,804) | upstream suite (4,778 tests) | upstream + the 220 tests |
|---|---:|---:|
| not reached by any test (exact) | 1,472 | 1,207 |
| reached, not infected (exact) | 1,137 | 993 |
| infected (exact) | 17,195 | 17,604 |
| killed (sample) | 633 of 805, 78.6% | 665 of 826, 80.5% |
| killed (estimate) | 13,521 [13,011, 13,984] | 14,173 [13,673, 14,623] |
| survived, every infecting test run (sample) | 45 of 805, 5.6% | 47 of 826, 5.7% |
| survived-capped (sample) | 127 of 805, 15.8% | 114 of 826, 13.8% |

The 220 tests kill 32 of the 934 sampled mutants that no upstream test kills (3.4%, about 679
[483, 950] of the 19,804). Per class, in the sample, upstream suite:

| class | sampled | killed | survived | survived-capped | not infected | not reached |
|---|---:|---:|---:|---:|---:|---:|
| condition | 432 | 311 | 15 | 47 | 40 | 19 |
| datapath-delete | 151 | 99 | 5 | 20 | 0 | 27 |
| datapath-const | 104 | 77 | 5 | 14 | 0 | 8 |
| container | 85 | 38 | 13 | 28 | 3 | 3 |
| option | 45 | 36 | 2 | 4 | 0 | 3 |
| enum | 38 | 21 | 4 | 9 | 0 | 4 |
| datapath-return | 31 | 19 | 0 | 5 | 3 | 4 |
| datapath-error | 20 | 9 | 0 | 0 | 8 | 3 |
| datapath-compare | 16 | 13 | 1 | 0 | 1 | 1 |
| datapath-vec | 12 | 10 | 0 | 0 | 0 | 2 |

container-iter-rev accounts for 12 of the 45 survivors and 22 of the 127 capped mutants, as
expected for an operator that mostly yields equivalent mutants. The per-operator table is printed
by `rvt-report`. Regenerate, from `source/` with build B in `out-B` (the 220 tests copied from the
companion PR into `out-B/build/source/rust_verify_test/tests/` and all tests built):

```
M="tools/mcdc/scripts/mutrun.py --map out-B/map --jobs 4"
$M rvt-baseline out-B/build/source                     # 4,998 tests, one per process
target-verus/release/mcdc mutgen --map out-B/map/mutants.tsv $(sed 's/^/--file /' tools/mcdc/mutate-files.txt) \
    --random 20261015:0.05 --list > sample.txt
$M rvt-mutants out-B/build/source sample.txt up.jsonl --tests '^(?!mutants_)' --budget 120
$M rvt-report sample.txt up.jsonl --tests '^(?!mutants_)'           # upstream column
$M rvt-mutants out-B/build/source left.txt new.jsonl --tests '^mutants_'   # left.txt: sample ids not killed
$M rvt-report sample.txt up.jsonl new.jsonl                         # second column
mutgen ... (no --random) > prio.txt; $M rvt-report prio.txt [--tests '^(?!mutants_)']   # exact counts
```

The campaign that produced the 220 tests ran at 1d72e6d with a different oracle (the verdict and
messages of standalone programs): there, 1,979 of the 2,753 mutants any program killed were killed
by programs harvested from the upstream suite, and the 220 tests were selected by `cover.py` to keep
the other 719 kills (lower bound 220).

## Running a measurement pass

From `source/`, with `vargo` and `z3` set up as for a normal build:

```
./tools/mcdc.sh                                         # build A, vstd + rust_verify_test, MC/DC report and GAPS
tools/mcdc/scripts/build.sh mutants out-B               # build B: MC/DC + mutants in every file (disable loop)
export MCDC_BUILD_A=mcdc-out/build/source/target-verus/release/verus
export MCDC_BUILD_B=out-B/build/source/target-verus/release/verus MCDC_MAP=out-B/map
# test programs with `// expected:` headers
tools/mcdc/scripts/mutrun.py tests PROGRAM_DIR && tools/mcdc/scripts/mutrun.py baseline
target-verus/release/mcdc mutgen --map out-B/map/mutants.tsv --class datapath --random 1:0.05 --list > ids.txt
tools/mcdc/scripts/mutrun.py mutants ids.txt results.jsonl && tools/mcdc/scripts/mutrun.py report results.jsonl
# the rust_verify_test suite (tests built in out-B/build/source with `vargo test --release -p rust_verify_test --no-run`)
tools/mcdc/scripts/mutrun.py --jobs 4 rvt-baseline out-B/build/source
tools/mcdc/scripts/mutrun.py --jobs 4 rvt-mutants out-B/build/source ids.txt kills.jsonl --budget 120
tools/mcdc/scripts/mutrun.py rvt-report ids.txt kills.jsonl
```

## Agents and reference

- [agents/](agents/README.md): prompts for the agent search that raises coverage and kills.
  `gap-target.md` closes MC/DC gaps; `propose-kill.md` writes a test that kills a survivor;
  `explain-survivor.md` classifies why a mutant survives; `review.md` checks dead-branch arguments;
  `explore-rule.md` searches translation rules from seed programs; `rules.md` and `mutants.md` are
  shared by all of them.
- [docs/REFERENCE.md](docs/REFERENCE.md): commands, file formats (manifest, records, mutants.tsv,
  bitset, path log), the scripts, the rewriting, cost and limits.
