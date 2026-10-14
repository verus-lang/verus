# mcdc: MC/DC coverage of the Verus verifier by its test suite

`mcdc` measures modified condition/decision coverage (MC/DC) of the verifier crates (`vir`,
`rust_verify`, `air`, `builtin_macros`, `state_machines_macros`) by the vstd build and the
`rust_verify_test` suite. It rewrites the crates' source so that every evaluation of a boolean
decision records which of its conditions were evaluated and their values, then computes the
coverage and, for every condition without coverage, the pair of evaluations a new test would
have to produce. It complements `tools/coverage.sh` (line coverage); it does not replace it.

## What MC/DC measures

A compound condition such as `a && (b || c)` encodes several distinct reasons for taking the
branch: `a` with `b`, or `a` with `c`. Each atom is one ingredient of a reason. Taking the branch
once, or a thousand times for the same reason, does not show that every reason was exercised, or
that every atom is needed. MC/DC asks, for each atom, for a recorded pair of evaluations in which
changing that atom alone changes the branch taken.

- A **decision** is a maximal boolean expression built from `&&` and `||` (through parentheses
  and `!`), in any position: `if` and `while` conditions, match guards, `let` initializers,
  `return` values, closure bodies, function arguments.
- A **condition** (here also called an **atom**) is a leaf of that expression: an operand that is
  not itself built from `&&`, `||` or `!` over such operands. `!x` with `x` a leaf is one atom.
- An **independence pair** for atom `i` is two recorded evaluations of the decision that have
  different outcomes, in which atom `i` is evaluated with different values, and in which every
  other atom either has the same value in both or is not evaluated in at least one of them.
  Atom `i` is MC/DC-covered when the recorded evaluations contain such a pair: the tests then
  show that atom `i` alone changes the outcome.
- **Short-circuit don't-care**: with `a && b`, the evaluation `a = false` does not evaluate `b`.
  An atom that is not evaluated in one of the two evaluations does not count as a difference.
- The criterion is **unique-cause MC/DC with short-circuit don't-cares** (the clang/LLVM
  definition, as in clang's `-fcoverage-mcdc` report). It is stricter than **masking MC/DC**
  (DO-178C, CAST-6), which also accepts a pair in which another evaluated atom changes when
  that change cannot affect the outcome. Every pair this tool accepts is also a masking pair, so
  the reported MC/DC percentage is a lower bound on masking MC/DC. Example: for
  `(a && b) || c`, the evaluations `a=T b=F c=T` (outcome true) and `a=F c=F` (outcome false)
  show `c` under masking MC/DC, because `a && b` is false in both; this tool does not count
  them, because `a` changes.
- The report also gives **condition coverage** (each atom observed both true and false) and
  **decision coverage** (both outcomes observed).

## Why this matters for Verus

Verus itself is not verified. Its soundness rests on checks such as the mode checks in
`vir/src/modes.rs`, the well-formedness checks in `vir/src/well_formed.rs` and the erasure in
`rust_verify/src/erase.rs` giving the right answer in every combination of their conditions. An
atom without an independence pair is a condition that no test shows to matter: it could be
wrong, inverted or redundant and every test would still pass. Line and branch coverage do not
report this, because they count each line or each outcome once, whatever the atom values were.

## Worked example: `vir/src/modes.rs:1434`

```rust
if ctxt.check_ghost_blocks
    && matches!(typing.block_ghostness, Ghost::Exec)
    && idx_mode != Mode::Exec
{
    return Err(error(&place.span, format!("cannot use {idx_mode}-mode expression in executable context")));
}
```

This is the VIR mode check that rejects a spec or proof index expression (`a[i]` with `i` ghost)
in exec code outside a ghost block. The atoms are `a`: the function is subject to ghost-block
checking (`check_ghost_blocks` is the function's `uses_ghost_blocks` attribute, true for
functions written inside `verus!`, modes.rs:4091); `b`: the place is outside a ghost block; `c`:
the index is not an exec value. With short-circuiting, four
evaluations are possible (`-` means not evaluated):

| evaluation | a | b | c | outcome |
|---|---|---|---|---|
| E1 | T | T | T | T (error) |
| E2 | F | - | - | F |
| E3 | T | F | - | F |
| E4 | T | T | F | F |

The independence pairs are E1/E2 for `a`, E1/E3 for `b` and E1/E4 for `c`. Full MC/DC of this
decision needs all four evaluations; a decision of n atoms joined by `&&` needs n + 1.

The vstd build and the full suite at 6d85179 record only E4 for this decision: MC/DC 0 of 3.
Line coverage reports that the `return Err` line never ran. One new test that reaches E1 makes
line coverage and branch coverage of this `if` complete, and with E4 it shows `c`; `a` and `b`
still have no pair, because no test evaluates the decision with `check_ghost_blocks` false or
outside exec code. MC/DC reports those two missing evaluations.

The pair for `a` is the informative one. `a = false` is the configuration in which this check,
and every other `check_ghost_blocks && ...` check in modes.rs, is switched off: a
`#[verifier::verify]` function written outside `verus!`. That configuration is where
verus-lang/verus#3171 (shape 3) was found: exec code there can use a spec value, for example as
an index, and Verus accepts it. The suite shows neither the error outcome of this check nor that
`check_ghost_blocks` matters to it.

Branch coverage can be complete while MC/DC is not. At `vir/src/modes.rs:1930`,
`ctxt.check_ghost_blocks && typing.block_ghostness == Ghost::Exec` ("cannot call spec function
from exec mode") has both outcomes in the suite: the recorded evaluations are `TT=>T` and
`TF=>F`. The first atom is true in every recorded evaluation, so no test shows that it is
needed: a mutation that deletes it changes no recorded outcome.

## Baseline

Baseline at 6d85179 (vstd build and full `rust_verify_test` suite, `tools/mcdc.sh` with
`JOBS=3`), per crate:

| crate | decisions | reached | full_mcdc | atoms | mcdc_atoms | mcdc | cond_atoms | cond | dec_outcomes | dec |
|---|---|---|---|---|---|---|---|---|---|---|
| air | 62 | 47 | 7 | 154 | 36 | 23.4% | 38 | 24.7% | 67 | 54.0% |
| builtin_macros | 107 | 99 | 34 | 297 | 131 | 44.1% | 148 | 49.8% | 165 | 77.1% |
| rust_verify | 256 | 235 | 101 | 584 | 291 | 49.8% | 317 | 54.3% | 375 | 73.2% |
| state_machines_macros | 41 | 40 | 30 | 98 | 64 | 65.3% | 67 | 68.4% | 72 | 87.8% |
| vir | 351 | 336 | 195 | 816 | 532 | 65.2% | 565 | 69.2% | 599 | 85.3% |
| PRIORITY FILES | 473 | 456 | 227 | 1130 | 664 | 58.8% | 725 | 64.2% | 770 | 81.4% |
| ALL | 817 | 757 | 367 | 1949 | 1054 | 54.1% | 1135 | 58.2% | 1278 | 78.2% |

Columns: `decisions` instrumented; `reached` evaluated at least once; `full_mcdc` decisions
with every atom covered; `mcdc_atoms`/`mcdc` atoms with an independence pair; `cond_atoms`/`cond`
atoms observed true and false; `dec_outcomes`/`dec` outcomes observed out of 2 per decision.
`PRIORITY FILES` totals the files that decide what Verus accepts (mode checking,
well-formedness, erasure, lowering to SST and AIR, `builtin_macros/src/syntax.rs`; the list is
`PRIORITY` in `src/analyze/mod.rs`).

450 decisions have at least one atom without a pair (895 atoms). The 17 top-ranked are all
`ctxt.check_ghost_blocks && typing.block_ghostness ...` checks in `vir/src/modes.rs`. 15 of
them never take the error outcome in the suite, and 14 of those 15 are the
`block_ghostness == Ghost::Exec` checks that reject spec or proof constructs (spec function
calls, `forall`, `choose`, `assert ... by`, spec-mode `if` conditions, ghost variable
declarations) in exec code outside a ghost block. A reading of `builtin_macros/src/syntax.rs`
suggests why: the `verus!` macro wraps these constructs in ghost blocks or rejects them before
VIR mode checking runs, so the suite tests the macro and not these checks. That is an inference
from the code, not a measurement; a test that reaches one of these checks without the macro's
help settles it.

In a separate experiment on the earlier commit 1d72e6d (the programs are not part of this
change), 211 programs written to close GAPS entries, run one at a time on the instrumented build
with their records added to the baseline, raised MC/DC from 54.1% (1052 of 1945 atoms) to 70.5%
overall and from 58.8% to 78.5% on the priority
files. Some of them reach the error outcome of modes.rs:1434 inside `verus!`, by indexing with the
result of an exec function that returns a `tracked` value. These numbers show how the tool was
used; they do not measure its accuracy.

## Running

From `source/`:

```
./tools/mcdc.sh                       # vstd build + whole rust_verify_test suite
./tools/mcdc.sh --test modes          # args pass to `vargo test`
./tools/mcdc.sh delta prog.rs [ARGS]  # what one program adds to the last full-suite run
./tools/mcdc.sh clean                 # remove the instrumented worktree and raw records
```

Environment variables, as in `coverage.sh`: `JOBS` (concurrent tests and nested build jobs,
default 4) and `OUT_DIR` (default `mcdc-out/`). `VERUS_Z3_PATH` defaults to `source/z3`.

The script never rewrites the checkout it runs from. The first run creates a detached git
worktree of `HEAD` in `$OUT_DIR/build`, applies the uncommitted changes to tracked files
(`git diff HEAD`; untracked files are not copied), runs `mcdc instrument --in-place` on that
worktree, and builds it with `vargo build --release`, which also verifies vstd with the
instrumented verifier. Later runs reuse the worktree and its build; run `clean` to measure new
source changes. The tests run with `vargo test --release -p rust_verify_test --no-fail-fast`
plus the given arguments. Every instrumented process writes its records to its own file under
`$OUT_DIR/records/`.

Outputs in `$OUT_DIR`:

- `manifest.jsonl`: one JSON object per decision: id, file, line, column, position kind,
  enclosing fn, structure over atom indices (for example `((0&&1)||!2)`), decision text, atom
  texts, and the code the decision guards.
- `records.bin`: distinct records of this run: the tests, plus the records of the vstd
  verification during `vargo build` (kept in `records/vstd/` across runs until `clean`).
  `baseline.bin`: a copy, written only by a run without test arguments; `delta` uses it.
- `report/summary.md` (the tables above, plus one line per priority file),
  `report/per-file.tsv`, `report/decisions.tsv` (one line per decision).
- `GAPS.md` (first 400 decisions with uncovered atoms, ranked) and `GAPS.tsv` (every uncovered
  atom).

The `mcdc` binary can also run each step by hand (`mcdc --help`):

```
mcdc instrument SOURCE_DIR (--out DIR | --in-place) [--manifest FILE] [--crates a,b,...]
mcdc report MANIFEST DATA... --out DIR
mcdc gaps MANIFEST DATA... --out DIR [--hints FILE]
mcdc delta MANIFEST BASE NEW...
mcdc compact OUT DATA...
```

`instrument --out DIR` copies `SOURCE_DIR` (without `target/`, `target-verus/`, `.verus-log/`
and `.git/`) and rewrites the copy; it refuses to run on files that are already instrumented.
The copy is meant for reading the rewritten code; building needs the git metadata, which is why
`mcdc.sh` uses a worktree.

## Reading GAPS

Each GAPS entry names a decision, its MC/DC count, the outcomes seen, and for each uncovered
atom a pair in this notation: one letter per atom in source order, `T` true, `F` false, `-` not
evaluated, then `=>` and the outcome. For modes.rs:1434 the entry for atom 1 is
`TTT=>T vs TF-=>F`, new vector needed `both`: neither evaluation is recorded. For atom 2 the
pair is `TTT=>T vs TTF=>F` and the new vector needed is `TTT=>T`, because `TTF=>F` is recorded:
one test that reaches the error covers atom 2. The pair is computed from the decision structure
alone (up to 18 atoms) and prefers a pair with one side already recorded, then the pair with the
fewest evaluated atoms.

The ranking adds weights for words in the decision and its guarded code that indicate a
soundness-relevant check (`Err(`, `error(`, `ghost`, `Mode::`, `erase`, `requires`, ...), a
per-file weight, +10 for priority files, and -3 for decisions never reached (line coverage
already reports those). `--hints FILE` replaces the generated hint of an entry with a hand-written
one (`file:line<TAB>text`).

`delta` prints one line per decision reached for the first time (`NEW-DECISION`), new outcome
(`NEW-OUTCOME`), atom newly observed both true and false (`NEW-COND`) and atom newly MC/DC-covered
(`NEW-MCDC`), then a summary. Use it to check that a new test covers the pair GAPS asked for.

## Cost

Measured on 6d85179, `JOBS=3`, on an Apple M4 Pro (14 cores, 48 GB, macOS 27.0.1):

| step | time |
|---|---|
| first run, total (worktree, tool and vargo builds, instrumentation, reports) | 13 min 6 s |
| of which `vargo build --release` of the instrumented worktree, including vstd verification (2060 verified) | 153 s |
| of which `vargo test --release -p rust_verify_test` (144 test binaries, 4773 passed, 60 ignored) | 630 s |
| later run with `--test modes` (build reused) | 12.2 s |
| `delta` on a 10-line program | 0.6 s |

This README does not give an uninstrumented full-suite time for comparison: it was not measured
on the same machine in the same conditions. On three test files (modes, recursion, erase; 236
tests) the prototype measured the same pass/fail results with and without instrumentation and
per-file times within 1 s of each other. The worktree and its build use 1.5 GB of disk.

The runtime keeps a per-process set of distinct records and writes each new one once (every
4096 new records, at most every 2 s, and at exit), so the cost per evaluation is one mutex lock
and one hash-set lookup. With `MCDC_DIR` unset the instrumented binary records nothing.

## How the rewriting works

`mcdc instrument` parses each file with `syn` and inserts text at token boundaries; it adds no
line breaks, so line numbers in error messages and in the manifest are those of the original
source (the one added line, `mod __mcdc`, is appended at the end of each crate root). A decision
`TREE` becomes

```rust
({let mut __mcdc_e: u128 = 0; let __mcdc_o: bool = TREE; crate::__mcdc::rec(ID, __mcdc_e, __mcdc_o); __mcdc_o})
```

and each atom `A` inside it becomes

```rust
({let __mcdc_c: bool = A; __mcdc_e |= if __mcdc_c {BITS_T} else {BITS_F}; __mcdc_c})
```

The `&&` and `||` operators of `TREE` stay in place, so evaluation order and short-circuiting are
those of the original code; an atom that is not evaluated leaves its two bits at 0. Rust 2024
let-chains in `if` and `while` (`if a && let Some(x) = e && b`) record a marker after each `let`
and the outcome at the start of the then-branch or in the else-branch. The runtime
(`src/runtime/mcdc_rt.rs`) is written next to each crate root as `__mcdc_rt.rs` and included as
`mod __mcdc`.

## Limits

- Code inside macro invocations is not instrumented (34 `&&`/`||` operators at 6d85179, for
  example inside `assert!`; `quote!` and `parse_quote!` bodies are generated code and not
  counted). One let-chain in a match guard is skipped. Const contexts are skipped (none at
  6d85179).
- Coverage is pooled over all processes: the vstd build and every test's verifier process add to
  one set of evaluations, so a pair can combine evaluations from two different tests. This is
  how suite-level MC/DC is defined, but it does not say which test produced which side.
- Atoms are often correlated (one implies another, or an earlier check rejects the input), so
  some needed pairs are infeasible. The pair in GAPS comes from the decision structure only; it
  is a candidate, not a proof that a test exists. Example: `vir/src/well_formed.rs:660` atom 1
  can only be true for a non-spec function, which line 651 already rejects.
- Decisions are boolean `&&`/`||` expressions only. Single-condition `if`s are decisions of one
  atom; `match` arms and `if let` without `&&` are not measured.
- The instrumented crates are the five listed above; `--crates` changes the list.

## Relation to `coverage.sh` and to rustc

`tools/coverage.sh` measures line coverage with `-C instrument-coverage`; this tool follows its
interface (`JOBS`, `OUT_DIR`, pass-through `vargo test` arguments) and runs the same suite. rustc
had an unstable MC/DC mode, `-Zcoverage-options=mcdc`, which has since been removed: rustc
1.98.0-nightly (4c9d2bfe4 2026-07-01) rejects it (`incorrect value 'mcdc' for unstable option
'coverage-options' - 'block' | 'branch' | 'condition' was expected`). `-Zcoverage-options=condition`
reports, per condition, whether it was observed true and false, which is condition coverage, not
MC/DC. The source rewriting here does not depend on a nightly compiler or on LLVM tools.

## Follow-up: match arms by Verus mode

The prototype this tool comes from also recorded, for each match arm in `vir/src/modes.rs`,
`vir/src/well_formed.rs`, `vir/src/ast_to_sst.rs`, `rust_verify/src/rust_to_vir_expr.rs` and
`rust_verify/src/erase.rs`, the Verus mode of the enclosing function, and listed arms reached only
in exec code or only in spec/proof code. It needs a per-file configuration of Rust expressions
over internal fields (`outer_mode`, `typing.block_ghostness`, `bctx.in_ghost`, ...) that changes
whenever those signatures change, so it is not part of this tool.

## Tests

`cargo test --release -p mcdc` (from `source/`; the crate is a member of the source/ workspace,
like `tools/line_count`) runs `tests/criterion.rs`, the criterion on hand-made evaluation sets
(short-circuit pairs, a pair where two atoms differ, the masking example above, atom 63), the
needed-pair computation, and the rewriter on small inputs: the output parses, keeps line
numbers and operators, skips const and macro code, and one test compiles a rewritten program with
`rustc`, checks that it prints the same side effects in the same order as the original, and checks
the recorded vectors against the expected short-circuit evaluations (`tests/rewrite.rs`).
