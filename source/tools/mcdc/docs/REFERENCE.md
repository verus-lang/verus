# mcdc reference

Commands, file formats, scripts, internals, cost and limits of `tools/mcdc`. The overview and the
test-generation loop are in [../README.md](../README.md).

## MC/DC

### What MC/DC measures

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

### Why this matters for Verus

Verus itself is not verified. Its soundness rests on checks such as the mode checks in
`vir/src/modes.rs`, the well-formedness checks in `vir/src/well_formed.rs` and the erasure in
`rust_verify/src/erase.rs` giving the right answer in every combination of their conditions. An
atom without an independence pair is a condition that no test shows to matter: it could be
wrong, inverted or redundant and every test would still pass. Line and branch coverage do not
report this, because they count each line or each outcome once, whatever the atom values were.

### Worked example: `vir/src/modes.rs:1434`

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

### Running

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

### Reading GAPS

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

### Cost

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

### How the rewriting works

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
and the outcome at the start of the then-branch or in the else-branch. A let-chain in a match guard
(`P if a && let Some(x) = e => ..`) cannot be wrapped in a block that declares the vector, so its
vector is kept per thread by the runtime: the guard starts an evaluation, each atom records itself,
and every arm body of the match ends the pending evaluation, with outcome true in the guarded arm
and false in the others. The runtime
(`src/runtime/mcdc_rt.rs`) is written next to each crate root as `__mcdc_rt.rs` and included as
`mod __mcdc`.

### Limits

- Code inside macro invocations is not instrumented (34 `&&`/`||` operators at 09d09ee2, for
  example inside `assert!`; `quote!` and `parse_quote!` bodies are generated code and not
  counted). The tokens of a macro call are not parsed as Rust expressions, so the rewriter cannot
  find the decisions in them without expanding the macro.
- Const contexts are skipped (none at 09d09ee2): a `const fn` body, a const or static
  initializer, an array length or an enum discriminant can only call `const fn`s, and the
  recording runtime (a hash set behind a mutex, file output) cannot be a `const fn`. A `const fn`
  called at run time is not recorded either, because its body is the same code.
- A decision with more than 64 atoms is skipped (none at 09d09ee2; the largest has 15 atoms):
  the evaluation vector is one `u128`, 2 bits per atom, and a record is 20 bytes. A wider vector
  would change the record format and the analyzer for decisions that do not occur.
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

### Relation to `coverage.sh` and to rustc

`tools/coverage.sh` measures line coverage with `-C instrument-coverage`; this tool follows its
interface (`JOBS`, `OUT_DIR`, pass-through `vargo test` arguments) and runs the same suite. rustc
had an unstable MC/DC mode, `-Zcoverage-options=mcdc`, which has since been removed: rustc
1.98.0-nightly (4c9d2bfe4 2026-07-01) rejects it (`incorrect value 'mcdc' for unstable option
'coverage-options' - 'block' | 'branch' | 'condition' was expected`). `-Zcoverage-options=condition`
reports, per condition, whether it was observed true and false, which is condition coverage, not
MC/DC. The source rewriting here does not depend on a nightly compiler or on LLVM tools.

### Tests

`cargo test --release -p mcdc` (from `source/`; the crate is a member of the source/ workspace,
like `tools/line_count`) runs `tests/criterion.rs`, the criterion on hand-made evaluation sets
(short-circuit pairs, a pair where two atoms differ, the masking example above, atom 63), the
needed-pair computation, and the rewriter on small inputs: the output parses, keeps line
numbers and operators, skips const and macro code, and one test compiles a rewritten program with
`rustc`, checks that it prints the same side effects in the same order as the original, and checks
the recorded vectors against the expected short-circuit evaluations, let-chains in `if`, `while`
and a match guard included (`tests/rewrite.rs`).
`tests/schemata.rs` checks the mutant rewriter and the map: the map is the same on two runs and its
ids follow source order, every operator class appears on a sample file, the rewritten file parses
and keeps its line count, MC/DC manifest ids are reused, disable entries remove their sites, a
bitset decodes to the ids it was written with, and each mutgen selector and filter selects what it
names. Two tests cover the combined build: a two-file program is built once with `mcdc instrument`
and once with `mcdc mutate` on every file and no mutant on; both are compiled with `rustc` and run,
and the test checks that the manifests are equal, the outputs are equal, the record sets are equal,
and the let-chain decisions of the mutated files (if, while, match guard) have records. The other
checks that the map records the merge base with the upstream branch, not HEAD, in a scratch git
repository with a tool commit on top of the base.

## Mutation

### Building

```
tools/mcdc/scripts/build.sh mcdc OUT      # build A: `mcdc instrument`, MC/DC only
tools/mcdc/scripts/build.sh mutants OUT   # build B: `mcdc mutate`, MC/DC + mutant schemata
```

Both create a detached worktree of `HEAD` in `OUT/build` (plus the uncommitted changes to tracked
files), rewrite it and run `vargo build --release`, which verifies vstd with the rewritten
verifier. The verus binary is `OUT/build/source/target-verus/release/verus`; `OUT/map` holds
`manifest.jsonl` (the MC/DC manifest, the same ids as an `mcdc instrument` build of the same
source) and, for build B, `mutants.tsv` and `decisions.tsv`. Environment: `JOBS`, `FILES` (a file
list that restricts the mutated files; default every file), `DISABLE` (default
`tools/mcdc/mutate-disable.txt`), `ROUNDS`
(default 20), `MUTANTS_OFF=1` (same rewrite, every mutant compiled off), `WRAP` (command prefix for
each `vargo build`, for example a timeout or a job limiter).

`mcdc mutate SOURCE_DIR [--files FILES] --map-dir DIR [--disable FILE] [--crates ..] [--commit SHA]
[--base-ref REF] [--mutants-off] [--dry-run]` instruments every crate for MC/DC and plants mutant
schemata in every file of those crates, or only in the files listed in FILES
(`tools/mcdc/mutate-files.txt` lists the 23 priority files). A mutated file keeps the MC/DC
instrumentation of `mcdc instrument`: both rewriters compute text edits on the original file, and
the edits are applied together (`src/edit.rs` orders the wrappers that open or close at the same
offset). The manifest and the records of a build B are therefore those of a build A of the same
source, let-chains included; `tests/schemata.rs` checks this on a sample program. The map's guard
decisions reuse the manifest id when the start position matches. `--commit` defaults to the merge
base of HEAD and `--base-ref` (default `origin/main`), the upstream commit of the verifier sources,
not the branch head; the command warns when the verifier crates differ from it. `--dry-run` writes the
map without changing `SOURCE_DIR`.

**Disable loop.** All operators are syntactic; the runtime helpers are generic (for example
`ob<T: Obo>` for off-by-one, `q<T: Default, E>` for a swallowed `?`) so that most alternatives
type-check without type information. Sites where they do not compile are removed: on a failed build,
`scripts/fixbuild.py LOG MAP_DIR SOURCE_DIR DISABLE` maps each compiler error to the mutation points
on the error line (or in the error's source excerpt), narrows the operator from the message (a
missing `Default` bound means drop-try or err-to-ok, a missing `Obo` bound an off-by-one, a borrow
error a boxed reversed iterator or a deleted or rewritten statement on a line the error names, a
definite-initialization error a deleted statement, a block that became `()` a skipped error return
or a deleted statement in the lines of the error) and appends
`file:line@op` entries to the disable list; `build.sh mutants` then rewrites and rebuilds.
`mutate-disable.txt` is the list for 6d85179: 1,351 entries (`grep -vc '^#'
tools/mcdc/mutate-disable.txt`).

### Operators

At 6d85179, `mcdc mutate` on mutate-files.txt with mutate-disable.txt (regenerate: `build.sh mutants OUT`, then `cut -f7 OUT/map/mutants.tsv | tail -n +3 | sort | uniq -c`):

| class | operator | mutation | mutants |
|---|---|---|---:|
| condition | cond-true | atom of a decision, or a single-condition if, while or match guard, forced to true | 2,645 |
| condition | cond-false | the same, forced to false | 2,645 |
| condition | cond-negate | the same, negated | 2,116 |
| condition | decision-negate | whole if condition negated (swaps the branches of an if/else) | 841 |
| condition | and-or-swap | `&&` replaced by `||` and the reverse | 644 |
| condition | while-false | while condition forced to false | 12 |
| datapath-delete | delete-stmt | expression statement skipped (call, method call, assignment, compound assignment, macro other than print/assert/panic) | 3,027 |
| datapath-delete | skip-err-return | `return Err(..)` statement falls through | 270 |
| datapath-const | const-plus1 | integer literal + 1 | 1,041 |
| datapath-const | const-minus1 | integer literal - 1 | 1,041 |
| datapath-const | index-plus1 | index expression + 1 | 203 |
| datapath-const | index-minus1 | index expression - 1 | 203 |
| container | container-iter-rev | `iter()` reversed | 747 |
| container | container-len-plus1 | `len()` + 1 | 396 |
| container | container-len-minus1 | `len()` saturating - 1 | 396 |
| container | container-contains-negate | `contains` negated | 58 |
| container | container-first-last | `first()` and `last()` swapped | 21 |
| container | container-insert-absent | `insert` used as a value returns the absent result | 21 |
| container | container-is-empty-negate | `is_empty` negated | 10 |
| container | container-retain-negate | `retain` predicate negated | 6 |
| container | container-remove-absent | `remove` used as a value returns the absent result | 2 |
| enum | enum-variant | unit variant of Mode, Ghost, InvAtomicity, InequalityOp or IntRange replaced by each other variant | 1,026 |
| option | option-some-none | `Some(x)` replaced by None | 757 |
| option | option-get-none | `get` / `get_mut` replaced by None | 148 |
| option | option-unwrap-or-default | `unwrap_or(d)` replaced by `d` | 8 |
| datapath-return | ret-true | the same, replaced by true | 179 |
| datapath-return | ret-negate | bool returned by a `-> bool` function negated | 179 |
| datapath-return | ret-false | the same, replaced by false | 179 |
| datapath-error | drop-try | `e?` with an Err replaced by Ok(Default) | 379 |
| datapath-error | err-to-ok | `Err(..)` value replaced by Ok(Default) | 18 |
| datapath-compare | rel-boundary | `<` to `<=`, `<=` to `<`, `>` to `>=`, `>=` to `>` | 175 |
| datapath-compare | eq-flip | `==` and `!=` swapped (outside condition atoms) | 122 |
| datapath-vec | vec-remove | one element removed from a `vec![..]` of 2 to 16 elements | 210 |
| total | | | 19,725 |

`decision` in mutants.tsv is the atom's own decision for a condition mutant, else the innermost
guarding decision with the outcome that reaches the mutant (`id:o`, o = 1 for T, 0 for F, k for match
arm k); `guards` is the static guard chain within the function, outermost first; `atom` is the atom
index of a condition mutant. Ids are deterministic: mutants are numbered in (file order, line,
column, operator) order, so the map is a function of the source, the file list and the disable list.
The FNV-1a 64 digest of mutants.tsv is compiled into the runtime.

### Switching mutants on

The runtime (`src/runtime/mut_rt.rs`, written next to the root of every mutated crate except
`rust_verify`, which uses `vir::__mut`; `air` and `rust_verify` binaries use their library's copy)
reads `MUTANT_BITSET=<file>` once at startup. Each crate with its own copy has its own guard stack
and writes its own path-log files. File format: 8 bytes magic `VMUTBS01`, 40 bytes source commit
(ASCII; the merge base, see above), u32 LE mutant count, u64 LE
map digest, then ceil((count + 1) / 8) bytes where bit i (least significant bit first) switches
mutant i on. The runtime exits with status 2 and names both sides when the commit, count or digest
differ from the build. `MUTANT_ID=N` is a shorthand for a bitset with bit N only. Several bits may be
set; within one site the lowest selected mutant applies. With no bitset, every site returns the
original value.

```
mcdc mutgen --map mutants.tsv [--id N] [--ids N,M] [--file REL] [--fn PATH] [--loc REL:LINE] [--stdin]
            [--class C[,C]] [--random SEED:RATE] (--out FILE | --list)
mcdc bitset FILE        # commit, count, digest and selected ids of a bitset
```

Selectors (`--id`, `--ids`, `--file`, `--fn`, `--loc`, `--stdin`) are united; with none, every mutant
is selected. `--fn` matches a full function path or any `::` suffix of it. Filters apply in order:
`--class` (an operator name or a class; `datapath` matches every `datapath-*` class), then `--random
SEED:RATE`, which keeps a mutant when splitmix64(SEED xor splitmix64(id)) is below RATE times 2^64,
so a sample is reproducible.

### Path log

Every guarded body (then block, else branch, while body, match arm) starts with
`let __mg = crate::__mut::guard(D, O);`. While logging, `guard` pushes (D, O) on a thread-local stack
and its value pops on drop, so early return, `?`, break and unwinding all pop. With `MUTANT_LOG=dir`,
each process writes, deduplicated, at exit:

| file | content |
|---|---|
| `<crate>-<pid>.reach` | `point hash`: the mutation site ran with guard stack `hash` |
| `<crate>-<pid>.inf` | `id hash`: the mutant would have changed a value or effect there (infection) |
| `<crate>-<pid>.stacks` | `hash d:o,...`: the stack with that hash, once per distinct stack |
| `<crate>-<pid>.dec` | `d o depth`: the guarded body of decision d was entered with outcome o at that depth |

Infection is computed beside the original value where that has no side effect: a forced atom infects
when it differs from the atom's value, a boundary comparison when `<` and `<=` disagree on the
operands, a swallowed `?` only on an Err, get-to-None only on a Some; a deleted statement, a skipped
error return or a removed vector element infects whenever it runs. A mutant that no run infects
cannot change any run. Decision ids are listed in decisions.tsv (MC/DC manifest ids below 100001).

**Cone of a target.** For a test that targets atom i of decision D on side o, the cone is the
condition mutants of (D, i), the mutants whose static guard chain contains (D, o), and the mutants
that some baseline run reached with (D, o) on the guard stack (this includes callees). `mutrun.py
check` scores the test only on the cone mutants that its own run reaches with the target guard on the
stack and infects. The cone is control dependence only: a value computed before D and read under D
is not in it.

### Scripts

`scripts/mutrun.py` (see `--help`) runs a mutation pass over test programs, each a `.rs` file with
an `// expected:` header and optional `// verus-args:`, `// env:` and `// target:` headers:

| command | does |
|---|---|
| `tests DIR...` | inventory of the programs |
| `baseline` | each program on build B with `MUTANT_LOG` and no mutant, on build A, and on a plain build if given: verdicts must agree; keeps the reach and infection sets and the path log |
| `mutants IDS OUT [--cap N]` | for each mutant, its infecting programs fastest first until one kills it (at most N) |
| `report RESULTS...` | status per mutant (KILLED, SURVIVED, SURVIVED-CAPPED, NOT-INFECTED, NOT-REACHED, NOT-RUN), counts per class and operator |
| `index` | cone index from the static guard chains and the baseline logs |
| `check TEST.rs [--target D:I:O]` | path-conditioned kill check of one program |
| `vet TEST.rs` | gate 1 on build A (verdict, compiled binary), then `check` |
| `suite TREE --test T [--name F] --ids ..` | `vargo test -p rust_verify_test` under each mutant; the tests whose result changes |
| `rvt-baseline TREE [--only RE]` | every non-ignored rust_verify_test test of build B's `source/` dir, one test per process with `MUTANT_LOG` and no mutant: result, time, reached points, infected mutants |
| `rvt-mutants TREE IDS OUT [--tests RE] [--budget S]` | for each mutant, the passing tests that infect it in that baseline, fastest first, in batches of 1, 4, 16, then 32 tests per process, under `MUTANT_ID`, until a test fails, crashes or times out (killed), all pass (survived) or S seconds are spent |
| `rvt-report IDS OUT...` | KILLED, SURVIVED, SURVIVED-CAPPED, NOT-INFECTED, NOT-REACHED per mutant of IDS, per class and operator; a mutant killed in any OUT file is killed |

Builds and the map come from `--build-a`, `--build-b`, `--plain`, `--map` or `MCDC_BUILD_A`,
`MCDC_BUILD_B`, `MCDC_PLAIN`, `MCDC_MAP`; `--jobs N` runs N programs in flight. `scripts/cover.py
MATRIX.jsonl [--weights ..] [--free NAMES]` selects the smallest weighted set of tests that keeps
every kill of a kill matrix (`mutrun.py mutants` writes one), with a lower bound on the count.

### Limits of the mutation layer

- Operators are syntactic. Sites where the generic helper does not type-check are dropped by the
  disable loop; a type-aware version would mutate after type checking.
- container-iter-rev produces mostly equivalent mutants, because most iteration in these files is
  order-insensitive.
- Equivalent mutants are not detected; a survivor needs an argument before it counts as a missing
  test.
- The cone holds control-dependent mutants only.
- The kill measurement in the README covers the mutants of the 23 priority files; the other files
  are mutated in the same build but not measured.
