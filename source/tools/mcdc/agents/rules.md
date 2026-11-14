# Shared rules for every agent

Every prompt in this directory includes this file. Read it before the task file.

## Inputs

- `MCDC_BUILD_A`: path to the `verus` binary of build A (`mcdc instrument`: MC/DC records only, original
  behavior).
- `MCDC_BUILD_B`: path to the `verus` binary of build B (`mcdc mutate`: MC/DC records and the mutant
  schemata; no mutant is active unless `MUTANT_BITSET` or `MUTANT_ID` is set).
- `MCDC_MAP`: the map directory written by `mcdc mutate` (`mutants.tsv`, `decisions.tsv`).
- The Verus source tree both builds were made from (read-only). Line numbers in the gap report and in
  `mutants.tsv` refer to this uninstrumented source.
- An output directory given in the launching prompt. Write only there.

## Running Verus

- Use the run command and limits the launching prompt gives (timeout, how many runs in flight). Without
  one: one Verus run at a time, timeout 300 s.
- A run that ends without a `verification results` line because it was killed (exit 137, a timeout) is not
  a result. Re-run it later; never record it as a verdict.
- Do not build Verus and do not modify the source tree or the builds.

## Test program header

Every program written by an agent starts with these comment lines (omit the ones that do not apply):

```
// target: id=D atoms i,j (..=>T)      one line per MC/DC target: decision id, atom indices, side
// kills: mutant N (file:line)          for a mutant-killing test
// expected: verifies                   or: // expected: rejected: <error substring>
//   <one line: why, from Rust and Verus semantics, written before running Verus>
// verus-args: <arguments, if any>
// runtime: <observed binary output, or n/a (no exec code) with the reason>
```

`expected` is the verdict the language semantics require, written before the first run. When the
observed verdict differs, the program is a finding: BUG when Verus accepts a program it must reject,
INCOMPLETE when Verus rejects a program it must accept.

## Ground truth

The execution of the compiled program settles what a program does. A Verus result that a run contradicts
is wrong, whatever a comment or an argument says.

- A program that verifies and has exec code: give it a `fn main` (marked `#[verifier::external]` or outside
  `verus!`) that calls each verified exec function on inputs that satisfy its `requires` (include boundary
  values: 0, the type's minimum and maximum, empty, one element) and checks each `ensures` with `assert!`.
  Compile with `verus prog.rs --compile -o bin` and run `./bin`. A failed `assert!`, or a panic where Verus
  proved there is none, is a BUG.
- A program that Verus rejects and that has exec code: copy the exec part into a plain Rust file (specs
  removed), compile it with `rustc` from the toolchain Verus uses, and run it. The run shows whether the
  rejected claim fails (the rejection is justified) or holds (the rejection is incompleteness).
- A proof of `false`: add an exec function whose verified `ensures` the binary violates (call the false
  lemma in a `proof` block, return a contradicting value, print it), so the finding has a runtime witness.
- Proof-only or spec-only programs: write `runtime: n/a (no exec code)`; when the claim is about a
  computable value, check that value with a small Rust or Python computation and record it.
- Option and driver programs (`verus-args`): the executed check is the Verus process itself (exit code,
  results line, `--output-json` fields).
- A runtime contradiction is attributed to Verus only if the program does not rely on a known rustc
  soundness bug (rustc `I-unsound` issues). The Rust toolchain is part of Verus's trusted base.
- A passing run on finite inputs does not prove the claim for all inputs; it only fails to refute it.

## Reporting a finding

A BUG gets: a minimal reproducer with the header above, a control (the same program without the
trigger) that Verus rejects, the exact commands, and the runtime witness. Put BUGs first in the final
message. A Verus panic is a crash, recorded separately with its first panic line; it is not a BUG unless
the panic is reached from verified code at run time.

## Dead-branch argument format

When a decision outcome, an atom value or a mutant cannot be reached from any Verus input, classify it
with one of these classes and give the argument in this form:

| class | meaning | the argument must cite |
|---|---|---|
| PINNED | the atom's value is fixed by an invariant | every site that constructs or assigns the value, and every caller of the enclosing function with the arguments it passes |
| UNREACHABLE | no input reaches the decision with the needed values | every call path from an entry point to the decision, and for each path the check that blocks it (with the pass order in `rust_verify/src/verifier.rs` when the argument is about order) |
| COUPLED-INFEASIBLE | the atoms are correlated by construction | the code that ties them and every construction of their inputs |
| FEATURE-GATED | needs a cargo feature, cfg or environment variable the builds lack | the cfg and every way to enable it |
| EQUIVALENT | a mutant changes no observable outcome for any program | the redundant check or the reason the value is never read (file:line) |

Record the enumeration commands (the `grep`/`rg` patterns) and their hit counts with the argument. An
argument is complete only when every listed site or path is accounted for. Spend at most 3 attempts on
one target before classifying it; if neither a program nor a complete argument exists, classify it OPEN
and list what was tried.

## Style

Present tense, no em-dashes, no metaphors. Every claim carries a file:line or a command with its output.
