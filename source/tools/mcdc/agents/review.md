# Review dead-branch arguments

Read `rules.md` first. You did not write the arguments you review; your task is to break them.

## Inputs

- A table of atoms (or mutants) with a claimed class (PINNED, UNREACHABLE, COUPLED-INFEASIBLE,
  FEATURE-GATED, EQUIVALENT) and the argument, from the launching prompt.
- The current gap report (`GAPS.tsv` of the latest `tools/mcdc.sh` run) and `tools/mcdc.sh delta`. Skip an
  atom that the current report already shows covered, and say that its argument was wrong.

## Method, per atom

1. Enumerate mechanically and record the commands with their hit counts:
   - PINNED: every place that constructs or assigns the value the atom reads (search the whole source tree,
     including vstd, the builtin crates and vendored dependencies when the claim depends on them), and
     every caller of the enclosing function with the arguments it passes.
   - UNREACHABLE: every call path to the decision, up to an entry point, and for each path the check that
     blocks the needed values.
   - COUPLED-INFEASIBLE: the code that ties the atoms, and every construction of their inputs.
   - FEATURE-GATED: the cfg and every way to enable it (Cargo features, vargo flags, environment
     variables).
   - EQUIVALENT (mutants): the cited redundant check or unread value, and every reader of the mutated value.
2. Attack: if the enumeration finds a site or path the argument does not cover, write a program that uses
   it and run it with `tools/mcdc.sh delta` (for a mutant: `scripts/mutrun.py check` under the mutant).
   Apply the ground-truth rule to any exec code.
3. Verdict:
   - CONFIRMED: the enumeration is complete and no counterexample exists;
   - REFUTED: a program shows the missing value, pair or kill (save it with its header);
   - WEAKENED: the enumeration found an uncovered site or path, but 3 attempts did not reach it; state
     exactly what is missing;
   - for atoms that were OPEN: CLOSED (covered now) or STILL-OPEN.
4. A program whose verdict is unsound is a BUG, with control and runtime witness.

## Output

`REVIEW.md` in your output directory: file:line | id | atom or mutant | claimed class | verdict |
enumeration summary (counts) | evidence or program. Final message: BUGs first, then counts per verdict, the
REFUTED list and the WEAKENED list.
