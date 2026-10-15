# Close MC/DC gaps

Read `rules.md` first. You write Verus programs that produce the decision evaluations the test suite
does not, and you treat each program as a soundness probe.

## Inputs

- The gap report of the last run of `tools/mcdc.sh`: `GAPS.tsv` and `GAPS.md` in its `OUT_DIR`. One row per
  atom without an independence pair: decision id, file:line, atom index, atom text, the recorded
  evaluations, the evaluation vector a new test must produce (`needed_pair`), and a hint.
- Your assignment: a list of files, or of decision ids, from the launching prompt.
- `tools/mcdc.sh delta prog.rs [verus args]`: runs the MC/DC build on one program and prints what it adds
  to the last full run (new MC/DC atoms, new condition values, new outcomes).

## Method, per gap

1. Read the decision, about 80 lines around it, and its callers. Write in one line what the decision
   protects: the error, obligation, assumption, encoding choice or mode rule that depends on it. If it
   protects nothing that can change a verdict (diagnostic text, logging, profiling), say so.
2. Write the smallest program that produces the needed evaluation vector. Start from an existing test
   program (`rust_verify_test/tests/*.rs`, `examples/*.rs`) for syntax instead of writing Verus syntax from
   memory.
3. Write the `expected` header before running Verus.
4. Run `tools/mcdc.sh delta`. Keep the program only if it adds at least one atom, condition value or
   outcome. Otherwise change the program, not the tool. One program may close several gaps.
5. Apply the ground-truth rule of `rules.md` and record the `runtime` line.
6. For each soundness-relevant decision, write at least one adversarial program in addition to the
   coverage program:
   - the decision guards an error or an obligation: an input that should trigger it but reaches the same
     code with the uncovered atom flipped (through another syntax, mode, context, macro route or attribute),
     then use the skipped check to prove `false`, or to verify an exec `ensures` that the binary violates;
   - the decision chooses between encodings (poly or native, ghost or exec, spec or proof, erased or kept):
     an input where the two choices disagree, observed as a proof of `false` or a runtime contradiction;
   - the decision is a shortcut that skips a check because something must hold: an input where it does not.
7. After 3 attempts without the needed vector, classify the atom with the dead-branch format of
   `rules.md`.

Before claiming that a flag or a field has a fixed value, check every assignment to it, not only the
initial value of a struct literal.

## Output

In your output directory:

- `corpus/*.rs`: one program per file, with the header of `rules.md` (`target`, `expected`, `verus-args`,
  `runtime`).
- `probes/*.rs`: the adversarial programs, same header.
- `control/*.rs`: the control of each BUG.
- `COVERAGE.md`: one row per assigned atom: file:line | id | atom | final class (COVERED with the program
  and the delta line, or a dead-branch class with its argument, or OPEN with what was tried); a table
  program | expected | observed | runtime | agrees (yes, BUG, INCOMPLETE); a section "Probes": decision |
  protects | program | expected | observed | runtime | result.

Final message: BUGs first (file, claim, root-cause file:line, runtime witness), then the count of atoms
newly covered, counts per final class, crashes, and the hardest OPEN atoms.
