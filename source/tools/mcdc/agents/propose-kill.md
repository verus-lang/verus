# Task PROPOSE: write a test that kills a surviving mutant

Read `rules.md` and `mutants.md` first.

## Inputs

- A queue of mutant ids (from the launching prompt), each a polarity gap: infected on the active path of
  some tests, killed by none, with its direction (weakening or strengthening) when known.
- For each mutant, the tests that reached and infected it.

## Method, per mutant

1. Start from one of the tests that reached and infected the mutant, or write a small new program. Keep
   the mutant on the active path and give the program the needed polarity:
   - weakening: make the program violate exactly the obligation or check the mutant removes (negate or
     perturb that assertion, `ensures`, bound, mode or precondition), so build A must reject it there;
   - strengthening: make the program need exactly the fact the mutant removes, so build A verifies it and
     build B with the mutant fails.
2. Header: `// kills: mutant <id> (<file>:<line>)`, `// target: id=D atoms i (..=>T|F)` when the decision is
   known, `// expected:` with a one-line reason, `// verus-args:` if needed. For exec code, a `fn main` with
   `assert!`s (the compiled binary is the ground truth).
3. Validate:
   - (a) build A gives the expected verdict, and the compiled binary agrees (`scripts/mutrun.py vet`, check 1);
   - (b) build B with the mutant on gives a different outcome than build B without it;
   - (c) the mutant is reached and infected on the path (`scripts/mutrun.py check --target ...`).
4. At most 3 attempts per mutant. If build A's verdict contradicts the expected verdict and the binary
   shows that Verus is wrong, copy the program to `findings/` with a control: that is a possible BUG.

## Output

In your output directory:

- `kills/*.rs`: the tests that pass (a), (b) and (c).
- `propose.tsv`: every attempt: id, test file, build A verdict, build B verdict under the mutant, killed
  (yes or no), reason.
- `findings/`: possible BUGs with control and runtime witness.

Final message: mutants attempted, kills achieved, and any possible BUGs.
