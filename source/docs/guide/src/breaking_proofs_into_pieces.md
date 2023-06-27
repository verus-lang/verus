# Breaking proofs into smaller pieces

## Motivation

If you write a long function with a lot of proof code, Verus will
correspondingly give the SMT solver a long and difficult problem to solve. So
one can improve solver performance by breaking that function down into smaller
pieces. This performance improvement can be dramatic because solver
performance typically increases nonlinearly as proof size increases. After
all, having twice as many facts in scope gives the solver far more than twice
as many possible paths to search for a proof. As a consequence, breaking
functions down can even make the difference between the solver timing out and
the solver succeeding quickly.

## Moving a subproof to a lemma

If you have a long function, look for a modest-size piece `P` of it that
functions as a proof of some locally useful set of facts `S`. Replace `P` with
a call to a lemma whose postconditions are `S`, then make `P` the body of that
lemma. Consider what parts of the original context of `P` are necessary to
establish `S`, and put those as `requires` clauses in the lemma. Those
`requires` clauses may involve local variables, in which case pass those
variables to the lemma as parameters.

You may find that, once you've moved `P` into the body of the lemma, you can
not only remove `P` from the long function but also remove significant
portions of `P` from the lemma where it was moved to. This is because a lemma
dedicated solely to establishing `S` will have a smaller context for the
solver to reason about. So less proof annotation may be necessary to get it to
successfully and quickly establish `S`.

## Dividing a proof into parts 1, 2, ..., n

Another approach is to divide your large function's proof into `n` consecutive
pieces and put each of those pieces into its own lemma. Make the first lemma's
`requires` clauses be the `requires` clauses for the function, and make its
`ensures` clauses be a summary of what its proof establishes. Make the second
lemma's `requires` clauses match the `ensures` clauses of the first lemma, and
make its `ensures` clauses be a summary of what it establishes. Keep going
until lemma number `n`, whose `ensures` clauses should be the `ensures`
clauses of the original function. Finally, replace the original function's
proof will a sequence of calls to those `n` lemmas in order.

