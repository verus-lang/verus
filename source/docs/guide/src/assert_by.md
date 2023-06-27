# Hiding local proofs with `assert(...) by { ... }`

## Motivation

Sometimes, in a long function, you need to establish a fact `F` that requires
a modest-size proof `P`. Typically, you do this by `...; P; assert(F); ...`.
But doing this comes with a risk: the facts `P` introduces can be used not
only for proving `F` but also for proving the entire rest of the
function. This gives the SMT solver much more to think about when proving things beyond
`assert(F)`, which is especially problematic when these additional facts are
universally quantified. This can make the solver take longer, and even time out, on
the rest of the function.

## Enter `assert(...) by { ... }`

Saying `assert(F) by {P}` restricts the context that `P` affects, so that
it's used to establish `F` and nothing else. After the closing brace at the
end of `{ P }`, all facts that it established except for `F` are removed from
the proof context.

## Underlying mechanism

The way this works internally is as follows. The solver is given the facts following
from `P` as a premise when proving `F` but isn't given them for the rest of
the proof. For instance, suppose `lemma_A` establishes fact `A` and `lemma_B`
establishes fact `B`. Then
```
lemma_A();
assert(F) by { lemma_B(); };
assert(G);
```
is encoded to the solver as something like `(A && B ==> F) && (A ==> G)`. If `B` is an expansive fact
to think about, like `forall|i: int| b(i)`, the solver won't be able to think about it
when trying to establish `G`.

## Difference from auxiliary lemmas

Another way to isolate the proof of `F` from the local context is to put the
proof `P` in a separate lemma and invoke that lemma. To do this, the proof
writer has to think about what parts of the context (like fact `A` in the
example above) are necessary to establish `F`, and put those as `requires`
clauses in the lemma. The developer may then also need to pass other variables
to the lemma that are mentioned in those required facts. This can be done, but
can be a lot of work. Using `assert(F) by { P }` obviates all this work. It
also makes the proof more compact by removing the need to have a separate
lemma with its own signature.
