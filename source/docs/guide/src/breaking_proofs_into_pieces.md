# Breaking proofs into smaller pieces

## Motivation

If you write a long function with a lot of proof code, Verus will
correspondingly give the SMT solver a long and difficult problem to solve. So
one can improve solver performance by breaking that function down into smaller
pieces. This performance improvement can be dramatic because solver response
time typically increases nonlinearly as proof size increases. After all,
having twice as many facts in scope gives the solver far more than twice as
many possible paths to search for a proof. As a consequence, breaking
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

For instance:
```
fn my_long_function(x: u64, ...)
{
    let y: int = ...;
    ... // first part of proof, establishing fact f(x, y)
    P1; // modest-size proof...
    P2; //   establishing...
    P3; //   facts s1 and s2...
    P4; //   about x and y
    ... // second part of proof, using facts s1 and s2
}
```
might become
```
proof fn my_long_function_helper(x: u64, y: int)
    requires
        f(x, y)
    ensures
        s1(x),
        s2(x, y)
{
    P1; // modest-size proof...
    P2; //   establishing...
    P3; //   facts s1 and s2...
    P4; //   about x and y
}

fn my_long_function(x: u64, ...)
{
    ... // first part of proof, establishing fact f(x, y)
    my_long_function_helper(x, y);
    ... // second part of proof, using facts s1 and s2
}

```

You may find that, once you've moved `P` into the body of the lemma, you can
not only remove `P` from the long function but also remove significant
portions of `P` from the lemma where it was moved to. This is because a lemma
dedicated solely to establishing `S` will have a smaller context for the
solver to reason about. So less proof annotation may be necessary to get it to
successfully and quickly establish `S`. For instance:

```
proof fn my_long_function_helper(x: u64, y: int)
    requires
        f(x, y)
    ensures
        s1(x),
        s2(x, y)
{
    P1; // It turns out that P2 and P3 aren't necessary when
    P4; //    the solver is focused on just f, s1, s2, x, and y.
}
```

## Dividing a proof into parts 1, 2, ..., n

Another approach is to divide your large function's proof into `n` consecutive
pieces and put each of those pieces into its own lemma. Make the first lemma's
`requires` clauses be the `requires` clauses for the function, and make its
`ensures` clauses be a summary of what its proof establishes. Make the second
lemma's `requires` clauses match the `ensures` clauses of the first lemma, and
make its `ensures` clauses be a summary of what it establishes. Keep going
until lemma number `n`, whose `ensures` clauses should be the `ensures`
clauses of the original function. Finally, replace the original function's
proof with a sequence of calls to those `n` lemmas in order.


For instance:
```
proof fn my_long_function(x: u64)
    requires r(x)
    ensures  e(x)
{
    P1;
    P2;
    P3;
}
```
might become
```
proof fn my_long_function_part1(x: u64) -> (y: int)
    requires
        r(x)
    ensures
        mid1(x, y)
{
    P1;
}

proof fn my_long_function_part2(x: u64, y: int)
    requires
        mid1(x, y)
    ensures
        mid2(x, y)
{
    P2;
}

proof fn my_long_function_part3(x: u64, y: int)
    requires
        mid2(x, y)
    ensures
        e(x)
{
    P3;
}

proof fn my_long_function(x: u64)
    requires r(x)
    ensures  e(x)
{
    let y = my_long_function_part1(x);
	my_long_function_part2(x, y);
	my_long_function_part3(x, y);
}

```
Since the expressions `r(x)`, `mid1(x, y)`, `mid2(x, y)`, and `e(x)` are each
repeated twice, it may be helpful to factor each out as a spec function and
thereby avoid repetition.
