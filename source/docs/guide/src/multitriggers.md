# Multiple variables, multiple triggers, matching loops

Suppose we have a `forall` expression with more than one variable, `i` and `j`:

```rust
{{#include ../../../rust_verify/example/guide/quants.rs:test_distinct1}}
```

The `forall` expression shown above says that every element of `s` is distinct.
(Note: we could have written
`0 <= i < s.len() && 0 <= j < s.len() && i != j`
instead of
`0 <= i < j < s.len()`,
but the latter is more concise and is just as general:
given any two distinct integers, we can let `i` be the smaller one
and `j` be the larger one so that `i < j`.)

In the example above, the trigger `is_distinct(s[i], s[j])`
contains both the variables `i` and `j`,
and the expression `is_distinct(s[2], s[4])` matches the trigger with `i = 2, j = 4`:

```
0 <= 2 < 4 < s.len() ==> is_distinct(s[2], s[4])
```

Instead of using a function call `is_distinct(s[i], s[j])`,
we could just write `s[i] != s[j]` directly.
However, in this case, we cannot use the expression `s[i] != s[j]` as a trigger,
because, as discussed in the [previous section](./forall.md),
triggers cannot contain equalities and disequalities like `!=`.
However, a trigger does not need to be just a single expression.
It can be split across multiple expressions,
as in the following code, which defines the trigger to be the pair of expressions
`s[i]`, `s[j]`:

```rust
{{#include ../../../rust_verify/example/guide/quants.rs:test_distinct2}}
```

Verus also supports an alternate, equivalent syntax `#![trigger ...]`,
where the `#![trigger ...]` immediately follows the `forall|...|`,
in case we prefer to write the pair `s[i]`, `s[j]` directly:

```rust
{{#include ../../../rust_verify/example/guide/quants.rs:test_distinct3}}
```

When the trigger is the pair `s[i]`, `s[j]`,
there are four matches: `i = 2, j = 2` and `i = 2, j = 4` and `i = 4, j = 2` and `i = 4, j = 4`:

```
0 <= 2 < 2 < s.len() ==> s[2] != s[2]
0 <= 2 < 4 < s.len() ==> s[2] != s[4]
0 <= 4 < 2 < s.len() ==> s[4] != s[2]
0 <= 4 < 4 < s.len() ==> s[4] != s[4]
```

The `i = 2, j = 4` instantiation proves s[2] != s[4],
which is equivalent to s[4] != s[2].
The other instantiations are dead ends, since `2 < 2`, `4 < 2`, and `4 < 4` all fail.

A trigger must mention each of the quantifier variables `i` and `j` at least once.
Otherwise, Verus will complain:

```rust
{{#include ../../../rust_verify/example/guide/quants.rs:test_distinct_fail1}}
```
```
error: trigger does not cover variable i
    |
    | / ...   forall|i: int, j: int|
    | | ...       0 <= i < j < s.len() ==> s[i] != #[trigger] s[j], // error: trigger fails to ment...
    | |__________________________________________________________^
```

In order to match a trigger with multiple expressions,
the SMT solver has to find matches for *all* the expressions in the trigger.
Therefore,
you can always make a trigger more restrictive by adding more expressions to the trigger.
For example, we could gratuitously add a third expression `is_even(i)`
to the trigger, which would cause the match to fail,
since no expression matches `is_even(i)`:

```rust
{{#include ../../../rust_verify/example/guide/quants.rs:test_distinct_fail2}}
```

To make this example succeed, we'd have to mention `is_even(2)` explicitly:
```rust
    assert(is_even(2));
    assert(s[4] != s[2]); // succeeds; we've matched s[2], s[4], is_even(2)
```

# Multiple triggers

In all the examples so far,
each quantifier contained exactly one trigger
(although the trigger sometimes contained more than one expression).
It's also possible, although rarer,
to specify multiple triggers for a quantifier.
The SMT solver will instantiate the quantifier if *any* of the triggers match.
Thus, adding more triggers leads to *more* quantifier instantiations.
(This stands in contrast to adding *expressions* to a trigger:
adding more expressions to a trigger makes a trigger more restrictive
and leads to *fewer* quantifier instantiations.)

The following example specifies both `#![trigger a[i], b[j]]` and `#![trigger a[i], c[j]]`
as triggers, since neither is obviously better than the other:

```rust
{{#include ../../../rust_verify/example/guide/quants.rs:test_multitriggers}}
```

(Note: to specify multiple triggers, you must use the `#![trigger ...]` syntax
rather than the `#[trigger]` syntax.)

If the quantifier had only mentioned the single trigger `#![trigger a[i], b[j]]`,
then the assertion above would have failed, because `a[2] != c[4]` doesn't mention `b`.
A single trigger `#![trigger a[i], b[j], c[j]]` would be even more restrictive,
requiring both `b` and `c` to appear, so the assertion would still fail.

In the example above, you can omit the explicit triggers and
Verus will automatically infer exactly the two triggers
`#![trigger a[i], b[j]]` and `#![trigger a[i], c[j]]`.
However, in most cases, Verus deliberately avoids inferring more than one trigger,
because multiple triggers lead to more quantifier instantiations,
which potentially slows down the SMT solver.
One trigger is usually enough.

As an example of where one trigger is safer than multiple triggers,
consider an assertion that says that updating element `j`
of sequence `s` leaves element `i` unaffected:

```rust
{{#include ../../../rust_verify/example/guide/quants.rs:seq_update_different}}
```

There are actually two possible triggers for this:

```
#![trigger s.update(j, a)[i]]
#![trigger s.update(j, a), s[i]]
```

However, Verus selects only the first one and rejects the second,
in order to avoid too many quantifier instantiations:

```
note: automatically chose triggers for this expression:
    |
    |       assert(forall|i: int, j: int|
    |  ____________^
    | |         0 <= i < s.len() && 0 <= j < s.len() && i != j ==> s.update(j, a)[i] === s[i]
    | |_____________________________________________________________________________________^

note:   trigger 1 of 1:
   --> .\rust_verify\example\guide\quants.rs:243:60
    |
    |         0 <= i < s.len() && 0 <= j < s.len() && i != j ==> s.update(j, a)[i] === s[i]
    |                                                            ^^^^^^^^^^^^^^^^^
```

(Note: you can use the `--triggers` command-line option to print the message above.)

# Matching loops: what they are and to avoid them

Suppose we want to specify that a sequence is sorted.
We can write this in a similar way to the earlier `forall` expression
about sequence distinctness,
writing `s[i] <= s[j]` in place of `s[i] != s[j]`:

```rust
{{#include ../../../rust_verify/example/guide/quants.rs:test_sorted_good}}
```

In Verus, this is the best way to express sortedness,
because the trigger `s[i], s[j]` works very well.
However, there is an alternate approach.
Instead of quantifying over both `i` and `j`,
we could try to quantify over just a single variable `i`,
and then compare `s[i]` to `s[i + 1]`:

```rust
{{#include ../../../rust_verify/example/guide/quants.rs:test_sorted_bad1}}
```

However, Verus complains that it couldn't find any good triggers:

```
error: Could not automatically infer triggers for this quantifer.  Use #[trigger] annotations to manually mark trigger terms instead.
    |
    | /         forall|i: int|
    | |             0 <= i < s.len() - 1 ==> s[i] <= s[i + 1],
    | |_____________________________________________________^
```

Verus considers the expressions `0 <= i`, `i < s.len() - 1`, `s[i]`, and `s[i + 1]`
as candidates for a trigger.
However, all of these except `s[i]` contain integer arithmetic, which is not allowed in triggers.
The remaining candidate, `s[i]`, looks reasonable at first glance.
Verus nevertheless rejects it, though, because it potentially leads to an infinite *matching loop*.
Triggers are the way to program the SMT solver's quantifier instantiations,
and if we're not careful, we can program infinite loops.
Let's look at how this can happen.
Suppose that we insist on using `s[i]` as a trigger:

```
forall|i: int|
    0 <= i < s.len() - 1 ==> #[trigger] s[i] <= s[i + 1],
```

(TODO: Verus should print a warning about a potential matching loop here.)

This would, in fact, succeed in verifying the assertion `s[2] <= s[4]`,
but not necessarily in a good way.
The SMT solver would match on `i = 2` and `i = 4`.
For `i = 2`, we'd get:

```
0 <= 2 < s.len() - 1 ==> s[2] <= s[3]
```

This creates a new expression `s[3]`, which the SMT can then match on with `i = 3`:

```
0 <= 3 < s.len() - 1 ==> s[3] <= s[4]
```

This tells us `s[2] <= s[3]` and `s[3] <= s[4]`,
which is sufficient to prove `s[2] <= s[4]`.
The problem is that the instantiations don't necessarily stop here.
Given `s[4]`, we can match with `i = 4`, which creates `s[5]`,
which leads to matching with `i = 5`, and so on:

```
0 <= 4 < s.len() - 1 ==> s[4] <= s[5]
0 <= 5 < s.len() - 1 ==> s[5] <= s[6]
0 <= 6 < s.len() - 1 ==> s[6] <= s[7]
...
```

In principle, the SMT solver could loop forever with `i = 6`, `i = 7`, and so on.
In practice, the SMT solver imposes a cutoff on quantifier instantiations which often
(but not always) halts the infinite loops.
But even if the SMT solver halts the loop,
this is still an inefficient process,
and matching loops should be avoided.
(For an example of a matching loop that causes the SMT solver to use an infinite
amount of time and memory, see [this section](./profiling.md).)
