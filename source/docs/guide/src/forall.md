# forall and triggers

Let's take a closer look at the following code,
which uses a `forall` expression in a `requires` clause
to prove an assertion:

```rust
{{#include ../../../rust_verify/example/guide/quants.rs:quants_use_forall}}
```

The `forall` expression means that `0 <= i < s.len() ==> is_even(s[i])`
for all possible integers `i`:

```
...
0 <= -3 < s.len() ==> is_even(s[-3])
0 <= -2 < s.len() ==> is_even(s[-2])
0 <= -1 < s.len() ==> is_even(s[-1])
0 <= 0 < s.len() ==> is_even(s[0])
0 <= 1 < s.len() ==> is_even(s[1])
0 <= 2 < s.len() ==> is_even(s[2])
0 <= 3 < s.len() ==> is_even(s[3])
...
```

There are infinitely many integers `i`, so the list shown above is infinitely long.
We can't expect the SMT solver to literally expand the `forall` into
an infinite list of expressions.
Furthermore, in this example, we only care about one of the expressions,
the expression for `i = 3`,
since this is all we need to prove `assert(is_even(s[3]))`:

```rust
0 <= 3 < s.len() ==> is_even(s[3])
```

Ideally, the SMT solver will choose just the `i` that are likely to be relevant
to verifying a particular program.
The most common technique that SMT solvers use for choosing likely relevant `i`
is based on *triggers*
(also known as SMT patterns or just
[patterns](https://microsoft.github.io/z3guide/docs/logic/Quantifiers)).

A *trigger* is simply an expression or set of expressions that the SMT solver uses as a pattern
to match with.
In the example above, the `#[trigger]` attribute marks the expression `is_even(s[i])`
as the trigger for the `forall` expression.
Based on this attribute,
the SMT solver looks for expressions of the form `is_even(s[...])`.
During the verification of the `test_use_forall` function shown above,
there is one expression that has this form: `is_even(s[3])`.
This matches the trigger `is_even(s[i])` exactly for `i = 3`.
Based on this pattern match, the SMT solver chooses `i = 3` and introduces the following fact:

```rust
0 <= 3 < s.len() ==> is_even(s[3])
```

This fact allows the SMT solver to complete the proof about the assertion
`assert(is_even(s[3]))`.

Triggers are the way you program the instantiations of the `forall` expressions
(and the way you program proofs of `exists` expressions, as discussed in a later section).
By choosing different triggers, you can influence how the `forall` expressions
get instantiated with different values, such as `i = 3` in the example above.
Suppose, for example, we change the assertion slightly so that we assert
`s[3] % 2 == 0` instead of `is_even(s[3])`.
Mathematically, these are both equivalent.
However, the assertion about `s[3] % 2 == 0` fails:

```rust
{{#include ../../../rust_verify/example/guide/quants.rs:trigger_fails}}
```

This fails because there are no expressions matching the pattern `is_even(s[...])`;
the expression `s[3] % 2 == 0` doesn't mention `is_even` at all.
In order to prove `s[3] % 2 == 0`,
we'd first have to mention `is_even(s[3])` explicitly:

```rust
{{#include ../../../rust_verify/example/guide/quants.rs:test_use_forall_succeeds1}}
```

Once the expression `is_even(s[3])` coaxes the SMT solver into instantiating the
`forall` expression with `i = 3`,
the SMT solver can use the resulting `0 <= 3 < s.len() ==> is_even(s[3])`
to prove `s[3] % 2 == 0`.

Alternatively, we could just choose a trigger that is less picky.
For example, the trigger `s[i]` matches any expression of the form
`s[...]`, which includes the `s[3]` inside `s[3] % 2 == 0` and
also includes the `s[3]` inside `is_even(s[3])`:

```rust
{{#include ../../../rust_verify/example/guide/quants.rs:test_use_forall_succeeds2}}
```

In fact, if we omit the `#[trigger]` attribute entirely,
Verus chooses the trigger `s[i]` automatically:

```rust
{{#include ../../../rust_verify/example/guide/quants.rs:test_use_forall_succeeds3}}
```

In fact, Verus prints a note stating that it chose this trigger:

```
note: automatically chose triggers for this expression:
   |
   |         forall|i: int| 0 <= i < s.len() ==> is_even(s[i]), // Verus chooses s[i] as the trigger
   |         ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

note:   trigger 1 of 1:
   |
   |         forall|i: int| 0 <= i < s.len() ==> is_even(s[i]), // Verus chooses s[i] as the trigger
   |                                                     ^^^^

note: Verus printed one or more automatically chosen quantifier triggers
      because it had low confidence in the chosen triggers.
```

Verus isn't sure, though,
whether the programmer wants `s[i]` as the trigger or `is_even(s[i])` as the trigger.
It slightly prefers `s[i]` because `s[i]` is smaller than `is_even(s[i])`,
so it chooses `s[i]`,
but it also prints out the note encouraging the programmer to review the decision.
The programmer can accept this decision by writing `#![auto]` before the quantifier body,
which suppresses the note:

```rust
{{#include ../../../rust_verify/example/guide/quants.rs:test_use_forall_succeeds4}}
```

## Good triggers and bad triggers

So ... which trigger is better, `s[i]` or `is_even(s[i])`?
Unfortunately, there's no one best answer to this kind of question.
There are tradeoffs between the two different choices.
The trigger `s[i]` leads to more pattern matches than `is_even(s[i])`.
More matches means that the SMT solver is more likely to find relevant
instantiations that help a proof succeed.
However, more matches also means that the SMT solver is more likely to generate
irrelevant instantiations that clog up the SMT solver with useless information,
slowing down the proof.

In this case, `s[i]` is probably a good trigger to choose.
It matches whenever the function `test_use_forall_succeeds4`
talks about an element of the sequence `s`,
yielding a fact that is likely to be useful for reasoning about `s`.
By contrast, suppose we chose the following bad trigger, `0 <= i`:

```rust
{{#include ../../../rust_verify/example/guide/quants.rs:test_use_forall_bad1}}
```

In principle, this would match any value that is greater than or equal to 0,
which would include values that have nothing to do with `s` and are unlikely
to be relevant to `s`.
In practice, Verus doesn't even let you do this:
triggers cannot contain equality or disequality (`==`, `===`, `!=`, or `!==`),
any basic integer arithmetic operator (like `<=` or `+`),
or any basic boolean operator (like `&&`):

```
error: trigger must be a function call, a field access, or a bitwise operator
    |
    |         forall|i: int| (#[trigger](0 <= i)) && i < s.len() ==> is_even(s[i]),
    |                        ^^^^^^^^^^^^^^^^^^^^
```

If we really wanted, we could work around this by introducing an extra function:

```rust
{{#include ../../../rust_verify/example/guide/quants.rs:test_use_forall_bad2}}
```

but this trigger fails to match, because the code doesn't explicitly mention `nonnegative(3)`
(you'd have to add an explicit `assert(nonnegative(3))` to make the code work).
This is probably just as well; `s[i]` is simply a better trigger than `nonnegative(i)`,
because `s[i]` mentions `s`, and the whole point of
`forall|i: int| 0 <= i < s.len() ==> is_even(s[i])`
is to say something about the elements of `s`,
not to say something about nonnegative numbers.
