# spec functions vs. proof functions

Now that we've seen both `spec` functions and `proof` functions,
let's take a longer look at the differences between them.
We can summarize the differences in the following table
(including `exec` functions in the table for reference):

|                              | spec function     | proof function   | exec function    |
|------------------------------|-------------------|------------------|------------------|
| compiled or ghost            | ghost             | ghost            | compiled         |
| code style                   | purely functional | mutation allowed | mutation allowed |
| can call `spec` functions    | yes               | yes              | yes              |
| can call `proof` functions   | no                | yes              | yes              |
| can call `exec` functions    | no                | no               | yes              |
| body visibility              | may be visible    | never visible    | never visible    |
| body                         | body optional     | body mandatory   | body mandatory   |
| determinism                  | deterministic     | nondeterministic | nondeterministic |
| preconditions/postconditions | recommends        | requires/ensures | requires/ensures |

As described in the [spec functions](spec_functions.md) section,
`spec` functions make their bodies visible to other functions in their module
and may optionally make their bodies visible to other modules as well.
`spec` functions can also omit their bodies entirely:

```
spec fn f(i: int) -> int;
```

Such an [uninterpreted function](https://microsoft.github.io/z3guide/docs/logic/Uninterpreted-functions-and-constants)
can be useful in libraries that define an abstract, uninterpreted function along with trusted axioms
about the function.

## Determinism

`spec` functions are deterministic:
given the same arguments, they always return the same result.
Code can take advantage of this determinism even when a function's body
is not visible.
For example, the assertion `x1 == x2` succeeds in the code below,
because both `x1` and `x2` equal `s(10)`,
and `s(10)` always produces the same result, because `s` is a `spec` function:

```rust
{{#include ../../../rust_verify/example/guide/modes.rs:determinism}}
```

By contrast, the proof function `p` is, in principle,
allowed to return different results each time it is called,
so the assertion `p1 == p2` fails.
(Nondeterminism is common for `exec` functions
that perform input-output operations or work with random numbers.
In practice, it would be unusual for a `proof` function to behave nondeterministically,
but it is allowed.)

## recommends

`exec` functions and `proof` functions can have `requires` and `ensures` clauses.
By contrast, `spec` functions cannot have `requires` and `ensures` clauses.
This is similar to the way [Boogie](https://github.com/boogie-org/boogie) works,
but differs from other systems like [Dafny](https://github.com/dafny-lang/dafny)
and [F*](https://github.com/FStarLang/FStar).
The reason for disallowing requires and ensures is to keep Verus's specification language
close to the SMT solver's mathematical language in order to use the SMT solver as efficiently
as possible (see the [Verus Overview](overview.md)).

Nevertheless, it's sometimes useful to have some sort of preconditions on `spec` functions
to help catch mistakes in specifications early or to catch accidental misuses of `spec` functions.
Therefore, `spec` functions may contain `recommends` clauses
that are similar to `requires` clauses,
but represent just lightweight recommendations rather than hard requirements.
For example, for the following function,
callers are under no obligation to obey the `i > 0` recommendation:

```rust
{{#include ../../../rust_verify/example/guide/modes.rs:recommends1}}
```

It's perfectly legal for `test1` to call `f(0)`, and no error or warning will be generated for `g`
(in fact, Verus will not check the recommendation at all).
However, *if* there's a verification error in a function,
Verus will automatically rerun the verification with recommendation checking turned on,
in hopes that any recommendation failures will help diagnose the verification failure.
For example, in the following:

```rust
{{#include ../../../rust_verify/example/guide/modes.rs:recommends2}}
```

Verus print the failed assertion as an error and then prints the failed recommendation as a note:

```
error: assertion failed
    |
    |     assert(f(0) <= f(1)); // FAILS
    |            ^^^^^^^^^^^^ assertion failed

note: recommendation not met
    |
    |     recommends i > 0
    |                ----- recommendation not met
...
    |     assert(f(0) <= f(1)); // FAILS
    |            ^^^^^^^^^^^^
```

If the note isn't helpful, programmers are free to ignore it.

By default, Verus does not perform `recommends` checking on calls from `spec` functions:

```rust
{{#include ../../../rust_verify/example/guide/modes.rs:recommends3}}
```

However, you can write `spec(checked)` to request `recommends` checking,
which will cause Verus to generate warnings for `recommends` violations:

```rust
{{#include ../../../rust_verify/example/guide/modes.rs:recommends4}}
```

This is particularly useful for specifications that are part of the "trusted computing base"
that describes the interface to external, unverified components.
