# Recursive functions, decreases, fuel

Recursive functions are functions that call themselves.
In order to ensure soundness, a recursive `spec` function must terminate on all inputs ---
infinite recursive calls aren't allowed.
To see why termination is important, consider the following nonterminating function definition:

```rust
{{#include ../../../rust_verify/example/guide/recursion.rs:bogus}}
```

Verus rejects this definition because the recursive call loops infinitely, never terminating.
If Verus accepted the definion, then you could very easily prove false,
because, for example, the definition insists that `bogus(3) == bogus(3) + 1`,
which implies that `0 == 1`, which is false:

```rust
{{#include ../../../rust_verify/example/guide/recursion.rs:exploit_bogus}}
```

To help prove termination,
Verus requires that each recursive `spec` function definition contain a `decreases` clause:

```rust
{{#include ../../../rust_verify/example/guide/recursion.rs:spec}}
```

Each recursive call must decrease the expression in the `decreases` clause by at least 1.
Furthermore, the call cannot cause the expression to decrease below 0.
With these restrictions, the expression in the `decreases` clause serves as an upper bound on the
depth of calls that `triangle` can make to itself, ensuring termination.

# Fuel and reasoning about recursive functions

Given the definition of `triangle` above, we can make some assertions about it:

```rust
{{#include ../../../rust_verify/example/guide/recursion.rs:lacks_fuel}}
```

The first assertion, about `triangle(0)`, succeeds.
But somewhat surprisingly, the assertion `assert(triangle(10) == 55)` fails,
despite the fact that `triangle(10)` really is
[equal to 55](https://en.wikipedia.org/wiki/Triangular_number).
We've just encountered a limitation of automated reasoning:
SMT solvers cannot automatically prove all true facts about all recursive functions.

For nonrecursive functions,
an SMT solver can reason about the functions simply by inlining them.
For example, if we have a call `min(a + 1, 5)` to the [`min` function](spec_functions.md):

```rust
{{#include ../../../rust_verify/example/guide/recursion.rs:min}}
```

the SMT solver can replace `min(a + 1, 5)` with:

```
    if a + 1 <= 5 {
        a + 1
    } else {
        5
    }
```

which eliminates the call.
However, this strategy doesn't completely work with recursive functions,
because inlining the function produces another expression with a call to the same function:

```
triangle(x) = if x == 0 { 0 } else { x + triangle(x - 1) }
```

Naively, the solver could keep inlining again and again,
producing more and more expressions,
and this strategy would never terminate:

```
triangle(x) = if x == 0 { 0 } else { x + triangle(x - 1) }
triangle(x) = if x == 0 { 0 } else { x + (if x - 1 == 0 { 0 } else { x - 1 + triangle(x - 2) }) }
triangle(x) = if x == 0 { 0 } else { x + (if x - 1 == 0 { 0 } else { x - 1 + (if x - 2 == 0 { 0 } else { x - 2 + triangle(x - 3) }) }) }
```

To avoid this infinite inlining,
Verus limits the number of recursive calls that any given call can spawn in the SMT solver.
This limit is called the *fuel*;
each nested recursive inlining consumes one unit of fuel.
By default, the fuel is 1, which is just enough for `assert(triangle(0) == 0)` to succeed
but not enough for `assert(triangle(10) == 55)` to succeed.
To increase the fuel to a larger amount,
we can use the `reveal_with_fuel` directive:

```rust
{{#include ../../../rust_verify/example/guide/recursion.rs:fuel}}
```

Here, 11 units of fuel is enough to inline the 11 calls
`triangle(0)`, ..., `triangle(10)`.
Note that even if we only wanted to supply 1 unit of fuel,
we could still prove `assert(triangle(10) == 55)` through a long series of assertions:

```rust
{{#include ../../../rust_verify/example/guide/recursion.rs:step_by_step}}
```

This works because 1 unit of fuel is enough to prove `assert(triangle(0) == 0)`,
and then once we know that `triangle(0) == 0`,
we only need to inline `triangle(1)` once to get:

```
triangle(1) = if 1 == 0 { 0 } else { 1 + triangle(0) }
```

Now the SMT solver can use the previously computed `triangle(0)` to simplify this to:

```
triangle(1) = if 1 == 0 { 0 } else { 1 + 0 }
```

and then produce `triangle(1) == 1`.
Likewise, the SMT solver can then use 1 unit of fuel to rewrite `triangle(2)`
in terms of `triangle(1)`, proving `triangle(2) == 3`, and so on.
However, it's probably best to avoid long series of assertions if you can,
and instead write a proof that makes it clear why the SMT proof fails by default
(not enough fuel) and fixes exactly that problem:

```rust
{{#include ../../../rust_verify/example/guide/recursion.rs:fuel_by}}
```
