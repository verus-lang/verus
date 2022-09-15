# Recursive exec and proof functions, proofs by induction

The previous section introduced a specification for triangle numbers.
Given that, let's try a series of executable implementations of triangle numbers,
starting with a simple recursive implementation:

```rust
{{#include ../../../rust_verify/example/guide/recursion.rs:rec_fail}}
```

We immediately run into one small practical difficulty:
the implementation needs to use a finite-width integer to hold the result,
and this integer may overflow:

```
error: possible arithmetic underflow/overflow
   |
   |         n + rec_triangle(n - 1) // FAILS: possible overflow
   |         ^^^^^^^^^^^^^^^^^^^^^^^
```

Indeed, we can't expect the implementation to work if the result
won't fit in the finite-width integer type,
so it makes sense to add a precondition saying
that the result must fit,
which for a `u32` result means `triangle(n) < 0x1_0000_0000`:

```rust
{{#include ../../../rust_verify/example/guide/recursion.rs:rec}}
```

This time, verification succeeds.
It's worth pausing for a few minutes, though, to understand *why* the verification succeeds.
For example, an execution of `rec_triangle(10)`
performs 10 separate additions, each of which could potentially overflow.
How does Verus know that *none* of these 10 additions will overflow,
given just the initial precondition `triangle(10) < 0x1_0000_0000`?

The answer is that each instance of `triangle(n)` for `n != 0`
makes a recursive call to `triangle(n - 1)`,
and this recursive call must satisfy the precondition `triangle(n - 1) < 0x1_0000_0000`.
Let's look at how this is proved.
If we know `triangle(n) < 0x1_0000_0000` from `rec_triangle`'s precondition
and we use 1 unit of fuel to inline the definition of `triangle` once,
we get:

```
triangle(n) < 0x1_0000_0000
triangle(n) = if n == 0 { 0 } else { n + triangle(n - 1) }
```

In the case where `n != 0`, this simplifies to:

```
triangle(n) < 0x1_0000_0000
triangle(n) = n + triangle(n - 1)
```

From this, we conclude `n + triangle(n - 1) < 0x1_0000_0000`,
which means that `triangle(n - 1) < 0x1_0000_0000`,
since `0 <= n`, since `n` has type `u32`, which is nonnegative.

Intuitively, you can imagine that as `rec_triangle` executes,
proofs about `triangle(n) < 0x1_0000_0000` gets passed down the stack to the recursive calls,
proving `triangle(10) < 0x1_0000_0000` in the first call,
then `triangle(9) < 0x1_0000_0000` in the second call,
`triangle(8) < 0x1_0000_0000` in the third call,
and so on.
(Of course, the proofs don't actually exist at run-time ---
they are purely static and are erased before compilation ---
but this is still a reasonable way to think about it.)

## Towards an imperative implementation: mutation and tail recursion

The recursive implementation presented above is easy to write and verify,
but it's not very efficient, since it requires a lot of stack space for the recursion.
Let's take a couple small steps towards a more efficient, imperative implementation
based on while loops.
First, to prepare for the mutable variables that we'll use in while loops,
let's switch `sum` from being a return value to being a mutably updated variable:

```rust
{{#include ../../../rust_verify/example/guide/recursion.rs:mut}}
```

From the verification's point of view, this doesn't change anything significant.
Internally, when performing verification,
Verus simply represents the final value of `*sum` as a return value,
making the verification of `mut_triangle` essentially the same as
the verification of `rec_triangle`.

Next, let's try to eliminate the excessive stack usage by making the function
[tail recursive](https://en.wikipedia.org/wiki/Tail_call).
We do this by introducing and index variable `idx` that counts up from `0` to `n`,
just as a while loop would do:

```rust
{{#include ../../../rust_verify/example/guide/recursion.rs:tail_fail}}
```

In the preconditions and postconditions,
the expression `*old(sum)` refers to the initial value of `*sum`,
at the entry to the function,
while `*sum` refers to the final value, at the exit from the function.
The precondition `*old(sum) == triangle(idx as nat)` specifies that
as `tail_triangle` executes more and more recursive calls,
`sum` accumulates the sum `0 + 1 + ... + idx`.
Each recursive call increases `idx` by 1 until `idx` reaches `n`,
at which point `sum` equals `0 + 1 + ... + n` and the function simply returns `sum` unmodified.

When we try to verify `tail_triangle`, though, Verus reports an error about possible overflow:

```
error: possible arithmetic underflow/overflow
    |
    |         *sum = *sum + idx;
    |                ^^^^^^^^^^
```

This may seem perplexing at first:
why doesn't the precondition `triangle(n as nat) < 0x1_0000_0000`
automatically take care of the overflow,
as it did for `rec_triangle` and `mut_triangle`?

The problem is that we've reversed the order of the addition and the recursive call.
`rec_triangle` and `mut_triangle` made the recursive call first,
and then performed the addition.
This allowed them to prove all the necessary
facts about overflow first in the series of recursive calls
(e.g. proving `triangle(10) < 0x1_0000_0000`, `triangle(9) < 0x1_0000_0000`,
..., `triangle(0) < 0x1_0000_0000`.)
before doing the arithmetic that depends on these facts.
But `tail_triangle` tries to perform the arithmetic first,
before the recursion,
so it never has a chance to develop these facts from the original
`triangle(n) < 0x1_0000_0000` assumption.

## Proofs by induction

In the example of computing `triangle(10)`,
we need to know `triangle(0) < 0x1_0000_0000`,
then `triangle(1) < 0x1_0000_0000`,
and so on, but we only know `triangle(10) < 0x1_0000_0000` to start with.
If we somehow knew that
`triangle(0) <= triangle(10)`,
`triangle(1) <= triangle(10)`,
and so on,
then we could derive what we want from `triangle(10) < 0x1_0000_0000`.
What we need is a *lemma* that proves the if `i <= j`,
then `triangle(i) <= triangle(j)`.
In other words, we need to prove that `triangle` is monotonic.

We can use a `proof` function to implement this lemma:

```rust
{{#include ../../../rust_verify/example/guide/recursion.rs:mono}}
```

The proof is by induction on j,
where the base case of the induction is `i == j`
and the induction step relates `j - 1` to `j`.
In Verus, the induction step is implemented as a recursive call from the proof to itself
(in this example, this recursive call is line `triangle_is_monotonic(i, (j - 1) as nat)`).

As with recursive `spec` functions,
recursive `proof` functions must terminate and need a `decreases` clause.
Otherwise, it would be easy to prove `false`,
as in the following non-terminating "proof":

```rust
{{#include ../../../rust_verify/example/guide/recursion.rs:circular}}
```

We can use the `triangle_is_monotonic` lemma to complete the verification of `tail_triangle`:

```rust
{{#include ../../../rust_verify/example/guide/recursion.rs:tail}}
```

Intuitively, we can think of the call from `tail_triangle` to `triangle_is_monotonic`
as performing a similar recursive proof that `rec_triangle` and `mut_triangle`
performed as they proved their `triangle(n) < 0x1_0000_0000` preconditions
in their recursive calls.
In going from `rec_triangle` and `mut_triangle` to `tail_triangle`,
we've just shifted this recursive reasoning from the executable code into a separate recursive lemma.
