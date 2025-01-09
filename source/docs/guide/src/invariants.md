# Devising Invariants for Loops and Recursion

Below, we develop several examples that show how to work through
the process of devising invariants for loops
and for recursive functions.


## Example 1: Fibonacci

Suppose our goal is to compute values in the [Fibonacci sequence](https://en.wikipedia.org/wiki/Fibonacci_sequence).
We use a `spec` function `fib` to mathematically define our specification using `nat`s
and a recursive description:
```rust
{{#include ../../../rust_verify/example/guide/invariants.rs:fib_spec}}
```

Our goal is to write a more efficient iterative implementation as the `exec`
function `fib_impl`.  To keep things simple, we'll add a precondition to
`fib_impl` saying that the result needs to fit into a `u64` value.
We connect the correctness of `fib_impl`'s return value
to our mathematical specification in `fib_impl`'s `ensures` clause.
```rust
{{#include ../../../rust_verify/example/guide/invariants.rs:fib_impl_no_proof}}
```
However, if we ask Verus to verify this code, it reports two errors:
```
error: postcondition not satisfied
   |
   |           result == fib(n as nat),
   |           ----------------------- failed this postcondition
```
and 
```
error: possible arithmetic underflow/overflow
   |
   |         let new_cur = cur + prev;
   |                       ^^^^^^^^^^
```

Let's start by addressing the first failure.  It shouldn't be suprising that Verus
can't tell that we satisfy the postcondition, since our while loop doesn't have any
invariants.  This means that after the while loop terminates, Verus doesn't know
anything about what happened inside the loop, except that the loop's conditional (`i < n`)
no longer holds.  To fix this, let's try to craft an invariant that summarizes the work
we're doing inside the loop that we think will lead to satisfying the postcondition.
In this case, since we return `cur` and expect it to be `fib(n as nat)`, let's add
the invariant that `cur == fib(i as nat)`.

If we run Verus, we see that this still isn't enough to satisfy the
postcondition.  Why?  Let's think about what Verus knows after the loop
terminates.  It knows our invariant, and it knows `!(i < n)`, which is
equivalent to `i >= n`.  When we think about it this way, it's clear what the
problem is: Verus doesn't know that `i == n`!  Hence, we need another invariant
to relate `i` and `n` as the loop progresses.  We know `i` starts at 1, and it
should end at `n`, so let's add the invariant `1 <= i <= n`.  Notice that we
need to use `i <= n`, since in the last iteration of the loop, we will start
with `i == n - 1` and then increment `i`, and an invariant must always be
true after the loop body executes.

With this new invariant, Verus no longer reports an error about the postcondition,
so we've made progress!  To be explicit, after the loop terminates, Verus now
knows (thanks to our new invariant) that `i <= n`, and from the fact that the loop
terminates, it also knows that `i >= n`, so it can conclude that `i == n`, and hence
from the invariant that `cur == fib(i as nat)`, it now knows that `cur == fib(n as nat)`.

Unfortunately, Verus is still concerned about arithmetic underflow/overflow,
and it also reports a new error, saying that our new invariant about `cur`
doesn't hold.  Let's tackle the underflow/overflow issue first.  First, We can
deduce that the problem is a potential overflow (since we're adding two
non-negative numbers).  Second, We know from our precondition, that `fib(n as
nat)` will fit into a `u64`, but to use this information inside the while loop,
we need to add it as an invariant too.  See the earlier [discussion of loops
and invariants](while.md) for why this is the case.  This still isn't enough,
however.  We also need to know something about the value of `prev` if we want
to show that `cur + prev` will not overflow.  Since we're using `prev` to track
earlier values of Fibonacci, let's add `prev == fib((i - 1) as nat)` as an
invariant.

Despite these new invariants, Verus still reports the same error.  Why?  The issue
is that although we know that `fib(n as nat)` won't overflow, that doesn't necessarily
mean that `fib(i as nat)` won't overflow.  As humans, we know this is true, because
`i < n` and `fib` is monotonic (i.e., it always grows larger as its argument increases).
Proving this property, however, requires an [inductive proof](induction.md). Before writing
the proof itself, let's just state the property we want as a lemma and see if
it suffices to make our proof go through.  Here's the Verus version of the
informal propery we want.  We write it as a `proof` mode function, since its
only purpose is to establish this property.
```rust
{{#include ../../../rust_verify/example/guide/invariants.rs:fib_mono_no_proof}}
```
Verus can't yet prove this, but let's try invoking it in our while loop.
To call this lemma in our `exec` implementation, we employ
a `proof {}` block and pass in the relevant arguments.  At the call site, Verus checks
that the preconditions for `lemma_fib_is_monotonic` hold and then assumes that the postdconditions hold.
```rust
{{#include ../../../rust_verify/example/guide/invariants.rs:fib_final}}
```
We put the lemma invocation after the increment of `i`, so that it establishes that
`fib(i as nat) <= fib(n as nat)` for the new value of `i` that we're about to compute
by summing `cur` and `prev`.  With this lemma invocation, `fib_impl` now verifies!

We're not done yet, however.  We still need to prove `lemma_fib_is_monotonic`.  To
construct our inductive proof, we need to lay out the base cases, and then help
Verus with the inductive step(s).  Here's the basic skeleton:
```rust
{{#include ../../../rust_verify/example/guide/invariants.rs:fib_mono_skeleton}}
```
Notice that we've added `assume(false)` to the two trickier cases (following the approach
of [using assert and assume](assert_assume.md) to build our proof).  When we run
Verus, it succeeds, indicating that Verus doesn't need any help with our base cases.
However, if we remove the first `assume(false)`, Verus reports that the postcondition
is not satisfied, confirming that it needs help here.  We can help Verus by (essentially)
telling it to unfold the definition of `fib(j)` one level, i.e., by writing:
```rust
assert(fib(j) == fib((j - 2) as nat) + fib((j - 1) as nat));
```
In this case, that's enough to complete this branch of the proof, since Verus knows that
`fib((j - 1) as nat) == fib(i as nat)`, and the assertion shows that `fib(j)` cannot be
less than `fib(i as nat)` (since `fib` returns non-negative values).

The final portion of the proof, however, needs more help (you can confirm this by
adding the same assertion we used above; the assertion passes, but the postcondition still fails).
The key idea here is to use our induction hypothesis to show that `fib(i)`
is smaller than both `fib(j - 1)` and `fib(j - 2)`.  We do this via two recursive invocations
of `lemma_fib_is_monotonic`.  Note that adding recursive calls means we need to add a decreases clause.
In this case, we're decreasing the distance between `j` and `i`, so `j - i` works.
```rust
{{#include ../../../rust_verify/example/guide/invariants.rs:fib_is_mono}}
```
With these additions, the proof succeeds, meaning that our entire program now verifies successfully!
