# Devising Loop Invariants

Below, we develop several examples that show how to work through
the process of devising invariants for loops.

## Example 1: Fibonacci

Suppose our goal is to compute values in the [Fibonacci sequence](https://en.wikipedia.org/wiki/Fibonacci_sequence).
We use a `spec` function `fib` to mathematically define our specification using `nat`s
and a recursive description:
```rust
{{#include ../../../../examples/guide/invariants.rs:fib_spec}}
```

Our goal is to write a more efficient iterative implementation as the `exec`
function `fib_impl`.  To keep things simple, we'll add a precondition to
`fib_impl` saying that the result needs to fit into a `u64` value.
We connect the correctness of `fib_impl`'s return value
to our mathematical specification in `fib_impl`'s `ensures` clause.
```rust
{{#include ../../../../examples/guide/invariants.rs:fib_impl_no_proof}}
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

Let's start by addressing the first failure.  It shouldn't be surprising that Verus
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

With this new invariant, Verus no longer reports an error about the
postcondition, so we've made progress!  To be explicit about the progress we've
made, after the loop terminates, Verus now knows (thanks to our new invariant)
that `i <= n`, and from the fact that the loop terminates, it also knows that
`i >= n`, so it can conclude that `i == n`, and hence from the invariant that
`cur == fib(i as nat)`, it now knows that `cur == fib(n as nat)`.

Unfortunately, Verus is still concerned about arithmetic underflow/overflow,
and it also reports a new error, saying that our new invariant about `cur`
doesn't hold.  Let's tackle the underflow/overflow issue first.  Note that we can
deduce that the problem is a potential overflow, since we're adding two
non-negative numbers.  We also know from our precondition that `fib(n as
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
informal property we want.  We write it as a `proof` mode function, since its
only purpose is to establish this property.
```rust
{{#include ../../../../examples/guide/invariants.rs:fib_mono_no_proof}}
```
Verus can't yet prove this, but let's try invoking it in our while loop.
To call this lemma in our `exec` implementation, we employ
a `proof {}` block and pass in the relevant arguments.  At the call site, Verus checks
that the preconditions for `lemma_fib_is_monotonic` hold and then assumes that the postconditions hold.
```rust
{{#include ../../../../examples/guide/invariants.rs:fib_final}}
```
We put the lemma invocation after the increment of `i`, so that it establishes that
`fib(i as nat) <= fib(n as nat)` for the new value of `i` that we're about to compute
by summing `cur` and `prev`.  With this lemma invocation, `fib_impl` now verifies!

We're not done yet, however.  We still need to prove `lemma_fib_is_monotonic`.  To
construct our inductive proof, we need to lay out the base cases, and then help
Verus with the inductive step(s).  Here's the basic skeleton:
```rust
{{#include ../../../../examples/guide/invariants.rs:fib_mono_skeleton}}
```
Notice that we've added `assume(false)` to the final tricky case (following the approach
of [using assert and assume](assert_assume.md) to build our proof).  When we run
Verus, it succeeds, indicating that Verus doesn't need any help with our base cases.
The final portion of the proof, however, needs more help (you can confirm this by
by removing the `assume(false)` and observing that the proof fails).
The key idea here is to use our induction hypothesis to show that `fib(i)`
is smaller than both `fib(j - 1)` and `fib(j - 2)`.  We do this via two recursive invocations
of `lemma_fib_is_monotonic`.  Note that adding recursive calls means we need to add a decreases clause.
In this case, we're decreasing the distance between `j` and `i`, so `j - i` works.
```rust
{{#include ../../../../examples/guide/invariants.rs:fib_is_mono}}
```
With these additions, the proof succeeds, meaning that our entire program now verifies successfully!


## Example 2: Account Balance

In this example, we're given a slice of `i64` values that represent a series of deposits and 
withdrawals from a bank account.  The goal is to determine whether the account's balance ever
drops below 0. We formalize this requirement with the spec function `always_non_negative`,
which is itself defined in terms of computing a sum of the first `i` elements in a sequence of `i64` values.
```rust
{{#include ../../../../examples/guide/invariants.rs:bank_spec}}
```

In our implementation, as usual, we tie the concrete result `r` to our spec
in the ensures clause.
```rust
{{#include ../../../../examples/guide/invariants.rs:bank_no_proof}}
```
Note that we use an `i128` to compute the account's running 
sum since it allows us to have sufficiently large numbers without overflowing.
As an exercise, you can try modifying the implementation to use an `i64` for
the sum instead, adding any additional invariants and proofs you need.
Here we use a `for` loop instead of a `while` loop, which means that we get a free
invariant that `0 <= i <= operations.len()`.  As before, however, that's not
enough to prove our postcondition or even to rule out overflow; Verus reports:
```rust
error: postcondition not satisfied
   |
   |           r == always_non_negative(operations@),
   |           ------------------------------------- failed this postcondition
   | / {
   | |     let mut s = 0i128;
   | |     for i in 0usize..operations.len()
   | |     {
...  |
   | |     true
   | | }
   | |_^ at the end of the function body

error: possible arithmetic underflow/overflow
   |
   |         s = s + operations[i] as i128;
   |             ^^^^^^^^^^^^^^^^^^^^^^^^^

```

Let's address the possible underflow/overflow first.  Why don't we expect this to happen?
Well, we don't expect underflow because we start with `s = 0`, and if at any point `s` goes
below 0, we immediately return.  How far can `s` go below 0? At worst, we might subtract `i64::MIN`
from 0, so we can argue that `i64::MIN <= s` is an invariant.  To rule out overflow, we need
to consider how large `s` can grow.  A simple bound is to say that if we add `i` `i64` values
together, the sum must be bounded by `i64::MAX * i`.  Putting this together, we can add a loop
invariant that says `i64::MIN <= s <= i64::MAX * i`.  With this invariant in place, Verus no
longer complains about possible arithmetic underflow/overflow.

Now let's address functional correctness, so that we can prove the postcondition holds.  As before,
we want our loop invariants to summarize the progress that we've made towards the postcondition,
ideally in a form such that when the loop terminates, the invariant nicely matches up with the
expression in the postcondition.  A first step in this direction is to make it explicit that `s`
represents the sum of the values up to `i`; i.e., `s == sum(operations@.take(i as int))`.  We
also need to keep track of the fact that we've checked each individual sum to confirm that it's non-negative.
In other words, we need `forall|j: int| 0 <= j <= i ==> sum(#[trigger] operations@.take(j)) >= 0`.
With these additions, Verus produces new complaints:
```rust
error: invariant not satisfied at end of loop body
   |
   |             s == sum(operations@.take(i as int)),
   |             ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

error: postcondition not satisfied
   |
   |         r == always_non_negative(operations@),
   |         ------------------------------------- failed this postcondition
...
   |             return false;
   |             ^^^^^^^^^^^^ at this exit
```
Are these two different issues or two symptoms of the same underlying issue?  One way to check this
is by assuming that the first one is true and seeing what happens to the second error.  In other words,
we update the body of the loop to be:
```rust
s = s + operations[i] as i128;
assume(s == sum(operations@.take((i + 1) as int)));
if s < 0 {
    return false;
}
```
It turns out this assumption eliminates both errors, so we really only need to convince Verus that
we've correctly computed the sum of the first `i+1` operations.  If we let `ops_i_plus_1` be `operations@.take((i + 1) as int)` and unfold the definition of `sum`,
we can see that `sum(ops_i_plus_1) == sum(ops_i_plus_1.drop_last()) + ops_i_plus_1.last()`.
This means Verus is having trouble determining that the right-hand side matches the value we computed
(namely `s + operations[i]`).  Lets check that the second term in the two sums match, namely:
```rust
assert(operations[i as int] == ops_i_plus_1.last());
```
That succeeds, so the problem must be showing that `s` 
(which we know from our invariant is `sum(operations@.take(i as int))`) is equal to `sum(ops_i_plus_1.drop_last())`.
Clearly, these two values would be equal if the arguments to sum were equal, so let's see if Verus can prove that,
which we can check by writing:
```rust
assert(operations@.take(i as int) == ops_i_plus_1.drop_last());
```
Verus is able to verify this assertion, and not only that, it can then prove our previous assumption that
`s == sum(operations@.take((i + 1) as int)`, hence completing our proof.  Why does this work?  Stating the
assertion causes Verus to invoke axioms about [sequence extensionality](spec_lib.md), i.e., the conditions
under which two sequences are equal, which then allows it to prove our sequences are equal, which proves
the sums are equal, which completes the proof.

Here's the full version of the verifying implementation.
```rust
{{#include ../../../../examples/guide/invariants.rs:bank_final}}
```

