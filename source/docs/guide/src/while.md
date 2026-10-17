# Loops and invariants

The previous section developed a tail-recursive implementation of `triangle`:

```rust
{{#include ../../../../examples/guide/recursion.rs:tail}}
```

We can rewrite this as a `while` loop as follows:

```rust
{{#include ../../../../examples/guide/recursion.rs:loop}}
```

The loop is quite similar to the tail-recursive implementation.
(In fact, internally, Verus verifies the loop as if it were its own function,
separate from the enclosing `loop_triangle` function.)
Where the tail-recursive function had preconditions,
the loop has *loop invariants* that describe what must
be true before and after each iteration of the loop.
For example, if `n = 10`,
then the loop invariant must be true 11 times:
before each of the 10 iterations,
and after the final iteration.

Notice that the invariant `idx <= n` allows for the possibility that `idx == n`,
since this will be the case after the final iteration.
If we tried to write the invariant as `idx < n`,
then Verus would fail to prove that the invariant is maintained after the final iteration.

After the loop exits,
Verus knows that `idx <= n` (because of the loop invariant)
and it knows that the loop condition `idx < n` must have been false
(otherwise, the loop would have continued).
Putting these together allows Verus to prove that `idx == n` after exiting the loop.
Since we also have the invariant `sum == triangle(idx as nat)`,
Verus can then substitute `n` for `idx` to conclude `sum == triangle(n as nat)`,
which proves the postcondition of `loop_triangle`.

Just as verifying functions requires some programmer effort to write
appropriate preconditions and postconditions,
verifying loops requires programmer effort to write loop invariants.
The loop invariants have to be neither too weak (`invariant true` is usually too weak)
nor too strong (`invariant false` is too strong),
so that:
- the invariants hold upon the initial entry to the loop
  (e.g. `idx <= n` holds for the initial value `idx = 0`, since `0 <= n`)
- the invariant still holds at the end of the loop body,
  so that the invariant is maintained across loop iterations
- the invariant is strong enough to prove the properties we want
  to know after the loop exits (e.g. to prove `loop_triangle`'s postcondition)

As mentioned above,
Verus verifies the loop separately from the function that contains the loop
(e.g. separately from `loop_triangle`).
This means that the loop does not automatically inherit preconditions
like `triangle(n as nat) < 0x1_0000_0000` from the surrounding function ---
if the loop relies on these preconditions,
they must be listed explicitly in the loop invariants.
(The reason for this is to improve the efficiency of the SMT solving
for large functions with large while loops;
verification runs faster if Verus breaks the surrounding function and the loops into separate pieces
and verifies them modularly.)

`reveal`, `reveal_with_fuel`, and `broadcast use` are exceptions to that split.
A directive that is in scope where the loop starts is available inside the loop,
including inside nested loops, and it keeps the unfolding depth chosen by
`reveal_with_fuel`. The same directive is available when it appears in the
statements of a `loop_isolation` boundary that belong to that loop.
A directive that appears only in another branch, only after the loop, or only
in a loop that has already finished stays in that context.
Assertions and preconditions about program state still have to be invariants.

`hide` applies to the whole function. It suppresses default unfolding in every
query for that function, and a later `reveal` or `reveal_with_fuel` turns
unfolding back on from that point, including in later isolated loops.
Using `hide` to cancel an outer `reveal` or `broadcast use` inside only one
loop is an open design question; Verus does not do that today.

Verus does allow you to opt-out of this behavior, meaning that your loops will inherit
information from the surrounding context.  This will simplify your loop invariants,
but verification time may increase for medium-to-large functions.
To opt-out for a single function or while loop, you can add the attribute 
`#[verifier::loop_isolation(false)]`.  You can also opt-out at the module or
crate level, by adding the `#![verifier::loop_isolation(false)]` attribute
to the module or the root of the crate.  You can then override the global
setting locally by adding `#[verifier::loop_isolation(true)]` on individual
functions or loops.

