# Example: binary search

Let's see how `forall` and `exists` work in a larger example.
The following code searches for a value `k` in a sorted sequence
and returns the index `r` where `k` resides.

```rust
{{#include ../../../rust_verify/example/guide/quants.rs:binary_search}}
```

The precondition `exists|i: int| 0 <= i < v.len() && k == v[i]`
specifies that `k` is somewhere in the sequence,
so that the search is guaranteed to find it.
The automatically inferred trigger for this `exists` expression is `v[i]`.
The `main` function satisfies this with the witness `i = 3` so that `30 == v[3]`:

```
assert(v[3] == 30); // needed to trigger exists|i: int| ... k == v[i]
let r = binary_search(&v, 30);
```

The search proceeds by keeping two indices `i1` and `i2` that
narrow in on `k` from both sides,
so that the index containing `k` remains between `i1` and `i2`
throughout the search:

```
exists|i: int| i1 <= i <= i2 && k == v[i]
```

In order for the loop to exit, the loop condition `i1 != i2` must be false,
which means that `i1` and `i2` must be equal.
In this case, the `i` in the `exists` expression above must be equal to `i1` and `i2`,
so we know `k == v[i1]`,
so that we can return the result `i1`.

## Proving that the loop invariant is maintained

In each loop iteration, we can assume that the loop invariants hold before the iteration,
and we have to prove that the loop invariants hold after the iteration.
Let's look in more detail at the proof of the invariant
`exists|i: int| i1 <= i <= i2 && k == v[i]`,
focusing on how the SMT solver handles the `forall` and `exists` quantifiers.

The key steps are:
- Knowing `exists|i: int| ... k == v[i]` gives us a witness `i_witness`
  such that `k == v[i_witness]`.
- The witness `i_witness` from the current iteration's
  `exists|i: int| ...` serves as the witness for the next iteration's
  `exists|i: int| ...`.
- The comparison `*v.index(ix) < k` tells us whether `v[ix] < k` or `v[ix] >= k`.
- The expressions `v[i_witness]` and `v[ix]` match the trigger `v[i], v[j]` trigger
  in the expression `forall|i: int, j: int| ... v[i] <= v[j]`.

We'll now walk through these steps in more detail.
(Feel free to [skip ahead](./binary_search.md#helping-the-automation-succeed) if this is too boring ---
as the next subsection discusses,
the whole point is that the SMT solver takes care of the boring details automatically
if we set things up right.)

There are two cases to consider, one where the `if` condition `*v.index(ix) < k` is true and one
where `*v.index(ix) < k` is false.
We'll just look at the former, where `v[ik] < k`.

We assume the loop invariant at the beginning of the loop iteration:

```
exists|i: int| i1 <= i <= i2 && k == v[i]
```

This tells us that there is some witness `i_witness` such that:

```
i1 <= i_witness <= i2 && k == v[i_witness]
```

In the case where `*v.index(ix) < k` is true, we execute `i1 = ix + 1`:

```rust
let ix = i1 + (i2 - i1) / 2;
if *v.index(ix) < k {
    i1 = ix + 1;
} else {
```

Since the new value of `i1` is `ix + 1`,
we'll need to prove the loop invariant with `ix + 1` substituted for `i1`:

```
exists|i: int| ix + 1 <= i <= i2 && k == v[i]
```

To prove an `exists` expression, the SMT solver needs to match the expression's trigger.
The automatically chosen trigger for this expression is `v[i]`,
so the SMT solver looks for expressions of the form `v[...]`.
It finds `v[i_witness]` from the previous loop invariant (shown above).
It also finds `v[ix]` from the call `v.index(ix)` in the expression `*v.index(ix) < k`.
Based on these, it attempts to prove `ix + 1 <= i <= i2 && k == v[i]`
with `i = i_witness` or `i = ix`:

```
ix + 1 <= i_witness <= i2 && k == v[i_witness]
ix + 1 <= ix <= i2 && k == v[ix]
```

The `i = ix` case is a dead end, because `ix + 1 <= ix` is never true.
The `i = i_witness` case is more promising.
We already know `i_witness <= i2` and `k == v[i_witness]`
from our assumptions about `i_witness` at the beginning of the loop iteration.
We just need to prove `ix + 1 <= i_witness`.
We can simplify this to `ix < i_witness`.

#### Proving ix < i_witness

To prove `ix < i_witness`, we now turn to the `forall` loop invariant:

```
forall|i: int, j: int| 0 <= i <= j < v.len() ==> v[i] <= v[j],
```

In order to instantiate this, the SMT solver again relies on triggers.
In this `forall`, expression, the trigger is `v[i], v[j]`,
so again the SMT solver looks for terms of the form `v[...]`
and finds `v[i_witness]` and `v[ix]`.
There are four different possible assignments of `i_witness` and `ix` to `i` and `j`.

```
0 <= i_witness <= i_witness < v.len() ==> v[i_witness] <= v[i_witness]
0 <= i_witness <= ix < v.len() ==> v[i_witness] <= v[ix]
0 <= ix <= i_witness < v.len() ==> v[ix] <= v[i_witness]
0 <= ix <= ix < v.len() ==> v[ix] <= v[ix]
```

Out of these, the second one is most useful:

```
0 <= i_witness <= ix < v.len() ==> v[i_witness] <= v[ix]
```

We already know `k == v[i_witness]`, so this becomes:

```
0 <= i_witness <= ix < v.len() ==> k <= v[ix]
```

The right-hand side of the `==>` says `k <= v[ix]`,
which contradicts our assumption that `v[ik] < k` in the case where `*v.index(ix) < k`.
This means that the left-hand side of the `==>` must be false:

```
!(0 <= i_witness <= ix < v.len())
```

The SMT solver knows that `0 <= i_witness` and `ix < v.len()`,
so it narrows this down to:

```
!(i_witness <= ix)
```

This tells us that `ix < i_witness`, which is what we want.

## Helping the automation succeed

As seen in the previous section,
proving the loop invariant requires a long chain of reasoning.
Fortunately, the SMT solver performs all of these steps automatically.
In fact, this is a particularly fortunate example,
because Verus automatically chooses the triggers as well,
and these triggers happen to be just what the SMT solver needs to complete the proof.

In general, though, how we express the preconditions, postconditions,
and loop invariants has a big influence on whether Verus and the SMT solver
succeed automatically.
Suppose, for example, that we had written the sortedness condition
(in the precondition and loop invariant) as:

```
forall|i: int| 0 <= i < v.len() - 1 ==> #[trigger] v[i] <= v[i + 1]
```

instead of:

```
forall|i: int, j: int| 0 <= i <= j < v.len() ==> v[i] <= v[j]
```

As discussed in a [previous section](./multitriggers.md),
the trigger `v[i]` in combination with `v[i] <= v[i + 1]` leads to a matching loop,
which can send the SMT solver into an infinite loop.
This is, in fact, exactly what happens:

```
error: while loop: Resource limit (rlimit) exceeded; consider rerunning with --profile for more details
    |
    | /     while i1 != i2
    | |         invariant
    | |             i2 < v.len(),
    | |             exists|i: int| i1 <= i <= i2 && k == v[i],
      |
    | |         }
    | |     }
    | |_____^
```

Even if the SMT solver had avoided the infinite loop, though,
it's hard to see how it could have succeeded automatically.
As discussed above, a crucial step involves instantiating
`i = i_witness` and `j = ix` to learn something about `v[i_witness] <= v[ix]`.
This simply isn't a possible instantiation when there's only one variable `i`
in the `forall` expression.
Learning something about `v[i_witness] <= v[ix]` would require chaining together
an arbitrarily long sequence of `v[i] <= v[i + 1]` steps to get from
`i_witness` to `i_witness + 1` to `i_witness + 2` all the way to `ix`.
This would require a separate proof by induction.
Intuitively, the expression `v[i] <= v[j]`
is better suited than `v[i] <= v[i + 1]`
to an algorithm like binary search that takes large steps from one index to another,
because `i` and `j` can be arbitrarily far apart,
whereas `i` and `i + 1` are only one element apart.

When the SMT automation fails, it's often tempting to immediately start adding `assert`s,
lemmas, proofs by induction, etc., until the proof succeeds.
Given enough manual effort, we could probably finish a proof of binary search with the problematic
`v[i] <= v[i + 1]` definition of sortedness.
But this would be a mistake;
it's better to structure the definitions in a way that helps the automation succeed
without so much manual effort.
If you find yourself writing a long manual proof,
it's worth stepping back and figuring out why the automation is failing;
maybe a change of definitions can fix the failure in the automation.

After all, if your car breaks down, it's usually better to fix the car than to push it.
