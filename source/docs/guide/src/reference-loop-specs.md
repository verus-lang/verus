# Loop specifications

Loops are specified with 3 types of clauses, which take spec expressions.
To first approximation:

 * An `invariant_except_break` predicate is asserted at the beginning of each iteration.
 * An `ensures` predicate is asserted at the end of the loop.
 * An `invariant` predicate is asserted at the beginning of each iteration,
   and at the end of the loop.

However, in actuality, **Verus may enforce only a subset of these predicates**, depending on its
VC-gen strategy. In particular, when `loop_isolation` is set to `false`, nothing is asserted
at loop exit, making `ensures` defunct and `invariant` equivalent to `invariant_except_break`.
Below, we cover the different VC-gen cases in more detail.

Beginners should consult [the guide](while.md)
for a high-level intuition of what kind of specification is useful when.

## Loop desugaring

To start, we review the Rust-level de-sugaring of various loop kinds.
We also label two program points, the _loop-entry_ and _loop-exit_,
for our explanation below.

### Normal loop

User code:

```rust
loop {
    $user-body
}
```

Desugared (no desugaring):

```rust
loop {
    // loop-entry
    $user-body
}
// loop-exit
```

### While loop

User code:

```rust
while c {
    $user-body
}
```

Desugared (no desugaring):

```rust
loop {
    // loop-entry
    if c {
        $user-body
    } else {
        break;
    }
}
// loop-exit
```

### For loop

User code:

```rust
for e in $iterator {
    $user-body
}
```

Desugared:

```rust
let mut iter = $iterator;
loop {
    // loop-entry
    match iter.next() {
        Some(e) => {
            $user-body
        }
        None => {
            break;
        }
    }
}
// loop-exit
```

## VC gen

### `loop_isolation(false)`

A program containing a loop (`loop`, `while`, or `for`)

```
$pre-body
loop {
    $desugared-body
}
$post-body
```

is elaborated into VCs as follows:

```
$pre-body
assert (invariant predicates, invariant_except_break predicates)
HAVOC all vars which might be modified by the loop
assume (invariant predicates, invariant_except_break predicates)
$desugared-body
if iteration continues:
  assert (invariant predicates, invariant_except_break predicates)
if iteration breaks:
  $post-body
``` 

**Remarks**

 * The `ensures` clause is ignored
 * The `invariant_except_break` clause is equivalent to `invariant`
 * Any predicates on non-havoc'ed variables that follows from the $pre-body code will
   automatically be known in the verification of the loop body.

### `loop_isolation(true)` - "simple" while loop

A `while` loop is _simple_ if:
  * It has no break (other than the implicit 'break' from desugaring), and
  * It has no `invariant_except_break` clauses
  * It has no `ensures` clauses

A program containing a simple while loop:

```
$pre-body
while $condition {
    $user-body
}
$post-body
```

is elaborated into VCs as follows:

Outer VC:

```
$pre-body
assert invariant predicates
HAVOC all vars which might be modified by the loop
assume invariant predicates
let c = $condition
assume(!c);
$post-body
```

Inner VC:

```
assume invariant predicates
let c = $condition;
assume(c);
$pre-body
assert invariant predicates
```

**Remarks**

 * Any predicates, even those on non-havoc'ed variables, that follow from the $pre-body code are
   NOT automatically be known in the verification of the loop body.
 * Note that the final iteration, where the condition evaluates to `false`, is considered to be "outside the loop" from the perspetive of the VCs.
    * This means that the `invariant` predicates are _not_ necessarily enforced
     at the "real" loop exit.  The latest moment that
     `invariant` is enforced is _before_ the final evaluation of `$condition` where it evaluates
     to false. Technically, this is the start of the last iteration of the loop, not the exit.
     Thus, if `$condition` is not side-effect-free, then the invariant may be invalidated
     by the evaluation of `$condition`. In any scenario, the invariant is assumed
     in the outer VC, but before the evaluation of `$condition`, not after.

### `loop_isolation(true)` - other loops

A program containing a loop (`loop`, `while`, or `for`), which is not a "simple while loop":

```
$pre-body
loop {
    $desugared-body
}
$post-body
```

is elaborated into VCs as follows:

Outer VC:

```
$pre-body
assert invariant predicates
assert invariant_except_break predicates
HAVOC all vars which might be modified by the loop
assume invariant predicates
assume ensures predicates
$post-body
```

Inner VC:

```
assume invariant predicates
assume invariant_except_break predicates
$desugard-body
if iteration continues:
    assert invariant predicates
    assert invariant_except_break predicates
if iteration breaks:
    assert invariant predicates
    assert ensures predicates
```

**Remarks**

 * Any predicates, even those on non-havoc'ed variables, that follow from the $pre-body code are
   NOT automatically be known in the verification of the loop body.

