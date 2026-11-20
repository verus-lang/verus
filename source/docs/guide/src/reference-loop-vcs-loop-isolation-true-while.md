# Loop verification of `while` with `loop_isolation=true`

The handling of a `while` loop depends on whether or not it contains a `break` statement.

### For a `while` loop with `break`

For a `while` loop with a `break` statement, Verus verifies the `while` loop identically
[to an ordinary `loop`](./reference-loop-vcs-loop-isolation-true-loop.md), using the following de-sugaring (which adds an additional `break`):

<div class="table-wrapper">
<table>
<thead>
<tr><th>Source</th><th>De-sugared</th></tr>
</thead>
<tbody>
<tr><td>

```rust
while $conditional {
    $body
}
```

</td><td>

```rust
loop {
    if $conditional {
        $body
    } else {
        break;
    }
}
```

</td></tr></tbody></table></div>

### For a `while` loop with no `break`

With no `break` statement, the only way to reach the loop exit is for the conditional expression
to return false.
We therefore put the final iteration of the loop, the one where the conditional returns false,
in the outer query. Thus, the final, breaking iteration is not treated the same as the
"ordinary" iterations.

Given a program with a `while` loop:

```rust
$pre
while $condition
    invariant $invariant
{
    $body
}
$post
```

Verus verifies this as if it were equivalent to the following two pieces of pseudo-code,
each handled separately.

The **"outer query"** represents the code enclosing the loop.

```
$pre
assert($invariant);
havoc [all variables that could be mutated by $body]
assume($invariant);
let cond = $condition;
assume(!cond);
$post
```

The **"inner query"** represents the interior of the loop.

```
assume($invariant);
let cond = $condition;
assume(cond);
$body
assert($invariant);
```

### Examples

!cond is automatically upheld
!cond is not automatically upheld for a breaking case

conditional-evaluation violating invariant
