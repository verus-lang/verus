# Loop verification of `loop` with `loop_isolation=true`

Given a program with a plain `loop`:

```rust
$pre
loop
    invariant $invariant
    invariant_except_break $invariant_except_break
    ensures $ensures
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
assert($invariant_except_break);
havoc [all variables that could be mutated by $body]
assume($invariant);
assume($ensures);
$post
```

The **"inner query"** represents the interior of the loop.

```
assume($invariant);
assume($invariant_except_break);
$body
/* Set the `BREAK` flag if $body terminated via `break` statement, and
   set the `CONTINUE` flag if it terminated via `continue` statement or
   reached the end normally. */
if CONTINUE {
    assert($invariant);
    assert($invariant_except_break);
} else if BREAK {
    assert($invariant);
    assert($ensures);
}
```

### Examples


