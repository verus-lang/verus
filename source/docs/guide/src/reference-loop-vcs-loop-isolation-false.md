# Loop verification with `loop_isolation=false`

### De-sugaring

Below we discuss the verification of an ordinary `loop { ... }` expression.
The `while` loops and `for` loops are de-sugared (in the standard Rust way)
approximately as follows:

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

</td></tr><tr><td>

```rust
for $pat in $iterable {
    $body
}
```

</td><td>

```rust
let mut iter = $iterable.into_iter();
loop {
    match iter.next() {
        None => { break; }
        Some($pat) => {
            $body
        }
    }
}
```

</td></tr></tbody></table></div>

### Verification

Given a program with a loop:

```rust
$pre
loop
    invariant $invariant
{
    $body
}
$post
```

Verus verifies it as if it were equivalent to the following pseudo-code.

```
$pre
assert($invariant);
havoc [all variables that could be mutated by $body]
assume($invariant);
$body
/* Set the `BREAK` flag if $body terminated via `break` statement, and
   set the `CONTINUE` flag if it terminated via `continue` statement or
   reached the end normally. */
if CONTINUE {
    assert($invariant);
} else if BREAK {
    $post
}
```
