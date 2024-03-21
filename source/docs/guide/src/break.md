# Loops with break

Loops can exit early using `return` or `break`.
Suppose, for example, we want to remove the requirement
`triangle(n as nat) < 0x1_0000_0000` from the `loop_triangle` function,
and instead check for overflow at run-time.
The following version of the function uses `return` to return
the special value `0xffff_ffff` in case overflow is detected at run-time:

```rust
{{#include ../../../rust_verify/example/guide/recursion.rs:loop_return}}
```

Another way to exit early from a loop is with a `break` inside the loop body.
However, `break` complicates the specification of a loop slightly.
For simple `while` loops without a `break`,
Verus knows that the loop condition (e.g. `idx < n`)
must be false after exiting the loop.
If there is a `break`, though, the loop condition is not necessarily false
after the loop, because the `break` might cause the loop to exit even when
the loop condition is true.
To deal with this, `while` loops with a `break`,
as well as Rust `loop` expressions (loops with no condition),
must explicitly specify what is true after the loop exit using `ensures` clauses,
as shown in the following code.
Furthermore, invariants that don't hold after a `break`
must be marked as `invariant_except_break` rather than `invariant`:

```rust
{{#include ../../../rust_verify/example/guide/recursion.rs:loop_break}}
```
