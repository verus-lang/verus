# Proving Absence of Overflow

Whenever Verus executable code performs a mathematical operation on
concrete (non-ghost) variables, Verus makes sure that it doesn't overflow.
This is useful because it prevents unexpected overflow (a common bug) and
because it allows simpler reasoning, e.g., not forcing the SMT solver to
reason about the possibility that `x + y` results in `(x + y) % pow(2,
32)`. However, it creates an obligation on the developer to prove that
every one of their operations can't overflow. We saw in the previous
section about [Devising loop invariants](invariants.md) that this
necessitates additional proof work.

One way to deal with this is to place explicit bounds on variables'
values so that the solver can infer that the code can't overflow. For
instance, the following simple function to compute a sum fails to verify because it
might overflow:
```rust
{{#include ../../../../examples/guide/overflow.rs:compute_sum_fails}}
```
But this version succeeds at verification because the solver can easily tell
that the bounds prevent overflow:
```rust
{{#include ../../../../examples/guide/overflow.rs:compute_sum_limited}}
```

Another way to deal with overflow is to explicitly check for it at
runtime. For this, one can use operations from the Rust standard library
like `checked_add` and `checked_mul`. These operations return an `Option`,
with the value `None` indicating that an overflow would have resulted.
Verus includes specifications for these, enabling their direct use.
This example illustrates how:
```rust
{{#include ../../../../examples/guide/overflow.rs:compute_sum_runtime_check}}
```

This works well for single operations, but performing multiple chained
operations of addition and/or multiplication is trickier. This is because
whenever overflow occurs one has to stop, and it's not clear that the
entire chain of operations collectively would have overflowed. For this
circumstance, the Verus standard library includes structs named
`CheckedU8`, `CheckedU16`, etc. Each of these can continue operating even
after it overflows, maintaining its true non-overflowing value in ghost
state. To see the value in this, consider the Fibonacci example from the
previous section about [Devising loop invariants](invariants.md). If we use
`CheckedU64`, as in the following example, we don't need to invoke
`lemma_fib_is_monotonic` to prove that the result can't overflow:
```rust
{{#include ../../../../examples/guide/invariants.rs:fib_checked}}
```
There is a small cost in performance and memory footprint, since the
checked versions consist of a runtime `Option<u64>` instead of a `u64`, but
in return the code is simpler. Another advantage is that we can remove the
precondition mandating that the result must fit in a `u64`, and correctly
handle the possibility of overflow:
```rust
{{#include ../../../../examples/guide/invariants.rs:fib_checked_no_precondition}}
```
