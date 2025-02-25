# Rust subset

Much of the spec language looks like a subset of the Rust language, though
there are some subtle differences.

### Function calls

Only pure function calls are allowed (i.e., calls to other `spec` functions or
functions marked with the `when_used_as_spec` directive).

### Let-assignment

Spec expressions support `let`-bindings, but not `let mut`-bindings.

### if / if let / match statements

These work as normal.

### `&&` and `||`

These work as normal, though as all spec expressions are pure and effectless,
there is no notion of "short-circuiting".

### Equality (==)

This is not the same thing as `==` in exec-mode; see [more on `==`](./spec-equality.md).

### Arithmetic

Arithmetic works a little differently in order to operate with Verus's `int`
and `nat` types. See [more on arithmetic](./spec-arithmetic.md).

### References (&T)

Verus attempts to ignore `Box` and references as much as possible in spec mode.
However, you still needs to satisfy the Rust type-checker, so you may need to insert
references (`&`) or dereferences (`*`) to satisfy the checker. Verus will ignore these
operations however.

### Box<T>

Verus special-cases `Box` along with box operations like `Box::new(x)` or `*box`
so they may be used in spec mode. Like with references, these operations are ignored,
however they are often useful. For example, to create a recursive type you need to satisfy
Rust's sanity checks, which often involves using a `Box`.
