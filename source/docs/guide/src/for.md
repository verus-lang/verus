# For Loops 

The previous section introduced a `while` loop implementation of `triangle`:

```rust
{{#include ../../../../examples/guide/recursion.rs:loop}}
```

We can rewrite this as a `for` loop as follows:

```rust
{{#include ../../../../examples/guide/recursion.rs:for_loop}}
```

The only difference between this `for` loop and the `while` loop 
is that `idx` is automatically incremented by 1 at the end of the 
each iteration, and we no longer need the `idx <= n` invariant.

For more complex examples, Verus also provides ghost specifications
about the iterator used in `for` loops, as we discuss in the next section.
