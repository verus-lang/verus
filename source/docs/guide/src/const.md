# const declarations

`const` declarations can either be marked `spec` or left without a mode:

```rust
{{#include ../../../rust_verify/example/guide/modes.rs:const1}}
```

A `spec const` is like `spec` function with no arguments.
It is always ghost and cannot be used as an `exec` value.

By contrast, a `const` without a mode is dual-use:
it is usable as both an `exec` value and a `spec` value.
Therefore, the `const` definition is restricted to obey the rules
for both `exec` code and `spec` code.
For example, as with `exec` code, its type must be compilable (e.g. `u8`, not `int`),
and, as with `spec` code, it cannot call any `exec` or `proof` functions.
