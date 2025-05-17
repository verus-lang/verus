## Struct

In Verus, just as in Rust, you can use `struct` to define a datatype that
collects a set of fields together:
```rust
{{#include ../../../../examples/guide/datatypes.rs:point}}
```

Spec and exec code can refer to `struct` fields:
```rust
{{#include ../../../../examples/guide/datatypes.rs:point-impl}}
```
