# Alternatives to unsafe

Currently, Verus does not support most of Rust's "unsafe" primitives, like
`*mut` pointers or [`UnsafeCell`](https://doc.rust-lang.org/std/cell/struct.UnsafeCell.html).
However, we provide alternatives:

 * For unsafe heap pointers, use [`PPtr`](https://verus-lang.github.io/verus/verusdoc/vstd/ptr/struct.PPtr.html)
 * For unsafe interior mutability, use [`PCell`](https://verus-lang.github.io/verus/verusdoc/vstd/cell/struct.PCell.html)

See the documentation for more details. Also note that these types are under active development
as our understanding of their use-cases evolve.
In the future, we hope to move more towards
Rust's standard types, like `*mut` and `*const`.
