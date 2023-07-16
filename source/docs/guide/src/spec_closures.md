# Spec Closures

Verus supports anonymous functions (known as "closures" in Rust) in ghost code.
For example, the following code from earlier in [this chapter](spec_lib.md)
uses an anonymous function `|i: int| 10 * i`,
to initialize a sequence with the values 0, 10, 20, 30, 40:

```rust
{{#include ../../../rust_verify/example/guide/lib_examples.rs:new0}}
```

The anonymous function `|i: int| 10 * i` has type `FnSpec(int) -> int`
and has mode `spec`.
Because it has mode `spec`,
the anonymous function is subject to the [same restrictions](modes.md) as named `spec` functions.
(For example, it can call other `spec` functions but not `proof` functions or `exec` functions.)

Note that in contrast to standard executable
[Rust closures](https://doc.rust-lang.org/book/ch13-01-closures.html),
where `Fn`, `FnOnce`, and `FnMut` are traits,
`FnSpec(int) -> int` is a type, not a trait.
Therefore, ghost code can return a spec closure directly,
using a return value of type `FnSpec(t1, ..., tn) -> tret`,
without having to use 
[(dyn or impl)](https://doc.rust-lang.org/book/ch19-05-advanced-functions-and-closures.html#returning-closures),
as with standard executable Rust closures.
