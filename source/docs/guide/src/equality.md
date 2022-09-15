# Equality

Equality behaves differently in ghost code than in executable code.
In executable code, Rust defines `==` to mean a call to the `eq` function of the `PartialEq` trait:

```rust
{{#include ../../../rust_verify/example/guide/equality.rs:eq1}}
```

For built-in integer types like `u8`, the `x.eq(y)` function is defined as we'd expect,
returning `true` if `x` and `y` hold the same integers.
For user-defined types, though, `eq` could have other behaviors:
it might have side effects, behave nondeterministically,
or fail to fulfill its promise to implement an
equivalence relation,
even if the type implements the Rust [`Eq` trait](https://doc.rust-lang.org/std/cmp/trait.Eq.html):

```rust
{{#include ../../../rust_verify/example/guide/equality.rs:eq2}}
```

In ghost code, by contrast, equality is always an equivalence relation.
Verus defines `==` in ghost code to mean a call to the Verus `spec_eq` function
rather than the standard Rust `eq` function,
and `spec_eq` is required to be an equivalence relation (i.e. to be reflexive, symmetric, and transitive):

```rust
{{#include ../../../rust_verify/example/guide/equality.rs:eq3}}
```

Not all types implement `spec_eq`, though.
(Technically, only types implementing the Verus `Structural` trait implement `spec_eq`.)
Therefore, Verus supports another syntax for equality, written `===`,
that applies to all types:

```rust
{{#include ../../../rust_verify/example/guide/equality.rs:eq4}}
```

The `===` operator is always an equivalence relation.  It is defined to be true when:
- for two integers or booleans, the values are equal
- for two structs or enums, the types are the same and the fields are equal
- for two RefCells or Cells, the pointers to the interior data are equal (not the interior contents)

For types that implement `spec_eq`, the `===` operator is equivalent to `spec_eq`,
so that `==` and `===` can be used interchangeably in ghost code in this case.
