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

In ghost code, by contrast, the `==` operator is always an equivalence relation
(i.e. it is reflexive, symmetric, and transitive):

```rust
{{#include ../../../rust_verify/example/guide/equality.rs:eq3}}
```

Verus defines `==` in ghost code to be true when:
- for two integers or booleans, the values are equal
- for two structs or enums, the types are the same and the fields are equal
- for two `&` references, two Box values, two Rc values, or two Arc values, the pointed-to values are the same
- for two RefCell values or two Cell values, the pointers to the interior data are equal (not the interior contents)

In addition, collection dataypes such as `Seq<T>`, `Set<T>`, and `Map<Key, Value>`
have their own definitions of `==`,
where two sequences, two sets, or two maps are equal if their elements are equal.
As explained more in [specification libraries](spec_lib.md) and [extensional equality](extensional_equality.md),
these sometimes require the "extensional equality" operator `=~=` to help prove equality
between two sequences, two sets, or two maps.
