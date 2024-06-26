# Type sizes

Verus does not have direct access to the result of `core::mem::size_of<T>()` during verification. The size of most types is undefined by default (with the exception of `usize`/`isize`; see below). To use the size of `Sized` types in spec code, the `global size_of` directive may be used to set the size of the type and add a static assertion for the Rust compiler to check that the provided size matches the result of `core::mem::size_of<T>()`. Note that checking this assertion requires the `--compile` flag, as the assertion is checked by Rust, not Verus.

For example:

```rust
{{#include ../../../rust_verify/example/guide/sized.rs:sized_foo}}
```

The size of `Foo` is 16, rather than 12, because the C representation adds four bytes of padding to ensure that field `b` has the correct alignment.

The layout of a type, including its size and alignment, is dependent on its representation. The default `Rust` representation [does not guarantee that the same type always compiles to the same layout](https://doc.rust-lang.org/reference/type-layout.html#size-and-alignment). If it is important that a type's size remains the same across compilations, [other representations](https://doc.rust-lang.org/reference/type-layout.html#representations) (e.g., `repr(C)`) should be used.

The size of a type set with the `global size_of` directive can be accessed with `core::mem::size_of::<T>()` in both ghost and `exec` code. For example:

```rust
{{#include ../../../rust_verify/example/guide/sized.rs:sized_check}}
```

## Platform-dependent sizes

The width of `usize` and `isize` is platform-dependent. By default, Verus assumes that these types may be either 32 bits or 64 bits wide, but this can be configured with the directive:

```rust
global size_of usize == 8;
```

This would set the size of `usize` to 8 bytes and add a static assertion to check that it matches the target. 

