# Type layout

Verus does not have direct access information about [type layout](https://doc.rust-lang.org/reference/type-layout.html) during verification. The layout of most types is undefined by default (with the exception of `usize`/`isize`; see below). The `global size_of` and `global layout` directives may be used to set the size and/or alignment of a type and add static assertions to check that the provided layout matches the layout used by the Rust compiler. Note that checking these assertions requires the `--compile` Verus flag as these assertions are checked by the Rust compiler.

For example:

```rust
{{#include ../../../rust_verify/example/guide/sized.rs:sized_foo}}
```

The size of `Foo` is 16, rather than 12, because the C representation adds four bytes of padding to ensure that field `b` has the correct alignment.

To set both the size and alignment of `Foo`, use the following directive:
```rust
{{#include ../../../rust_verify/example/guide/sized.rs:layout_foo}}
```

The layout of a type is dependent on its representation. The default `Rust` representation [does not guarantee that the same type always compiles to the same layout](https://doc.rust-lang.org/reference/type-layout.html#size-and-alignment). If it is important that a type's size remains the same across compilations, [other representations](https://doc.rust-lang.org/reference/type-layout.html#representations) (e.g., `repr(C)`) should be used.

Once set using these directives, the size and/or alignment of a type can be accessed with `core::mem::size_of::<T>()`/`core::mem::align_of::<T>()` in both ghost and `exec` code. For example:

```rust
{{#include ../../../rust_verify/example/guide/sized.rs:sized_check}}
```

## Platform-dependent sizes

The width of `usize` and `isize` is platform-dependent. By default, Verus assumes that these types may be either 32 bits or 64 bits wide, but this can be configured with the directive:

```rust
global size_of usize == 8;
```

This would set the size of `usize` to 8 bytes and add a static assertion to check that it matches the target. 

