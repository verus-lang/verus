# Extensional Equality

In [specification libraries](spec_lib.md), we introduced the extensional equality operator `=~=` to check equivalence for `Seq`, `Set`, and `Map`.

For a datatype containing these collections, it would be rather painful to use `=~=` on each field every time to check for equivalence. 
To help with this, we introduce the `#[verifier::ext_equal]` attribute to mark datatypes if they need extensionality on `Seq`, `Set`, `Map`, `Multiset`, `FnSpec` 
fields or fields of other `#[verifier::ext_equal]` datatypes. This does not change the meaning of `==`. See:

```rust
{{#include ../../../rust_verify/example/guide/ext_equal.rs:ext_eq_struct}}
```

Since collection datatypes are parameterized, they can contain other collection datatype as a result. 
To check extensional equality on nested collections, it is not enough to just use `=~=`, but need a "deep" extensional equality operator `=~~=`. 
Don't worry, the number of `~` does not grow infinitely, `=~~=` handles arbitrary nesting of collections, `FnSpec`, and datatypes. See:

```rust
{{#include ../../../rust_verify/example/guide/ext_equal.rs:ext_eq_nested}}
```
