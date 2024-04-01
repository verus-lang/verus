# Equality via extensionality

In the [specification libraries](spec_lib.md) section,
we introduced the extensional equality operator `=~=`
to check equivalence for `Seq`, `Set`, and `Map`.

Suppose that a `struct` or `enum` datatype has a field containing `Seq`, `Set`, and `Map`,
and suppose that we'd like to prove that two values of the datatype are equal.
We could do this by using `=~=` on each field individually:

```rust
{{#include ../../../rust_verify/example/guide/ext_equal.rs:ext_eq_struct_fields}}
```

However, it's rather painful to use `=~=` on each field every time to check for equivalence.
To help with this, Verus supports the `#[verifier::ext_equal]` attribute
to mark datatypes that need extensionality on `Seq`, `Set`, `Map`, `Multiset`, `spec_fn`
fields or fields of other `#[verifier::ext_equal]` datatypes.  For example:

```rust
{{#include ../../../rust_verify/example/guide/ext_equal.rs:ext_eq_struct}}
```

(Note: adding `#[verifier::ext_equal]` does not change the meaning of `==`;
it just makes it more convenient to use `=~=` to prove `==` on datatypes.)

Collection datatypes like sequences and sets can contain other collection datatypes as elements
(for example, a sequence of sequences, or set of sequences).
The `=~=` operator only applies extensionality to the top-level collection,
not to the nested elements of the collection.
To also apply extensionality to the elements,
Verus provides a "deep" extensional equality operator `=~~=`
that handles arbitrary nesting of collections, `spec_fn`, and datatypes.
For example:

```rust
{{#include ../../../rust_verify/example/guide/ext_equal.rs:ext_eq_nested}}
```

The same applies to `spec_fn`, as in:

```rust
{{#include ../../../rust_verify/example/guide/ext_equal.rs:ext_eq_fnspec}}
```
