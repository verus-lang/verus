# Equality via extensionality

The [specification libraries](spec_lib.md) section
introduced the extensional equality operator `=~=`
to check equivalence for collection types like `Seq`, `Set`, and `Map`.
Extensional equality proves that two collections are equal by proving that
the collections contain equal elements.
This can be used, for example, to prove that the sequences `s1`, `s2`, and `s3`
are equal because they have the same elements (0, 10, 20, 30, 40),
even though this sequences were constructed in different ways:

```rust
{{#include ../../../../examples/guide/lib_examples.rs:test_eq2}}
```

Assertions like `assert(s1 =~= s2)` are common for proving equality via extensionality.
Note that by default, Verus promotes `==` to `=~=` inside `assert`, `ensures`, and `invariant`,
so that, for example, `assert(s1 == s2)` actually means `assert(s1 =~= s2)`.
This is convenient in many cases where extensional equality is merely a minor step in a larger proof,
and you don't want to clutter the proof with low-level details about equality.
For proofs where extensional equality is the key step,
you may want to explicitly write `assert(s1 =~= s2)` for documentation's sake.

(If you don't want Verus to auto-promote `==` to `=~=`,
perhaps because you want to see exactly where extensional equality is really needed,
the `#[verifier::auto_ext_equal(...)]` and `#![verifier::auto_ext_equal(...)]`
attributes can override Verus's default behavior.
See [ext_equal.rs](https://github.com/verus-lang/verus/blob/main/source/rust_verify_test/tests/ext_equal.rs)
for examples.)

## Extensional equality for structs and enums

Suppose that a `struct` or `enum` datatype has a field containing `Seq`, `Set`, and `Map`,
and suppose that we'd like to prove that two values of the datatype are equal.
We could do this by using `=~=` on each field individually:

```rust
{{#include ../../../../examples/guide/ext_equal.rs:ext_eq_struct_fields}}
```

However, it's rather painful to use `=~=` on each field every time to check for equivalence.
To help with this, Verus supports the `#[verifier::ext_equal]` attribute
to mark datatypes that need extensionality on `Seq`, `Set`, `Map`, `Multiset`, `spec_fn`
fields or fields of other `#[verifier::ext_equal]` datatypes.  For example:

```rust
{{#include ../../../../examples/guide/ext_equal.rs:ext_eq_struct}}
```

(Note: adding `#[verifier::ext_equal]` does not change the meaning of `==`;
it just makes it more convenient to use `=~=` to prove `==` on datatypes.)

## Deep extensional equality

Collection datatypes like sequences and sets can contain other collection datatypes as elements
(for example, a sequence of sequences, or set of sequences).
The `=~=` operator only applies extensionality to the top-level collection,
not to the nested elements of the collection.
To also apply extensionality to the elements,
Verus provides a "deep" extensional equality operator `=~~=`
that handles arbitrary nesting of collections, `spec_fn`, and datatypes.
For example:

```rust
{{#include ../../../../examples/guide/ext_equal.rs:ext_eq_nested}}
```

The same applies to `spec_fn`, as in:

```rust
{{#include ../../../../examples/guide/ext_equal.rs:ext_eq_fnspec}}
```
