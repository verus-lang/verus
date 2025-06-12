# Strings

Verus supports reasoning about Rust `String` and `&str`:

```rust
{{#include ../../../../examples/guide/strings.rs:initial}}
```

By default a string literal is treated as opaque,

```rust
fn opaque_by_default() {
    let x = "hello world";
    assert(x@.len() == 11); // FAILS
}
```

this code results in a failed assertion:

```
error: assertion failed
  --> ../examples/guide/strings.rs:21:12
   |
21 |     assert(x@.len() == 11); // FAILS
   |            ^^^^^^^^^^^^^^ assertion failed
```

which can be fixed by using `reveal_strlit` (like in the
example at the top).

However, comparing for equality does not require revealing
literals:

```rust
{{#include ../../../../examples/guide/strings.rs:literal_eq}}
```

A string literal is a `&str` and its view is a `Seq<char>`,

```rust
{{#include ../../../../examples/guide/strings.rs:literal_view}}
```

whose value is unkown until the literal is revealed.

One can of course specify information about the view in, e.g., a function precondition (or some other predicate);

```rust
fn subrange<'a>(s: &str)
    requires
        s@ =~= "Hello"@,
{
    assert(s@.subrange(0, 1) == "H"@);
}
```

however, we need to reveal both literals to obtain information about their views in this case:

```rust
{{#include ../../../../examples/guide/strings.rs:pre_substring}}
```

Operating on strings currently requires the operations defined in `vstd::strings` [documented here](https://verus-lang.github.io/verus/verusdoc/vstd/string/index.html).

An important predicate for `&str` and `String` is `is_ascii`,
which enables efficient slicing, for example:


```rust
{{#include ../../../../examples/guide/strings.rs:substring_ascii}}

```