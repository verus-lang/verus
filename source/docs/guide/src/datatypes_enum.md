## Enum

In Verus, just as in Rust, you can use `enum` to define a datatype that is any one of the
defined variants:
```rust
{{#include ../../../rust_verify/example/guide/datatypes.rs:beverage}}
```

An `enum` is often used just for its tags, without member fields:
```rust
{{#include ../../../rust_verify/example/guide/datatypes.rs:syrup}}
```

## Identifying a variant with the `is` operator

In spec contexts, the `is` operator lets you query which variant of an
enum a variable contains. 
```rust
{{#include ../../../rust_verify/example/guide/datatypes.rs:make_float}}
```

## Accessing fields with the arrow operator

If all the fields have distinct names, as in the `Beverage` example,
you can refer to fields with the arrow `->` operator:
```rust
{{#include ../../../rust_verify/example/guide/datatypes.rs:count_creamers}}
```

If an `enum` field reuses a name, you can qualify the field access:
```rust
{{#include ../../../rust_verify/example/guide/datatypes.rs:life}}
```

`match` works as in Rust.
```rust
{{#include ../../../rust_verify/example/guide/datatypes.rs:shape}}
```

For variants like `Shape` declared with round parentheses `()`,
you can use Verus' `->' tuple-like syntax to access a single field
without a match destruction:
```rust
{{#include ../../../rust_verify/example/guide/datatypes.rs:rect_height}}
```

## matches with &&, ==>, and &&&

`match` is natural for examining every variant of an `enum`.
If you'd like to bind the fields while only considering one or two of the
variants, you can use Verus' `matches` syntax:
```rust
{{#include ../../../rust_verify/example/guide/datatypes.rs:cuddly}}
```

Because the `matches` syntax binds names in patterns, it has no trouble
with field names reused across variants, so it may be preferable
to the (qualified) arrow syntax.

Notice that `l matches Mammal{legs} && legs == 4` is a boolean expression,
with the special property that `legs` is bound in the remainder of the
expression after `&&`. That helpful binding also works with `==>`
and `&&&`:
```rust
{{#include ../../../rust_verify/example/guide/datatypes.rs:kangaroo}}
```
