# Producing executable code from spec functions with the `exec_spec!` macro

When writing proofs in Verus, we occasionally need to
implement some simple function or data structure in both exec
and spec modes, and then establish their equivalence.
This process can be tedious for simple functions.

The `exec_spec!` macro simplifies this process: you only need
to write the desired functions/structs/enums in spec mode within
the supported fragment of `exec_spec!`, and then the macro can
automatically generate exec counterparts of these spec items,
as well as proofs of equivalence.

Here is an example:
```rust
{{#include ../../../../examples/guide/exec_spec.rs:example}}
```
In the example, we define a simple spec function `on_line` to check if
the given sequence of `Point`s have the same coordinates.

The `exec_spec!` macro call in this example takes all spec items in
its scope, and then derives executable counterparts along the lines of
the following definitions:
```
struct ExecPoint {
    x: i64,
    y: i64,
}

impl DeepView for ExecPoint {
    type V = Point;
    ...
}

fn exec_on_line(points: &[ExecPoint]) -> (res: bool)
    ensures res == on_line(points.deep_view())
{ ... }
```

After the macro invocation, we have the original spec items
as before (`Point` and `on_line`), but also new items `ExecPoint` and
`exec_on_line` with a suitable equivalence verified.
We can test the equivalence using the following sanity check:
```rust
{{#include ../../../../examples/guide/exec_spec.rs:check}}
```

Currently, `exec_spec!` supports these basic features:
  - Basic arithmetic operations
  - Logical operators (&&, ||, &&&, |||, not, ==>)
  - If, match and "matches"
  - Field expressions
  - Spec function calls and recursion
  - Bounded quantifiers of the form `forall |i| <lower> <= i < <upper> ==> <expr>` and `exists |i| <lower> <= i < <upper> && <expr>`
  - `Seq<T>` (compiled to `Vec<T>` or `&[T]` depending on the context), indexing, len, `seq!` literals
  - `SpecString` (an alias to `Seq<char>` to syntactically indicate that we want `String`/`&str`), indexing, len, string literals
  - `Option<T>`
  - User-defined structs and enums
  - Primitive integer/boolean types (`i<N>`, `isize`, `u<N>`, `usize`, `char`, etc.). Note that `int` and `nat` cannot be used in `exec_spec!`.
  - Equality between Seq, String, and arithmetic types

## Related

`exec_spec!` compiles spec items to exec items, which might not cover your use case.
For example, you may want to go from [exec to spec](exec_to_spec.html), 
or use the [`when_used_as_spec` attribute](reference-attributes.html).
