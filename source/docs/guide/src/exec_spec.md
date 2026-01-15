# Producing executable code from spec functions with the `exec_spec!` macro

When writing proofs in Verus, we occasionally need to
implement some simple function or data structure in both exec
and spec modes, and then establish their equivalence.
This process can be tedious for simple functions.

The `exec_spec!` macro simplifies this process: you only need
to write the desired functions/structs/enums in spec mode within
the supported fragment of `exec_spec!`, and then the macro can
automatically generate exec counterparts of these spec items,
as well as proofs of equivalence. The `exec_spec_trusted!` macro 
does the same generation of exec code, but without proofs of equivalence
(all generated code is annotated with `#[verifier::external_body]`).

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
  - Bounded quantifiers. The quantifier expressions must match this form: `forall |x1: <type1>, x2: <type2>, ..., xN: <typeN>| <guard1> && <guard2> && ... && <guardN> ==> <body>` or `exists |x1: <type1>, x2: <type2>, ..., xN: <typeN>| <guard1> && <guard2> && ... && <guardN> && <body>`, where:
    - `<guardI>` is of the form: `<lowerI> <op> xI <op> <upperI>`, where:
        - `<op>` is either `<=` or `<`
        - `<lowerI>` and `<upperI>` can mention `xJ` for all `J < I`
    - `<typeI>` is a Rust primitive integer (`i<N>`, `isize`, `u<N>`, `usize`) or `char`
  - `Seq<T>` (compiled to `Vec<T>` or `&[T]` depending on the context), `seq!` literals, and `len`, indexing, `subrange`, `add`, `push`, `update`, `empty`, `new`, `to_multiset`, `drop_first`, `drop_last`, `take`, `skip`, `first`, `last`
  - `Multiset<T>` (compiled to `ExecMultiset<T>`, a type implemented in `vstd::contrib::exec_spec` whose internal representation is a `HashMap`), and `len`, `count`
  - `SpecString` (an alias to `Seq<char>` to syntactically indicate that we want `String`/`&str`), indexing, len, string literals
  - `Option<T>`
  - User-defined structs and enums
  - Primitive integer/boolean types (`i<N>`, `isize`, `u<N>`, `usize`, `char`, etc.). Note that `int` and `nat` cannot be used in `exec_spec!`.
  - Equality between Seq, String, and arithmetic types

## Related

`exec_spec!` compiles spec items to exec items, which might not cover your use case.
For example, you may want to go from [exec to spec](exec_to_spec.html), 
or use the [`when_used_as_spec` attribute](reference-attributes.html).
