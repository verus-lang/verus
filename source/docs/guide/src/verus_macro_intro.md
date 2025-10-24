# The verus! macro

Recall the sample program from the [Getting Started](./getting_started.md) chapters:

```rust
{{#include ../../../../examples/guide/getting_started.rs}}
```

What is this exactly? Is it Verus? Is it Rust?

It's both! It's a Rust source file that uses the `verus!` macro to embed Verus.
Specifically, the `verus!` macro extends Rust's syntax with verification-related features
such as preconditions, postconditions, assertions, `forall`, `exists`, etc.,
which we will learn more about in this tutorial.


Verus uses a macro named `verus!` to extend Rust's syntax with verification-related features
such as preconditions, postconditions, assertions, `forall`, `exists`, etc.
Therefore, each file in a crate will typically take the following form:

```rust
use vstd::prelude::*;

verus! {
    // ...
}
```

The `vstd::prelude` exports the `verus!` macro along with some other Verus utilities.

The `verus!` macro, besides extending Rust's syntax, also 
_tells Verus to verify the functions contained within_.
By default, Verus verifies everything inside the `verus!` macro and ignores anything
defined outside the `verus!` macro. There are various attributes and directives to modify
this behavior (e.g., see [this chapter](./interacting-with-unverified-code.md)), but for
most of the tutorial, we will consider all code to be Verus code that must be in the
`verus!` macro.

**Note for the tutorial.**
In the remainder of this guide, we will omit these declarations from the examples to avoid clutter.
However, remember that any example code should be placed inside the `verus! { ... }` block,
and that the file should contain `use vstd::prelude::*;`.

**Alternate syntax.**
Verus also supports an alternate, [attribute-based syntax](exec_attr.md).
This syntax may be helpful when you want to minimize changes to an existing Rust project.
However, because the `verus!` syntax is cleaner and simpler, we'll stick to that in this
tutorial.
