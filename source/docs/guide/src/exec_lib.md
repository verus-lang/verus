# Executable libraries: Vec

The previous section discussed the mathematical collection types
`Seq`, `Set`, and `Map`.
This section will discuss `Vec`, an executable implementation of `Seq`. 
Verus supports some functionality of Rust's `std::vec::Vec` type. To use 
`Vec`, include `use std::vec::Vec;` in your code.

You can allocate `Vec` using `Vec::new` and then push elements into it:

```rust
{{#include ../../../rust_verify/example/guide/lib_examples.rs:test_vec1}}
```

The code above is able to make assertions directly about the `Vec` value `v`.
You could also write more compilicated specifications and proofs about `Vec` values.
In general, though, Verus encourages programmers to write `spec` functions
and `proof` functions about mathematical types like `Seq`, `Set`, and `Map` instead
of hard-wiring the specifications and proofs to particular concrete datatypes like `Vec`.
This allows `spec` functions and `proof` functions to focus on the essential ideas,
written in terms of mathematical types like `Seq`, `Set`, `Map`, `int`, and `nat`,
rather than having to fiddle around with finite-width integers like `usize`,
worry about arithmetic overflow, etc.

Of course, there needs to be a connection between the mathematical types
and the concrete types, and specifications in `exec` functions will commonly have to move
back and forth between mathematical abstractions and concrete reality.
To make this easier, Verus supports the syntactic sugar `@` for extracting
a mathematical `view` from a concrete type.
For example, `v@` returns a `Seq` of all the elements in the vector `v`:

```rust
{{#include ../../../rust_verify/example/guide/lib_examples.rs:test_vec2}}
```

Using the `Seq` view of the `Vec` allows us to use the various features of `Seq`,
such as concatenation and subsequences,
when writing specifications about the `Vec` contents.

Verus support for `std::vec::Vec` is currently being expanded. For up-to-date
documentation, visit [this link](https://verus-lang.github.io/verus/verusdoc/vstd/std_specs/vec/index.html).
Note that these functions provide specifications for `std::vec::Vec` functions. Thus,
for example, `ex_vec_insert` represents support for the `Vec` function `insert`. Code written 
in Verus should use `insert` rather than `ex_vec_insert`.

Documentation for `std::vec::Vec` functionality can be found [here](https://doc.rust-lang.org/std/vec/struct.Vec.html).
