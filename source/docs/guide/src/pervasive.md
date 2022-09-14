# Basic libraries

This chapter introduces some of Verus's built-in libraries for sequences, sets, maps, and vectors.
The libraries are currently located in a collection of modules
in the [pervasive](https://github.com/verus-lang/verus/tree/main/source/pervasive/) directory:
- [seq.rs](https://github.com/verus-lang/verus/tree/main/source/pervasive/seq.rs)
- [seq_lib.rs](https://github.com/verus-lang/verus/tree/main/source/pervasive/seq_lib.rs)
- [set.rs](https://github.com/verus-lang/verus/tree/main/source/pervasive/set.rs)
- [set_lib.rs](https://github.com/verus-lang/verus/tree/main/source/pervasive/set_lib.rs)
- [map.rs](https://github.com/verus-lang/verus/tree/main/source/pervasive/map.rs)
- [vec.rs](https://github.com/verus-lang/verus/tree/main/source/pervasive/vec.rs)

See also the [API documentation](https://verus-lang.github.io/verus/verusdoc/lib/pervasive/index.html).

UNDER CONSTRUCTION:
In the near future, we plan to move these libraries into their own pre-compiled crate.
At the moment, unfortunately, Verus doesn't support verified libraries from separate crates.
Therefore, to use the libraries, you have to make the libraries part of your own crate.
You can do this by placing `mod pervasive;` in the root of your crate,
as shown in
[this example code](https://github.com/verus-lang/verus/tree/main/source/rust_verify/example/guide/pervasive_example.rs):

```rust
{{#include ../../../rust_verify/example/guide/pervasive_example.rs}}
```

(If you're running the `rust_verify` executable directly,
you also have to pass the `--pervasive-path pervasive` command-line option to `rust_verify`.
If you're using the `rust-verify.sh` script,
the script will pass this argument for you.)

# Some syntactic sugar: spec_index and view

In ghost code, Verus supports two pieces of syntactic sugar that are used by the libraries:
- `[...]` is an abbreviation for `.spec_index(...)`.
  This is used, for example, to get an element from a sequence: `s[3]` means `s.spec_index(3)`.
- `@` is an abbreviation for `.view()`.
  This is commonly used to get a `spec` value
  that represents the abstract contents of a concrete `exec` object.
  For example, for an `exec` vector `v` of type `Vec<T>`, the value `v@` is a `spec` sequence
  of type `Seq<T>` containing the elements of `v`.
