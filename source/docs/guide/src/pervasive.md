# Basic libraries

This chapter introduces some of Verus's built-in libraries for sequences, sets, maps, and vectors.
The libraries are currently located in a collection of modules
in the [vstd](https://github.com/verus-lang/verus/tree/main/source/vstd/) directory:
- [vstd::seq](https://github.com/verus-lang/verus/tree/main/source/vstd/seq.rs)
- [vstd::seq_lib](https://github.com/verus-lang/verus/tree/main/source/vstd/seq_lib.rs)
- [vstd::set](https://github.com/verus-lang/verus/tree/main/source/vstd/set.rs)
- [vstd::set_lib](https://github.com/verus-lang/verus/tree/main/source/vstd/set_lib.rs)
- [vstd::map](https://github.com/verus-lang/verus/tree/main/source/vstd/map.rs)
- [vstd::vec](https://github.com/verus-lang/verus/tree/main/source/vstd/vec.rs)

For more information,
see the [API documentation](https://verus-lang.github.io/verus/verusdoc/vstd/index.html).

As an example, the [following code](https://github.com/verus-lang/verus/tree/main/source/rust_verify/example/guide/vstd_example.rs)
uses the `vstd::seq` module:

```rust
{{#include ../../../rust_verify/example/guide/vstd_example.rs}}
```

For convenience, the `vstd::prelude` module includes `builtin_macros`, `builtin`,
as well as types from `seq`, `set`, `map`, `option`, `result`, and `string`:

```rust
use vstd::prelude::*;

verus! {

fn main() {
    proof {
        let s: Seq<int> = seq![0, 10, 20, 30, 40];
        assert(s.len() == 5);
        assert(s[2] == 20);
        assert(s[3] == 30);
    }
}

} // verus!
```

# Some syntactic sugar: spec_index and view

In ghost code, Verus supports two pieces of syntactic sugar that are used by the libraries:
- `[...]` is an abbreviation for `.spec_index(...)`.
  This is used, for example, to get an element from a sequence: `s[3]` means `s.spec_index(3)`.
- `@` is an abbreviation for `.view()`.
  This is commonly used to get a `spec` value
  that represents the abstract contents of a concrete `exec` object.
  For example, for an `exec` vector `v` of type `Vec<T>`, the value `v@` is a `spec` sequence
  of type `Seq<T>` containing the elements of `v`.
