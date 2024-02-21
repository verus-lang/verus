# Bit vectors and bitwise operations

Verus offers two dedicated mechanisms for reasoning about bit manipulation
(e.g., to prove that `xor(w, w) == 0`).  Small, one-off proofs can be done
via `assert(...) by(bit_vector)`. Larger proofs, or proofs that will be needed in more than one place, can be done by writing a proof function and adding the annotation 
`by(bit_vector)`.  
Both mechanisms export facts expressed over integers (e.g., in terms of `u32`), but internally, they translate the proof obligations into assertions about bit vectors and use a dedicated solver to discharge those assertions.

### `assert(...) by(bit_vector)`
This style can be used to prove a short and context-free bit-manipulation property.
Here are two example use cases:
```rust
{{#include ../../../rust_verify/example/guide/nonlinear_bitvec.rs:bitvector_easy}}
```

Currently, assertions expressed via `assert(...) by(bit_vector)` do not include any ambient facts from the surrounding context (e.g., from the surrounding function's `requires` clause or from previous variable assignments).  For example, the following example will fail.

```rust
{{#include ../../../rust_verify/example/guide/nonlinear_bitvec.rs:bitvector_fail}}
```

To make ambient facts available, add a `requires` clause to "import" these facts into the bit-vector assertion.  For example, the following example will now succeed.
```rust
{{#include ../../../rust_verify/example/guide/nonlinear_bitvec.rs:bitvector_success}}
```


### `proof fn ... by(bit_vector)`
This mechanism should be used when proving more complex facts about bit manipulation or when a proof will be used more than once. To use this mechanism, you should write a function in `proof` mode.
The function **should not** have a body. Context can be provided via a `requires` clause. 
For example:     
```rust
{{#include ../../../rust_verify/example/guide/nonlinear_bitvec.rs:de_morgan}}
```

## Limitations

### Supported Expressions 

The bit-manipulation reasoning mechanism supports only a subset of the full set of expressions Verus offers.
Currently, it supports:
- Unsigned integer types (as well as the `as` keyword between unsigned integers)
- Built-in operators
- `let` binding
- Quantifiers
- `if-then-else` 

Note that function calls are not supported. As a workaround, you may consider using a macro instead of a function. 


### Bitwise Operators As Uninterpreted Functions
Outside of `by(bit_vector)`, bitwise operators are translated into uninterpreted functions in Z3, meaning Z3 knows nothing about them when used in other contexts. 
As a consequence, basic properties such as the commutativity and associativity of bitwise-AND will not be applied automatically. To make use of these properties, please refer to [this example file](https://github.com/verus-lang/verus/blob/main/source/rust_verify/example/bitvector_basic.rs), which contains basic properties for bitwise operators.

### Naming Arithmetic Operators: `add/sub/mul`
Inside a bit-vector assertion, please use `add`, `sub`, and `mul` for fixed-width operators instead of `+` `-` `*`, as the latter operators widen the result to a mathematical integer. 

### Bit-Manipulation Examples Using the `get_bit!` and `set_bit!` Macros
You can use two macros, `get_bit!` and `set_bit!`, to access and modify a single bit of an integer variable. Please refer our [garbage collection example](https://github.com/verus-lang/verus/blob/main/source/rust_verify/example/bitvector_garbage_collection.rs) and our [bitvector equivalence example](https://github.com/verus-lang/verus/blob/main/source/rust_verify/example/bitvector_equivalence.rs).
