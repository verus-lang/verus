# Integers: nonlinear arithmetic and bit vectors

Nonlinear arithmetic and bit-vector reasoning are disabled by default in Verus. Instead, Verus offers dedicated mechanisms for reasoning about these topics. These mechanisms can generally be invoked by adding `by` clause in `assert` or `fn` signature. To be specific, `by(nonlinear_arith)` enables nonlinear arithmetic reasoning, and `by(bit_vector)` enables bit-vector reasoning. Furthermore, Verus provides support for an optional backed solver called Singular, to help prove nonlinear arithmetic facts.



# Non Linear Arithmetic in Verus

## 1. Proving with Z3 
Note that default Verus runs with nonlinear arithmetic support disabled(i.e., `smt.arith.nl=false`). Therefore, Verus might fail to prove an easy fact about non-linear arithmetics without using one of the strategies described below. You can turn on Z3's non-linear arithmetic support using `by(nonlinear_arith)`.
### `assert(...) by(nonlinear_arith)`
This assertion generates a separate SMT query with `smt.arith.nl=true`. The `requires` inside the `by(nonlinear_arith)` assertion is assumed inside its proof block, whereas these are transformed into assertions in the main query. In the main query, the predicate inside the assertion is assumed. The separated non-linear query does not recognize surrounding facts other than variables' type invariants. Users should provide required contexts using `requires` in `assert(...) by(nonlinear_arith)`. 
For example:
```rust
{{#include ../../../rust_verify/example/guide/nonlinear_bitvec.rs:bound_checking}}
```

### `proof fn ... by(nonlinear_arith)`
You can also use `by(nonlinear_arith)` in a proof function's signature. By including `by(nonlinear_arith)`, the query for this function runs with nonlinear arithmetic reasoning enabled.


## 2. Proving with Singular (optional)
***WARNING: This feature is currently under maintenance; this feature might be broken.***

Even if you use `by(nonlinear_arith)`, it is easy to get a timeout or unknown for non-linear arithmetics since it is not easy for SMT solvers to deal with non-linear arithmetics. Therefore, Verus further supports utilizing a separate solver called Singular. 

### `#[verifier(integer_ring)]`
When a proof function is annotated with `verifier(integer_ring`), instead of Z3, Singular uses the Groebner basis for the ideal membership problem. First, it registers all polynomials from requires clauses as a basis. These basis forms an ideal, and the Groebner basis is computed from it. If the ensures polynomial is reduced to 0, it returns Valid; otherwise, it returns invalid.

Using this functionality helps users to prove facts with `mod` much easier. For example, the below example is instantly proved, while it is not easy to prove in Z3.

(TODO: add example)

### Installing Singular
To use Singular's standard library(which includes Groebner basis), you need more than just Singular executable binary. Using the system's package manager is preferred, but you can find other options as well. 

- Mac: `brew install Singular` and add `VERUS_SINGULAR_PATH` when running Verus. (e.g. `VERUS_SINGULAR_PATH=/usr/local/bin/Singular`). For more options, see OS X installation [guide](https://www.singular.uni-kl.de/index.php/singular-download/install-os-x.html)  

  
- Linux: `apt-get update`, `apt-get install singular`, and add `VERUS_SINGULAR_PATH` when running Verus. (e.g. `VERUS_SINGULAR_PATH=/usr/bin/Singular`). For more options, see Linux installation [guide](https://www.singular.uni-kl.de/index.php/singular-download/install-linuxunix.html)

- Windows: [guide](https://www.singular.uni-kl.de/index.php/singular-download/install-windows.html)

### Compiling with Feature 'Singular'
This `integer_ring` functionality is conditionally compiled when `singular` feature is set. To use this, add flag `--features singular` when `vargo build`.

### Details/Limitations
- This can be used only with **int** parameters.
- With current encoding, proving inequalities are not supported.   
- Function calls are interpreted into uninterpreted functions. Users can to feed the function's behavior in `requires`. Instead, users can consider using macros.
- `/` Division is not supported.

#### Workarounds for limitations
- Since it is only with `int`, users need to check bounds when they want to prove properties about bounded integers. One example of this is at `source/rust_verify/examples/integer_ring/integer_ring_bound_check.rs`.
- Proving inequalities and division is not supported. However, users might be able to use Singular by adding additional variables. One example of this is at `source/rust_verify/examples/integer_ring/integer_ring.rs, line 115: multiple_offsed_mod_gt_0_int`.
   

### Examining the encoding
Singular queries will be logged in a separate file with `.singular` suffix. Users can directly run this file with Singular. For example, `Singular .verus-log/root.singular --q`. The output `0` is expected when the query is verified.

---
# Proving Properties About Bit Manipulation

Verus offers two dedicated mechanisms for reasoning about bit manipulation
(e.g., to prove that `xor(w, w) == 0`).  Small, one-off proofs can be done
via `assert(...) by(bit_vector)`. Larger proofs, or proofs that will be needed in more than one place, can be done by writing a lemma and adding the annotation 
`by(bit_vector)`.  
Both mechanisms export facts expressed over integers (e.g., in terms of `u32`), but internally, they translate the proof obligations into assertions about bit vectors and use a dedicated solver to discharge those assertions.

### `assert(...) by(bit_vector)`
It can be used when a short and context-free bit-related fact is needed. 
Here are two example use cases:
```rust
{{#include ../../../rust_verify/example/guide/nonlinear_bitvec.rs:bitvector_easy}}
```

Currently, assertions expressed via `assert(...) by(bit_vector)` do not include any ambient facts from the surrounding context (e.g., from `requires` clauses or previous variable definitions).  For example, the following example will fail.

```rust
{{#include ../../../rust_verify/example/guide/nonlinear_bitvec.rs:bitvector_fail}}
```

To make ambient facts available, use `requires` clause to "import" these facts into the bit-vector assertion.  For example, the following example will now succeed.
```rust
{{#include ../../../rust_verify/example/guide/nonlinear_bitvec.rs:bitvector_success}}
```


### `proof fn ... by(bit_vector)`
This mechanism should be used when proving more complex facts about bit manipulation or when a proof will be used more than once. To use this mechanism, the developer should write a function in `proof` mode.
The function **should not** have a body. Context can be provided via a `requires` clause. 
For example:     
```rust
{{#include ../../../rust_verify/example/guide/nonlinear_bitvec.rs:de_morgan}}
```

For more examples, please refer to the bit-manipulation examples at the bottom.

## Limitations

### Supported Expressions 

The bit-reasoning mechanism supports only a subset of the full set of expressions Verus offers.
Currently, it supports:
- Unsigned Integer types (as well as the `as` keyword between unsigned integers)
- Built-in operators
- `let` binding
- Quantifiers
- `if-then-else` 

Note that function calls are not supported. As a workaround, you may consider using a macro instead of a function. Currently, the bit-reasoning mechanism does not support signed integers.


### Bitwise Operators As Uninterpreted Functions
Outside of `by(bit_vector)`, bitwise operators are translated into uninterpreted functions in Z3, meaning Z3 knows nothing about them when used in other other contexts. 
As a consequence, basic properties such as commutativity and associativity of bitwise-AND will not be applied automatically. To make use of these properties, please refer to [this file](https://github.com/verus-lang/verus/blob/main/source/rust_verify/example/bitvector_basic.rs), which contains basic properties for bitwise operators.

### add/sub/mul
Inside bit-vector assertion, please use `add` `sub` `mul` for fixed-bit operators instead of `+` `-` `*`, as normal operators widen the result to a mathematical integer. You could find these functions at `builtin::add(left, right)`, `builtin::sub(left, right)`, and `builtin::mul(left, right)`

### Bit-manipulation examples using `get_bit!` and `set_bit!` macro
You could use two macros, `get_bit!` and `set_bit!`, to access and modify a single bit of an integer variable. Please refer [garbage collecting example](https://github.com/verus-lang/verus/blob/main/source/rust_verify/example/bitvector_garbage_collection.rs) and [bitvector equivalence example](https://github.com/verus-lang/verus/blob/main/source/rust_verify/example/bitvector_equivalence.rs).
