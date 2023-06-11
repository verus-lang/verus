# Integers: Nonlinear Arithmetic and Bit Manipulation

Some properties about integers are very difficult (or expensive) to reason about fully automatically.
As described below, to tackle these properties, Verus offers several dedicated proof strategies.

# Nonlinear Arithmetic in Verus

Nonlinear arithmetic involves equations that multiply, divide, or take the remainder of integer variables 
(e.g., `x * (y * z) == (x * y) * z`).  As discussed earlier in this guide, determining the truth of such formulas
is undecideable in general, meaning that general-purpose SMT solvers like Z3 can only make a best-effort attempt
to solve them.  These attempts rely on heuristics that can be unpredictable.  Hence, by default, Verus 
disables Z3's nonlinear arithmetic heuristics.  When you need to prove such properties, Verus offers the two dedicated
proof strategies described below.  The first can reliably prove a limited subset of nonlinear properties.  For properties
outside that subset, Verus offers a way to invoke Z3's nonlinear heuristics in a way that will hopefully provide
better reliability.

## 1. Proving Ring-based Properties with Singular (optional)
***WARNING: This feature is currently under maintenance; this feature might be broken.***

While general nonlinear formulas cannot be solved consistently, certain
sub-classes of nonlinear formulas can be.  For example, nonlinear formulas that
consist of a series of congruence relations (i.e., equalities modulo some
divisor `n`).  As a simple example, we might like to show that `a % n == b % n
==> (a * c) % n == (b * c) % n`.

Verus offers a deterministic proof strategy to discharge such obligations.
As shown below, to use this strategy, you must state the desired property
as a proof function annotated with `#[verifier(integer_ring)]`.

(TODO: add example based on the equations above)

Verus will then discharge the proof obligation using a dedicated algebra solver
called [Singular](https://www.singular.uni-kl.de/).  As hinted at by the
annotation, this proof technique is only complete (i.e., guaranteed to succeed)
for properties that are true for all
[rings](https://en.wikipedia.org/wiki/Ring_(mathematics)).   Formulas that rely
specifically on properties of the integers may not be solved successfully.

Using this proof technique requires a bit of additional configuration of your Verus installation.

### Setup

1. Install Singular
    - To use Singular's standard library, you need more than just the Singular executable binary. 
      Hence, when possible, we strongly recommend using your system's package manager.  Here are 
      some suggested steps for different platforms.
        - Mac: `brew install Singular` and set the `VERUS_SINGULAR_PATH` environment variable when running Verus. (e.g. `VERUS_SINGULAR_PATH=/usr/local/bin/Singular`). For more options, see Singular's [OS X installation guide](https://www.singular.uni-kl.de/index.php/singular-download/install-os-x.html). 

        - Debian-based Linux: `apt-get install singular` and set the `VERUS_SINGULAR_PATH` environment variable when running Verus. (e.g. `VERUS_SINGULAR_PATH=/usr/bin/Singular`). For more options, see Singular's [Linux installation guide](https://www.singular.uni-kl.de/index.php/singular-download/install-linuxunix.html).

        - Windows: See Singular's [Windows installation guide](https://www.singular.uni-kl.de/index.php/singular-download/install-windows.html).

2. Compiling Verus with Singular Support
    - The `integer_ring` functionality is conditionally compiled when the `singular` feature is set.
      To add this feature, add the `--features singular` flag when you invoke `vargo build` to compile Verus.

### Details/Limitations
- This can be used only with **int** parameters.
- Formulas that involve inequalities are not supported.   
- Function calls in the formulas are treated as uninterpreted functions.  If a function definition is important for the proof, you should unfold the definition of the function in the proof function's `requires` clause.
- Division is not yet supported.

#### Workarounds for limitations
(TODO: Please add inline source code examples)

- Since these proofs only support `int`, you need to include explicit bounds when you want to prove properties about bounded integers. One example of this is at `source/rust_verify/examples/integer_ring/integer_ring_bound_check.rs`.
- To work around the lack of support for inequalities and division, you can sometimes add additional variables to the formulas. One example of this is at `source/rust_verify/examples/integer_ring/integer_ring.rs, line 115: multiple_offsed_mod_gt_0_int`.
   

### Examining the encoding
Singular queries will be logged to the directory specified with `--log-dir` (which defaults to `.verus-log`) in a separate file with a `.singular` suffix. You can directly run Singular on this file. For example, `Singular .verus-log/root.singular --q`. 
The output is `0` when Singular successsfully verifies the query.


## 2. Proving General Properties with Z3 
To prove a nonlinear formula that cannot be solved using Singular,
you can selectively turn on Z3's nonlinear reasoning heuristics.
As described below, you can do this either inline in the midst of a larger
function, or in a dedicated proof function.

### Inline Proofs with `assert(...) by(nonlinear_arith)`
To prove a nonlinear property in the midst of a larger function,
you can write `assert(...) by(nonlinear_arith)`.  This creates
a separate Z3 query just to prove the asserted property,
and for this query, Z3 runs with its nonlinear heuristics enabled.
The query does not include ambient facts (e.g., knowledge that stems
from the surrounding function's `requires` clause
or from preceding variable assignments) other than each variable's type invariants
(e.g., the fact that a `nat` is non-negative).  To include additional
context in the query, you can specify it in a `requires` clause for the `assert`,
as shown below.
```rust
{{#include ../../../rust_verify/example/guide/nonlinear_bitvec.rs:bound_checking}}
```

### Modular Proofs with `proof fn ... by(nonlinear_arith)`
You can also use `by(nonlinear_arith)` in a proof function's signature. By including `by(nonlinear_arith)`, the query for this function runs with nonlinear arithmetic reasoning enabled.


---
# Proving Properties About Bit Manipulation

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

For more examples, please refer to the bit-manipulation examples at the bottom.

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
