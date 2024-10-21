# Bit vectors and bitwise operations

In its default prover mode, Verus treats bitwise operations like `&`, `|`, `^`, `<<` and `>>` as uninterpreted functions.
Even basic facts like `x & y == y & x` are not exported by Verus's default solver mode.

To handle these situations, Verus provides the specialized solver mode `bit_vector`.
This solver is great for properties about bitwise operators, and it can also handle
some bounded integer arithmetic, though for this, its efficacy varies.

## Invoking the `bit_vector` prover mode.

The `bit_vector` prover mode can be invoked 
[similarly to `nonlinear_arith`](./nonlinear.md#1-invoking-a-specialized-solver-nonlinear_arith),
with `by(bit_vector)` either on an `assert` or a `proof fn`.

For example, we can shorts and context-free bit-manipulation properties:
```rust
{{#include ../../../rust_verify/example/guide/nonlinear_bitvec.rs:bitvector_easy}}
```

Again, as with `nonlinear_arith`, assertions that use `by(bit_vector)`
do not include any ambient facts from the surrounding context (e.g., from the surrounding function's `requires` clause or from previous variable assignments).

Currently, assertions expressed via `assert(...) by(bit_vector)` do not include any ambient facts from the surrounding context (e.g., from the surrounding function's `requires` clause or from previous variable assignments).  For example, the following example will fail:

```rust
{{#include ../../../rust_verify/example/guide/nonlinear_bitvec.rs:bitvector_fail}}
```

But context can be imported explicitly with a `requires` clause:

```rust
{{#include ../../../rust_verify/example/guide/nonlinear_bitvec.rs:bitvector_success}}
```

And `by(bit_vector)` is also supported on proof functions:

```rust
{{#include ../../../rust_verify/example/guide/nonlinear_bitvec.rs:de_morgan}}
```

Again, this will use the `bit_vector` solver to prove the lemma, but all calls to the lemma
will use the normal solver to prove the precondition.

## How the `bit_vector` solver works and what it's good at

The bitvector solver uses a different SMT encoding, though one where all arithmetic operations
have the same semantic meaning.
Specifically, it encodes all integers into the [Z3 `bv` type](https://microsoft.github.io/z3guide/docs/theories/Bitvectors/) and encodes arithmetic via the built-in bit-vector operations.
Internally, the SMT solver uses a technique called "bit blasting".

In order to implement this encoding, Verus needs to choose an appropriate bit width to represent
any given integer. For symbolic, fixed-width integer values (e.g., `u64`) it can just choose
the appropriate bitwidth (e.g., 64 bits). For the results of arithmetic operations,
Verus chooses an appropriate bitwidth automatically.
However, for this reason, the bitvector solver cannot reason over _symbolic_ integer values.

The bitvector solver is ideal for proofs about bitwise operations
([`&`, `|`, `^`, `<<` and `>>`](./spec-bit-ops.md)).
However, it is also decent at arithmetic (`+`, `-`, `*`, `/`, `%`) over bounded integers.

## Examples and tips

### Functions vs macros

The bit-vector solver doesn't allow arbitrary functions. However, you can use _macros_.
This is useful when certain operations need a common shorthand, like
"get the <i>i<sup>th</sup></i> bit of an integer".

```
macro_rules! get_bit_macro {
    ($a:expr, $b:expr) => {{
        (0x1u32 & ($a >> $b)) == 1
    }};
}

macro_rules! get_bit {
    ($($a:tt)*) => {
        verus_proof_macro_exprs!(get_bit_macro!($($a)*))
    }
}
```

### Overflow checking

Though the `bit_vector` solver does not handle symbolic `int` values, it _does_ support many
arithmetic operations that return `int` values.
This makes it possible to write conditions about overflow:

```rust
proof fn test_overflow_check(a: u8, b: u8) {
    // `a` and `b` are both `u8` integers, but we can test if their addition
    // overflows a `u8` by simply writing `a + b < 256`.
    assert((a & b) == 0 ==> (a | b) == (a + b) && (a + b) < 256) by(bit_vector);
}
```

### Integer wrapping and truncation

The `bit_vector` solver is one of the easiest ways to reason about truncation, which can be naturally expressed through bit operations.

```rust
proof fn test_truncation(a: u64) {
    assert(a as u32 == a & 0xffff_ffff) by(bit_vector);

    // You can write an identity with modulus as well:
    assert(a as u32 == a % 0x1_0000_0000) by(bit_vector);
}
```

You may also find it convenient to use `add`, `sub`, and `mul`, which (unlike `+`, `-`, and `*`) automatically truncate.

```rust
proof fn test_truncating_add(a: u64, b: u64) {
    assert(add(a, b) == (a + b) as u64) by(bit_vector);
}
```

### Working with `usize` and `isize`

If you use variables of type `usize` or `isize`, the bitvector solver (by default) assumes they
might be either 32-bit or 64-bit, which affects the encoding.
In that case, the solver will generate 2 different queries and verifies both.

However, the solver can also be [configured to assume a particular platform size](./reference-global.md#with-usize-and-isize).

### Bit-width dependence and independence

For many operations, their results are independent of the input bit-widths.
This is true of `&`, `|`, `^`, and `>>`.
In fact, we don't even need the bit-vector to prove this; the normal solver mode is "aware"
of this fact as well.

```rust
proof fn test_xor_u32_vs_u64(x: u32, y: u32) {
    assert((x as u64) ^ (y as u64) == (x ^ y) as u64) by(bit_vector);

    // XOR operation is independent of bitwidth so we don't even
    // need the `bit_vector` solver to do this:
    assert((x as u64) ^ (y as u64) == (x ^ y) as u64);
}
```

However, this is _not_ true of left shift, `<<`.
With left shift, you always need to be careful of the bitwidth of the left operand.

```rust
proof fn test_left_shift_u32_vs_u64(y: u32) {
    assert(1u32 << y == 1u64 << y); // FAILS (in either mode) because it's not true
}
```

### More examples

Some larger examples to browse:

 * [garbage collection example](https://github.com/verus-lang/verus/blob/main/source/rust_verify/example/bitvector_garbage_collection.rs)
 * [bitvector equivalence example](https://github.com/verus-lang/verus/blob/main/source/rust_verify/example/bitvector_equivalence.rs)
 * [miscellaneous](https://github.com/verus-lang/verus/blob/main/source/rust_verify/example/bitvector_basic.rs)
