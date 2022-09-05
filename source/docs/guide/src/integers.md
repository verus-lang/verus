# Integer types

Rust supports various
[fixed-bit-width integer types](https://doc.rust-lang.org/book/ch03-02-data-types.html#integer-types):

- `u8`, `u16`, `u32`, `u64`, `u128`, `usize`
- `i8`, `i16`, `i32`, `i64`, `i128`, `isize`

To these, Verus adds two more integer types to represent arbitrarily large integers in specifications:

- int
- nat

The type `int` is the most fundamental type for reasoning about integer arithmetic in Verus.
It represents [all mathematical integers](https://en.wikipedia.org/wiki/Integer),
both positive and negative.
The SMT solver contains direct support for reasoning about values of type `int`.

Internally, Verus uses `int` to represent the other integer types,
adding mathematical constraints to limit the range of the integers.
For example, a value of the type `nat` of [natural numbers](https://en.wikipedia.org/wiki/Natural_number) 
is a mathematical integer constrained to be greater than or equal to `0`.
Rust's fixed-bit-width integer types have both a lower and upper bound;
a `u8` value is an integer constrained to be greater than or equal to `0` and less than 256:

```rust
{{#include ../../../rust_verify/example/guide/integers.rs:test_u8}}
```

(The bounds of `usize` and `isize` are platform dependent.
By default, Verus assumes that these types may be either 32 bits or 64 bits wide,
but this can be configured with the Verus command-line option `--arch-word-bits`.)

# Using integer types in specifications

Since there are 14 different integer types (counting `int`, `nat`, `u8`...`usize`, and `i8`...`isize`),
it's not always obvious which type to use when writing a specification.
Our advice is to be as general as possible by default:
- Use `int` by default, since this is the most general type and is supported most efficiently by the SMT solver.
  - Example: the Verus [sequence library](https://github.com/secure-foundations/verus/blob/main/source/pervasive/seq.rs)
    uses `int` for most operations, such as indexing into a sequence.
  - Note: as discussed below, most arithmetic operations in specifications produce values of type `int`,
    so it is usually most convenient to write specifications in terms of `int`.
- Use `nat` for return values and datatype fields where the 0 lower bound is likely to provide useful information,
  such as lengths of sequences.
  - Example: the Verus [`Seq::len()` function](https://github.com/secure-foundations/verus/blob/main/source/pervasive/seq.rs)
    returns a `nat` to represent the length of a sequence.
  - The type `nat` is also handy for proving that recursive definitions terminate;
    you might to define a recursive `factorial` function to take a parameter of type `nat`,
    if you don't want to provide a definition of `factorial` for negative integers.
- Use fixed-width integer types for fixed-with values such as bytes.
  - Example: the bytes of a network packet can be represented with type `Seq<u8>`, an arbitrary-length sequence of 8-bit values.

Note that `int` and `nat` are usable only in ghost code;
they cannot be compiled to executable code.
For example, the following will not work:

```rust
fn main() {
    let i: int = 5; // FAILS: executable variable `i` cannot have type `int`, which is ghost-only
}
```

# Integer constants

As in ordinary Rust, integer constants in Verus can include their type as a suffix
(e.g. `7u8` or `7u32` or `7int`) to precisely specify the type of the constant:

```rust
{{#include ../../../rust_verify/example/guide/integers.rs:test_consts}}
```

Usually, but not always, Verus and Rust will be able to infer types for integer constants,
so that you can omit the suffixes unless the Rust type checker complains about not being able to infer the type:

```rust
{{#include ../../../rust_verify/example/guide/integers.rs:test_consts_infer}}
```

Note that the values `0`, `u`, `i`, `n`, and `4` in the expression `0 <= u < i < n < 4`
are allowed to all have different types --
you can use `<=`, `<`, `>=`, `>`, `==`, and `!=` to compare values of different integer types inside ghost code
(e.g. comparing a `u8` to an `int` in `u < i`).

Constants with the suffix `int` and `nat` can be arbitrarily large:

```rust
{{#include ../../../rust_verify/example/guide/integers.rs:test_consts_large}}
```

# Integer coercions using "as"

As in ordinary rust, the `as` operator coerces one integer type to another.
In ghost code, you can use `as int` or `as nat` to coerce to `int` or `nat`:

```rust
{{#include ../../../rust_verify/example/guide/integers.rs:test_coerce}}
```

You can use `as` to coerce a value `v` to a type `t` even if `v` is too small or too large to fit in `t`.
However, if the value `v` is outside the bounds of type t,
then the expression `v as t` will produce some arbitrary value of type `t`:

```rust
{{#include ../../../rust_verify/example/guide/integers.rs:test_coerce_fail}}
```

This produces an error for the assertion, along with a hint that the value in the `as` coercion might have been out of range:

```
error: assertion failed
   |
   |     assert(u == v); // FAILS, because u has type u8 and therefore cannot be equal to 257
   |            ^^^^^^ assertion failed

note: recommendation not met: value may be out of range of the target type (use `#[verifier(truncate)]` on the cast to silence this warning)
   |
   |     let u: u8 = v as u8;
   |                 ^
```

# Integer arithmetic

Integer arithmetic behaves differently in ghost code than in executable code.
In particular, in ghost code, the `+`, `-`, and `*` operations generate results of type `int`,
so that the arithmetic operations cannot underflow or overflow.
For example, in the following code, the executable operation `let sum1: u8 = x + y`
might overflow, producing a value greater than `255` that does not fit inside the result value of type `u8`:

```rust
{{#include ../../../rust_verify/example/guide/integers.rs:test_sum}}
```

For overflows in executable code, Verus reports an error:

```
error: possible arithmetic underflow/overflow
   |
   |     let sum1: u8 = x + y; // FAILS: possible overflow
   |                    ^^^^^
```

By contrast, the ghost operation `let sum2: int = x + y` will produce a value of type `int` in the range `0`...`510`,
even though the inputs `x` and `y` have type `u8`:

```rust
{{#include ../../../rust_verify/example/guide/integers.rs:test_sum2}}
```

Since `+` does not overflow in ghost code, we can easily write specifications *about* overflow.
For example, to make sure that the executable `x + y` doesn't overflow,
we simply write `requires x + y < 256`, relying on the fact that `x + y` is widened to type `int`
in the `requires` clause:

```rust
{{#include ../../../rust_verify/example/guide/integers.rs:test_sum3}}
```

Also note that the inputs need not have the same type;
you can add, subtract, or multiply one integer type with another:

```rust
{{#include ../../../rust_verify/example/guide/integers.rs:test_sum_mixed}}
```

If you don't want to widen the results of addition, subtraction, or multiplication to type `int`,
Verus also includes functions `add(a, b)`, `sub(a, b)`, and `mul(a, b)` that return the input type
(both `a` and `b` must have the same type), returning an arbitrary value of that type in case of overflow or underflow:

```rust
{{#include ../../../rust_verify/example/guide/integers.rs:test_sum_add_sub}}
```

The following table summarizes the types of integer operations in ghost code:

| operation | left-hand side type | right-hand side type | result type | notes                |
|-----------|---------------------|----------------------|-------------|----------------------|
| <=        | t1                  | t2                   | bool        |                      |
| <         | t1                  | t2                   | bool        |                      |
| >=        | t1                  | t2                   | bool        |                      |
| >         | t1                  | t2                   | bool        |                      |
| ==        | t1                  | t2                   | bool        |                      |
| !=        | t1                  | t2                   | bool        |                      |
| +         | t1                  | t2                   | int         | except for nat + nat |
| -         | t1                  | t2                   | int         |                      |
| *         | t1                  | t2                   | int         | except for nat * nat |
| +         | nat                 | nat                  | nat         |                      |
| *         | nat                 | nat                  | nat         |                      |
| /         | t                   | t                    | int         | for i8...isize, int  |
| /         | t                   | t                    | t           | for u8...usize, nat  |
| %         | t                   | t                    | t           |                      |
| add(_, _) | t                   | t                    | t           |                      |
| sub(_, _) | t                   | t                    | t           |                      |
| mul(_, _) | t                   | t                    | t           |                      |
| bitwise op| t                   | t                    | t           |                      |

Note that for convenience, addition and multiplication on two `nat` values return `nat`, not `int`,
so that for `n` of type `nat`, you can write `n + 1` to get a `nat` without having to write
`add(n, 1)` or `(n + 1) as nat`.

Finally, note that in ghost code, `/` and `%` compute
[Euclidean division and remainder](https://en.wikipedia.org/wiki/Euclidean_division),
rather than Rust's truncating division and remainder,
when operating on negative left-hand sides or negative right-hand sides.
