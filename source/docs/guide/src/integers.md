# Integer types

Rust supports various
[fixed-bit-width integer types](https://doc.rust-lang.org/book/ch03-02-data-types.html#integer-types):

- `i8`, `i16`, `i32`, `i64`, `i128`, `isize`
- `u8`, `u16`, `u32`, `u64`, `u128`, `usize`

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

The bounds of `usize` and `isize` are platform dependent.
By default, Verus assumes that these types may be either 32 bits or 64 bits wide,
but [this assumption may be configured](./reference-global.md#with-usize-and-isize).
Verus recognizes the constants
[`usize::BITS`](https://doc.rust-lang.org/std/primitive.usize.html#associatedconstant.BITS),
[`usize::MAX`](https://doc.rust-lang.org/std/primitive.usize.html#associatedconstant.MAX),
[`isize::MAX`](https://doc.rust-lang.org/std/primitive.isize.html#associatedconstant.MAX),
and
[`isize::MIN`](https://doc.rust-lang.org/std/primitive.isize.html#associatedconstant.MIN),
which are useful for reasoning symbolically
about the `usize` integer range.

## Using integer types in specifications

Since there are 14 different integer types (counting `int`, `nat`, `u8`...`usize`, and `i8`...`isize`),
it's not always obvious which type to use when writing a specification.
Our advice is to be as general as possible by default:
- Use `int` by default, since this is the most general type and is supported most efficiently by the SMT solver.
  - Example: the Verus [sequence library](https://github.com/verus-lang/verus/blob/main/source/vstd/seq.rs)
    uses `int` for most operations, such as indexing into a sequence.
  - Note: as discussed below, most arithmetic operations in specifications produce values of type `int`,
    so it is usually most convenient to write specifications in terms of `int`.
- Use `nat` for return values and datatype fields where the 0 lower bound is likely to provide useful information,
  such as lengths of sequences.
  - Example: the Verus [`Seq::len()` function](https://github.com/verus-lang/verus/blob/main/source/vstd/seq.rs)
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

## Integer constants

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
are allowed to all have different types ---
you can use `<=`, `<`, `>=`, `>`, `==`, and `!=` to compare values of different integer types inside ghost code
(e.g. comparing a `u8` to an `int` in `u < i`).

Constants with the suffix `int` and `nat` can be arbitrarily large:

```rust
{{#include ../../../rust_verify/example/guide/integers.rs:test_consts_large}}
```

## Integer coercions using "as"

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

note: recommendation not met: value may be out of range of the target type (use `#[verifier::truncate]` on the cast to silence this warning)
   |
   |     let u: u8 = v as u8;
   |                 ^
```

See [the reference](./reference-as.md) for more on how Verus defines as-truncation and how
to reason about it.

## Integer arithmetic

Integer arithmetic behaves a bit differently in ghost code than in executable code.

In **executable** code, we frequently have to reason about integer overflow,
and in fact, Verus requires us to prove the absence of overflow.
The following operation fails because the arithmetic might produce an operation greater
than 255:

```rust
{{#include ../../../rust_verify/example/guide/integers.rs:test_sum}}
```

```
error: possible arithmetic underflow/overflow
   |
   |     let sum1: u8 = x + y; // FAILS: possible overflow
   |                    ^^^^^
```

In **ghost** code, however,
common arithmetic operations
(`+`, `-`, `*`, `/`, `%`) never overflow or wrap.
To make this possible, Verus widens the results of many operations;
for example, adding two `u8` values is widened to type `int`.

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

In general in ghost code,
Verus widens native Rust integer types to `int` for operators like `+`, `-`, and `*` that might overflow;
the [reference page](./spec-arithmetic.md) describes the widening rules in more detail.

Here are some more tips to keep in mind:

 * In ghost code, `/` and `%` compute
    [Euclidean division and remainder](https://en.wikipedia.org/wiki/Euclidean_division),
    rather than Rust's truncating division and remainder,
    when operating on negative left-hand sides or negative right-hand sides.
 * Division-by-0 and mod-by-0 are errors in executable code and are unspecified in ghost code
   (see [Ghost code vs. exec code](./ghost_vs_exec.md) for more detail).
 * The named arithmetic functions, `add(x, y)`, `sub(x, y)`, and `mul(x, y)`, do not perform widening, and thus
    have truncating behavior, even in ghost code. Verus also recognizes some Rust functions like
    [`wrapped_add`](https://doc.rust-lang.org/std/primitive.u32.html#method.wrapping_add)
    and [`checked_add`](https://doc.rust-lang.org/std/primitive.u32.html#method.checked_add),
    which may be used in either executable or ghost code.
