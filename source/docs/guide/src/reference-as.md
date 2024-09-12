# Coercion with `as`

In spec code, any "integer type" may be coerced to any other integer type via `as`.
For the sake of this page, "integer type" means any of the following:

 * `i8`, `i16`, `i32`, `i64`, `i128`, `isize`
 * `u8`, `u16`, `u32`, `u64`, `u128`, `usize`
 * `int`
 * `nat`
 * [`char`](./char.md)

Note that this is more permissive than `as` in Rust exec code. For example, Rust does
not permit using `as` to cast from a `u16` to a `char`, but this is allowed in Verus
spec code.

## Definition

Verus defines `as`-casting as follows:

 * Casting to an `int` is always defined and does not require truncation.
 * Casting to a `nat` is _unspecified_ if the input value is negative.
 * Casting to a `char` is _unspecified_ if the input value is outside the [allowed `char` values](./char.md).
 * Casting to any other finite-size integer type is defined as _truncation_ — taking the
    lower N bits for the appropriate N, then interpreting the result as a signed or unsigned
    integer.

## Reasoning about truncation

The definition of truncation is _not_ exported in Verus's default prover mode
(i.e., it behaves as if it is unspecified). To reason about truncation, use
[the bit-vector solver](./reference-assert-by-bit-vector.md)
or the [compute solver](./reference-assert-by-compute.md).

Also note that the value of N for `usize` and `isize` may be [configured with the `global` directive](./reference-global.md).
