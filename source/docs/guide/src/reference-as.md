# Coercion with `as`

## Coercions on integer types and `char`

Any of the following types may be coerced to any of the other types:

 * `i8`, `i16`, `i32`, `i64`, `i128`, `isize`
 * `u8`, `u16`, `u32`, `u64`, `u128`, `usize`
 * `int`
 * `nat`
 * [`char`](./char.md)

Note that this is more permissive than `as` in Rust exec code. For example, Rust does
not permit using `as` to cast from a `u16` to a `char`, but this is allowed in Verus
spec code.

### Definition

Verus defines `as`-casting as follows:

 * Casting to an `int` is always defined and does not require truncation.
 * Casting to a `nat` is _unspecified_ if the input value is negative.
 * Casting to a `char` is _unspecified_ if the input value is outside the [allowed `char` values](./char.md).
 * Casting to any other finite-size integer type is defined as _truncation_ — taking the
    lower N bits for the appropriate N, then interpreting the result as a signed or unsigned
    integer.

### Reasoning about truncation

The definition of truncation is _not_ exported in Verus's default prover mode
(i.e., it behaves as if it is unspecified). To reason about truncation, use
[the bit-vector solver](./reference-assert-by-bit-vector.md)
or the [compute solver](./reference-assert-by-compute.md).

Also note that the value of N for `usize` and `isize` may be [configured with the `global` directive](./reference-global.md).

## Coercions on pointers

### Pointers to integers

You can coerce any pointer to any integer type. For a pointer `ptr: *mut T` or `ptr: *const T`,
the expression `ptr as INT_TYPE` is equivalent to `ptr.addr() as INT_TYPE`.

> **Note:** Using `ptr.addr()` explicitly is often clearer than an `as`-cast.

> **Note:** Verus does not support casting an integer to a pointer using `as`. Instead, use a function like [`with_addr`](https://verus-lang.github.io/verus/verusdoc/vstd/std_specs/struct.VstdSpecsForRustStdLib.html#method._verus_external_fn_specification_1018__60__32__42__32_mut_32_T_32__62__32__58__58__32_with__addr) or [`with_exposed_provenance`](https://verus-lang.github.io/verus/verusdoc/vstd/raw_ptr/fn.with_exposed_provenance.html).

### Pointers to pointers

Verus supports some pointer-to-pointer coercions, including between `*const` and `*mut` pointers:

 * `*mut T` to `*const T` (identity function)
 * `*const T` to `*mut T` (identity function)

And other kinda of coercions:

 * `*mut T` to `*mut S` for any `S: Sized` ([spec](https://verus-lang.github.io/verus/verusdoc/vstd/raw_ptr/fn.spec_cast_ptr_to_thin_ptr.html))
 * `*mut [T; N]` to `*mut [T]` ([spec](https://verus-lang.github.io/verus/verusdoc/vstd/raw_ptr/fn.spec_cast_array_ptr_to_slice_ptr.html))
 * `*mut [T]` to `*mut [U]` ([spec](https://verus-lang.github.io/verus/verusdoc/vstd/raw_ptr/fn.spec_cast_slice_ptr_to_slice_ptr.html))
 * `*mut [T]` to `*mut str` ([spec](https://verus-lang.github.io/verus/verusdoc/vstd/raw_ptr/fn.spec_cast_slice_ptr_to_str_ptr.html))
 * `*mut str` to `*mut [T]` ([spec](https://verus-lang.github.io/verus/verusdoc/vstd/raw_ptr/fn.spec_cast_str_ptr_to_slice_ptr.html))

And the equivalent set of casts for `*const` pointers.
