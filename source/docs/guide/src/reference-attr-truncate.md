# Truncate

The `#[verifier::truncate]` attribute can be added to expressions to silence
recommends-checking regarding out-of-range as-casts.

When casting from one integer
type to another, Verus usually inserts recommends-checks that the source
value fits into the target type. For example, if `x` is a `u32` and we cast it
via `x as u8`, Verus will add a recommends-check that `0 <= x < 256`. 
However, sometimes truncation is the _desired_ behavior, so 
`#[verifier::truncate]` can be used to signal this intent, suppressing
the recommends-check.

Note that the attribute is optional, even when truncation behavior is intended.
The only effect of the attribute is to silence the recommends-check, which is
already elided if the enclosing function body has no legitimate verification errors.

**Aside.** When truncation is intended, [the bit-vector solver mode](./reference-assert-by-bit-vector.md) is often useful for writing proofs about truncation.
