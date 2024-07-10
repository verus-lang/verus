# The `char` primitive

Citing the [Rust documentation on `char`](https://doc.rust-lang.org/std/primitive.char.html):

> A char is a ‘Unicode scalar value’, which is any ‘Unicode code point’ other than a surrogate code point. This has a fixed numerical definition: code points are in the range 0 to 0x10FFFF, inclusive. Surrogate code points, used by UTF-16, are in the range 0xD800 to 0xDFFF.

Verus treats `char` similarly to bounded integer primitives like `u64` or `u32`: We represent
`char` as an integer. A `char` always carries an invariant that it is in the prescribed set
of allowed values:

`[0, 0xD7ff] ∪ [0xE000, 0x10FFFF]`

In spec code, chars can be cast to an from other integer types using `as`. This is more
permissive than exec code, which disallows many of these coercions.
As with other coercions, the result may be undefined if the integer being coerced does not
fit in the target range.
