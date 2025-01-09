# Bit operators

## Definitions

### `&`, `|`, and `^`

These have the usual meaning: bitwise-OR, bitwise-AND, and bitwise-XOR. Verus, like Rust, requires the input operands to be the same
type, even in specification code.
However, as binary operators defined over the integers,
&#x2124; x &#x2124; &#x2192; &#x2124;,
these operations are independent of bitwidth.
This is true even for negative operands, as a result of the way two's complement
[sign-extension](https://en.wikipedia.org/wiki/Sign_extension) works.

### `>>` and `<<`

Verus specifications, like Rust, does not require the left and right sides of a _shift_ operator
to be the same type. Shift is unspecified when the right-hand side is negative.
Unlike in executable code, however, there is no _upper_ bound on the right-hand side.

`a << b` and and `a >> b` both have the same type as `a`.

Right shifts can be defined over the integers 
&#x2124; x &#x2124; &#x2192; &#x2124; independently of the input bitwidth.

For `<<`, however, the result _does_ depend on the input type
because a left shift may involve truncation if some bits get shifted "off to the left".
There is no widening to an `int` (unlike, say, Verus specification `+`).

## Reasoning about bit operators

In Verus's default prover mode, the definitions of these bitwise operators are not exported.
To prove nontrivial facts about bitwise operators, use
[the bit-vector solver](./reference-assert-by-bit-vector.md)
or the [compute solver](./reference-assert-by-compute.md).
