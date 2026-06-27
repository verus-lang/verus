# Arithmetic in spec code

**Note:** This reference page is about arithmetic in _Verus specification code_.
This page is **does not apply** to arithmetic is _executable Rust code_.

For an introduction to Verus arithmetic, see
[Integers and arithmetic](./integers.md).

### Syntax

```verus-grammar
V@[arith_expr] ::= V@[spec_expr] \+ V@[spec_expr]
             | V@[spec_expr] - V@[spec_expr]
             | - V@[spec_expr]
             | V@[spec_expr] \* V@[spec_expr]
             | V@[spec_expr] / V@[spec_expr]
             | V@[spec_expr] % V@[spec_expr]

V@[ineq_expr] ::= | V@[spec_expr] <= V@[spec_expr]
              | V@[spec_expr] <  V@[spec_expr]
              | V@[spec_expr] >= V@[spec_expr]
              | V@[spec_expr] >  V@[spec_expr]
```

### Typing

In spec code, the results of arithmetic are automatically widened to avoid overflow or wrapping.
The types of various operators, given as functions of the input types, are summarized in
the below table.
Note that in most cases, the types of the inputs are not required to be the same.

| operation | LHS type            | RHS type             | result type | notes                |
|-----------|---------------------|----------------------|-------------|----------------------|
| `<=` `<` `>=` `>`  | t<sub>1</sub>  | t<sub>2</sub>    | bool        |                      |
| `+`         | t<sub>1</sub>     | t<sub>2</sub>        | int         | except for nat + nat |
| `+`         | nat               | nat                  | nat         |                      |
| `-`         | t<sub>1</sub>     | t<sub>2</sub>        | int         |                      |
| `*`         | t<sub>1</sub>     | t<sub>2</sub>        | int         | except for nat * nat |
| `*`         | nat               | nat                  | nat         |                      |
| `/`         | t                 | t                    | int         | for i8...isize, int  |
| `/`         | t                 | t                    | t           | for u8...usize, nat  |
| `%`         | t                 | t                    | t           |                      |
| `add(_, _)` | t                 | t                    | t           |                      |
| `sub(_, _)` | t                 | t                    | t           |                      |
| `mul(_, _)` | t                 | t                    | t           |                      |

### Semantics

Due to type-widening, the result of any arithmetic operator is the exact result of the arithmetic
without any consideration for overflow or truncation, with the exception of the named
`add`, `sub`, and `mul` operators, which truncate.

**Quotient and remainder.**
In Verus specifications, `/` and `%` are defined by [Euclidean division](https://en.wikipedia.org/wiki/Euclidean_division).

For `b != 0`, the quotient `a / b` and remainder `a % b` are defined as the unique integers
`q` and `r` such that:

 * `b * q + r == a`
 * `0 <= r < |b|`.

Note that:

 * The remainder `a % b` is always nonnegative
 * The quotient is "floor division" when b is positive
 * The quotient is "ceiling division" when b is negative

Also note that `a / b` and `a % b` are unspecified when `b == 0`.
However, because all spec functions
are total, division-by-0 or mod-by-0 are not hard errors.

> [!DIFF]
> The `/` and `%` in spec code may differ from Rust's `/` and `%` operators in executable code
> when either operand is negative.
>
> For `/`:
>
> |               | Verus spec `/` (Euclidean) | Rust `/` |
> |---------------|----------------------------|----------|
> | `7 / 3`       | 2                          | 2        |
> | `7 / (-3)`    | -2                         | -2       |
> | `(-7) / 3`    | -3                         | -2       |
> | `(-7) / (-3)` | 3                          | 2        |
>
> For `%`:
>
> |               | Verus spec `%` (Euclidean) | Rust `%` |
> |---------------|----------------------------|----------|
> | `7 % 3`       | 1                          | 1        |
> | `7 % (-3)`    | 1                          | 1        |
> | `(-7) % 3`    | 2                          | -1       |
> | `(-7) % (-3)` | 2                          | -1       |

## More advanced arithmetic

The Verus standard library includes the following additional arithmetic functions
usable in spec expressions:
* Exponentiation ([`vstd::arithmetic::power::pow`](https://verus-lang.github.io/verus/verusdoc/vstd/arithmetic/power/fn.pow.html))
* Power of two ([`vstd::arithmetic::power2::pow2`](https://verus-lang.github.io/verus/verusdoc/vstd/arithmetic/power2/fn.pow2.html))
* Integer logarithm ([`vstd::arithmetic::logarithm::log`](https://verus-lang.github.io/verus/verusdoc/vstd/arithmetic/logarithm/fn.log.html))
