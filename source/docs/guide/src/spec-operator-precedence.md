# Operator Precedence

The table below defines operator precedence from tightest-binding (top) to loosest-binding (bottom).

| Operator                                                                             | Associativity        | Grammar                                                 |
|--------------------------------------------------------------------------------------|----------------------|---------------------------------------------------------|
| **Binds tighter**                                                                    |                      |                                                         |
| [`.` `->`](./datatypes_struct.md)                                                    | left                 |                                                         |
| [`is` `matches`](./datatypes_enum.md)                                                | left                 |                                                         |
| [`*` `/` `%`](./spec-arithmetic.md)                                                  | left                 | V@[arith_expr]                                          |
| [`+` `-`](./spec-arithmetic.md)                                                      | left                 | V@[arith_expr]                                          |
| [`<<` `>>`](./spec-bit-ops.md)                                                       | left                 | V@[shl_expr] V@[shr_expr]                               |
| [`&`](./spec-bit-ops.md)                                                             | left                 | V@[bit_and_expr]                                        |
| [`^`](./spec-bit-ops.md)                                                             | left                 | V@[bit_xor_expr]                                        |
| [<code>&#124;</code>](./spec-bit-ops.md)                                             | left                 | V@[bit_or_expr]                                         |
| [`!==` `==` `!=`](./spec-equality.md) `<=` `<` `>=` `>`                              | requires parentheses | V@[equality_expr] V@[ineq_expr]                         |
| `&&`                                                                                 | left                 | V@[and_expr]                                            |
| <code>&#124;&#124;</code>                                                            | left                 | V@[or_expr]                                             |
| [`==>`](./reference-implication.md)                                                  | right                | V@[implies_expr]                                        |
| [`<==`](./reference-implication.md)                                                  | left                 | V@[explies_expr]                                        |
| [`<==>`](./reference-implication.md)                                                 | requires parentheses | V@[iff_expr]                                            |
| `..`                                                                                 | left                 |                                                         |
| `=`                                                                                  | right                |                                                         |
| closures; [`forall`, `exists`](./spec-quantifiers.md); [`choose`](./spec-choose.md)  | right                | V@[forall_expr] V@[exists_expr] V@[choose_expr]         |
| [`&&&`](./prefix-and-or.md)                                                          | left                 | V@[prefix_and_expr]                                     |
| [<code>&#124;&#124;&#124;</code>](./prefix-and-or.md)                                | left                 | V@[prefix_or_expr]                                      |
| **Binds looser**                                                                     |                      |                                                         |

All operators that are from ordinary Rust have the same precedence-ordering as in
ordinary Rust.
See also the [Rust operator precedence](https://doc.rust-lang.org/reference/expressions.html).
