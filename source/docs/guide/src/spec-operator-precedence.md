# Operator Precedence

| Operator                 | Associativity         |
|--------------------------|-----------------------|
| **Binds tighter**                                |
| [`.` `->`](./datatypes_struct.md)                    | left                  |
| [`is` `matches`](./datatypes_enum.md)                    | left                  |
| [`*` `/` `%`](./spec-arithmetic.md)                    | left                  |
| [`+` `-`](./spec-arithmetic.md)                      | left                  |
| [`<<` `>>`](./spec-bit-operators.md)                    | left                  |
| [`&`](./spec-bit-ops.md)                        | left                  |
| [`^`](./spec-bit-ops.md)                        | left                  |
| [<code>&#124;</code>](./spec-bit-ops.md)                   | left                  |
| [`!==` `==` `!=`](./spec-equality.md) `<=` `<` `>=` `>`  | requires parentheses  |
| `&&`                       | left                  |
| <code>&#124;&#124;</code>             | left                  |
| [`==>`](./reference-implication.md)                      | right                 |
| [`<==`](./reference-implication.md)                      | left                  |
| [`<==>`](./reference-implication.md)                     | requires parentheses  |
| `..`                       | left                  |
| `=`                        | right                 |
| closures; [`forall`, `exists`](./spec-quantifiers.md); [`choose`](./spec-choose.md) | right                 |
| [`&&&`](./prefix-and-or.md)                      | left                  |
| [<code>&#124;&#124;&#124;</code>](./prefix-and-or.md)       | left                  |
| **Binds looser**                                 |

All operators that are from ordinary Rust have the same precedence-ordering as in
ordinary Rust.
See also the [Rust operator precedence](https://doc.rust-lang.org/reference/expressions.html).
