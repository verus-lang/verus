# Attributes

Verus has a number of attributes that control how code is interpreted.

## Controlling visibility

These attributes control when definitions are visibile for verification performance reasons.

--------
| `#[verifier(opaque)]` | Makes the function opaque; it can be revealed with `reveal(name)` or `reveal_with_fuel(name, fuel)` if it is recursive. |
--------

## Controlling triggering

These attributes control how triggers are selected for quantifiers to ensure quantifiers are instantiated and to optimize verification performance.

--------
| `#[auto]` | Accepts a trigger for a quantifier that was chosen automatically chosen, but with low confidence, which causes a warning. |
| `#[trigger]` | Manually annotates an expression as a trigger for the enclosing quantifier. |
| `#![trigger <expr1>, <expr2>]` | Selects a set of triggers for this quantifiers. Applies to the quantifier, rather than the specific expression. |
--------

## Trusting definitions (ignore them in the verifier)

These attributes allows hiding definitions from the verifier, so that they are trusted to be correct, instead of verified.

--------
| `#[verifer(external_body)]` |  |

