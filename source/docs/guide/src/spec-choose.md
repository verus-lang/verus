# Such that (`choose`)

For an intuition-guided introduction, see [exists and choose](exists.md).

`choose` is a **spec-mode only** expression that returns an arbitrary value satisfying
a given predicate. It is the Hilbert choice operator (also known as epsilon or the
[such-that operator](https://en.wikipedia.org/wiki/Epsilon_calculus)).

## Syntax

```verus-grammar
V@[choose_expr] ::= choose |R@[binders...]| V@[spec_expr]
```

`SpecExpr` is a spec-mode `bool` expression. When multiple variables are bound, the result
is a tuple `(T1, T2, ...)`.

## Semantics

`choose|x: T| P(x)` evaluates to some value of type `T`:

- If there exists a value `x` of type `T` such that `P(x)` is true, `choose` returns
  one such value (the choice is arbitrary but deterministic — the same expression always
  returns the same value).
- If no such value exists, `choose` returns an arbitrary value of type `T` (with no
  guarantee that `P` holds of it).

Therefore, to use the result of `choose|x: T| P(x)` with the guarantee that `P` holds,
you must separately establish `exists|x: T| P(x)`. Verus will then allow you to conclude
`P(choose|x: T| P(x))`.

## Examples

```rust
// Requires a proof that such an i exists; choose picks one.
proof fn get_zero_index(s: Seq<int>) -> (i: int)
    requires exists|i: int| 0 <= i < s.len() && s[i] == 0,
    ensures 0 <= i < s.len() && s[i] == 0,
{
    choose|i: int| 0 <= i < s.len() && s[i] == 0
}
```

```rust
// Multiple variables — result is a tuple.
let (i, j): (int, int) = choose|i: int, j: int| less_than(i, j);
```

## Relationship to `exists`

`choose` and `exists` are complementary:

- `exists|x: T| P(x)` asserts that a satisfying value *exists*.
- `choose|x: T| P(x)` *extracts* a satisfying value, given that one exists.

Triggers on a `choose` expression work the same way as on `exists`: Verus uses them to
find a witness in the proof context. See [Trigger annotations](./trigger-annotations.md)
for details.
