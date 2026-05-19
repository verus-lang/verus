# Such that (`choose`)

For an intuition-guided introduction, see [exists and choose](exists.md).

`choose` is a **spec-mode only** expression that returns an arbitrary value satisfying
a given predicate. It is the Hilbert choice operator (also known as the epsilon operator or
[such-that operator](https://en.wikipedia.org/wiki/Epsilon_calculus)).

### Syntax

```verus-grammar
V@[choose_expr] ::= choose |R@[binders...]| V@[spec_expr]
```

### Typing

The body V@[spec_expr] must have type `bool`. The bound variables are available as spec-mode
variables within the body. The return type depends on the number of binders:

 * For a single binder `x: T`, the expression has type `T`.
 * For multiple binders `x: T, y: U, ...`, the expression has tuple type `(T, U, ...)`.

### Semantics

`choose|x: T| P(x)` evaluates to some value of type `T`:

- If there exists a value `x` of type `T` such that `P(x)` is `true`, `choose` returns one
  such value. The choice is deterministic: the same expression always returns the same value.
- If no such value exists, `choose` returns an arbitrary value of type `T` with no guarantee
  that `P` holds of it.

To use the result with the guarantee that `P` holds, you must separately establish
`exists|x: T| P(x)`. Verus will then allow you to conclude `P(choose|x: T| P(x))`.

`choose` and `exists` are complementary: `exists|x: T| P(x)` asserts that a satisfying value
*exists*, while `choose|x: T| P(x)` *extracts* one. Triggers on `choose` work the same way
as on `exists`; see [Trigger annotations](./trigger-annotations.md) for details.

**Example:**

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
