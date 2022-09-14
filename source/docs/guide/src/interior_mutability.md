# Interior Mutability

The [Interior Mutability pattern](https://doc.rust-lang.org/book/ch15-05-interior-mutability.html)
is a particular Rust pattern wherein the user is able to manipulate the contents of a value
accessed via a shared borrow `&`. (Though `&` is often referred to as "immutable borrow,"
we will call it a "shared borrow" here, to avoid confusion.)
Two common Rust types illustrating interior mutability are
[`Cell` and `RefCell`](https://doc.rust-lang.org/std/cell/).
Here, we will overview the equivalent concepts in Verus.

### Mutating stuff that can't mutate

To understand the key challenge in verifying these interior mutability patterns,
recall an important fact of Verus's SMT encoding. Verus assumes that any value of type `&T`,
for any type `T`, can never change. However, we also know that the contents of a
`&Cell<V>` might change. After all, that's the whole point of the `Cell<T>` type!

The inescapable conclusion, then, is that
_the value taken by a `Cell<T>` in Verus' SMT encoding must not depend on the cell's contents_.
Instead, the SMT "value" of a `Cell<T>` is nothing more than a unique identifier for the Cell.
In some regards, it may help to think of `Cell<T>` as similar to a pointer `T*`.
The value of the `Cell<T>` is _only_ its identifier (its "pointer address") rather than
its contents ("the thing pointed to be a pointer"). Of course, it's _not_ a pointer, but
from the perspective of the encoding, it might as well be.

Note one immediate ramification of this property:
[Verus' pure equality `===`](./equality.md) on `Cell` types cannot possibly
give the same results as Rust's standard `==` (`eq`) on `Cell` types.
Rust's `==` function actually compares the contents of the cells.
But pure equality, `===`, which must depend on the SMT encoding values,
cannot possibly depend on the contents!
Instead, `===` compares two cells as equal only if they are _the same cell_.

(TODO finish writing this chapter)
