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

So, with these challenges in mind, how _do_ we handle interior mutability in Verus?

There are a few different approaches we can take.

 * When retrieving a value from the interior of a Cell-like data structure, we can model
   this as non-deterministically receiving a value of the given type.
   At first, this might seem like it gives us too little to work with for verifying
   correctness properties. However, we can impose additional structure by specifying
   _data invariants_ to restrict the space of possible values.

 * Track the exact value using `tracked ghost` code.

More sophisticated data structures---especially concurrent ones---often require a careful
balance of both approaches. We'll cover both here.

### Data Invariants with `InvCell`.

[`InvCell`](https://verus-lang.github.io/verus/verusdoc/lib/pervasive/cell/struct.InvCell.html),
provided by Verus' standard library, is an example of the "data invariant" approach.
When constructing a new `InvCell<T>`, the user specifies a data invariant: some boolean predicate
over the type `T` which tells the cell what values are allowed to be stored.
Then, the `InvCell` only has to impose the restriction that whenever the user writes to the cell,
the value `val` being written has to satisfy the predicate, `cell.inv(val)`.
In exchange, though, whenever the user _reads_ from the cell, they know the value they
receive satisfies `cell.inv(val)`.

Here's an example using an `InvCell` to implement a memoized function:

```rust
{{#include ../../../rust_verify/example/guide/interior_mutability.rs:inv_cell_example}}
```

### Tracked ghost state with `PCell`.

(TODO finish writing this chapter)


