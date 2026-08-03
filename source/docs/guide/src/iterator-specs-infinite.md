# Implementing Iterator Specifications for Infinite Iterators

Somewhat surprisingly, we can also 

Let's start with the most common class of iterators: those that eventually
return `None` and then continue to return `None` on all subsequent calls to
`next()`.  To illustrate the [steps needed to verify an iterator implementation](iterator-specs.md) 
for a custom type, in the example below, we'll imagine that `Vec`
doesn't provide an iterator, so we're going to implement one for it.

### 1. The iterator struct

`VecIterator` holds a reference to the underlying `Vec` plus indices `i` and `j`
marking the current and end positions. The type invariant enforces that `i <= j <=
v.len()` at all times.

```rust
{{#include ../../../../examples/guide/iterators.rs:iter_def}}
```

### 2. The `next` method

This is an ordinary Rust `Iterator` implementation with no Verus-specific annotations.
It uses the type invariant to prove that it meets the Verus specification for `next()`.

```rust
{{#include ../../../../examples/guide/iterators.rs:normal_iter}}
```

### 3. The spec implementation

In `vstd`, Verus provides `IteratorSpec`, an extension of the Rust
[`Iterator`](https://doc.rust-lang.org/std/iter/trait.Iterator.html) trait that
defines a variety of specification functions, as well as the Verus specs for
the `next()` function.  To enable us to reason about our custom iterator, we
need to implement the Verus-provided `IteratorSpecImpl` trait (not the
`IteratorSpec` trait that defines the specs -- see ["External trait
specifications"](external_trait_specifications.md) for more details).
Here's a brief summary of the specification functions, with a focus
on how we define them for our custom iterator.

- **`obeys_prophetic_iter_laws`** — return `true` to assert that this iterator satisfies
  the Verus specification for `next`.  Most iterator implementations should return `true` here,
  and most iterator adaptors should return their inner iterator's value.  By returning `true`,
  we're saying that the iterator will eventually return `None`, and after that point, continue 
  to return `None`.  
- **`remaining`** — a prophetic spec function returning the sequence of items that the iterator will
  eventually produce. For `VecIterator`, this is the subrange `v[i..j]`.  Note that `remaining`
  returns a `Seq<Self::Item>`; as a result, because our `VecIterator`'s `Item` is `&T`, its
  `remaining` function will return `Seq<&T>`.  The sequence library in `vstd` provides the convenience
  function `as_ref` to convert `Seq<T>` to `Seq<&T>`, and `unref` for the reverse direction.
- **`will_return_none`** — return `true` if the iterator will eventually return `None`.
  Infinite iterators or iterators driven by a non-terminating closure may return `false`.
- **`decrease`** — a termination metric for Verus's decreases checker.  By default,
  `for` loops expect this to return `Some(n)` where `n` decreases on every call to `next`. Here `j - i` works.
- **`initial_value_relation`** — a prophetic invariant relating the iterator's initial state to
  the exec expression used to initialize it. This is what lets loop invariants
  refer to the original collection (e.g., `iter.seq() == v@`).
- **`peek`** — optionally returns the item at a given look-ahead index. Providing this
  helps Verus reason about the current element in the iteration.


```rust
{{#include ../../../../examples/guide/iterators.rs:iter_spec}}
```

### 4. The constructor

Most iterator types will need to be constructed from some other type.  In our example,
our constructor `vec_iter` will take in a `&'a Vec<T>` and return a `VecIterator<'a, T>`.
As shown below, you'll typically want (at least) the three postconditions shown below;
the first one connects the iterator's prophetic sequence to the 
values it was constructed from (in this case, the elements of the
`Vec<T>`);
the second enables a `for` loop to automatically prove termination;
and the third connects the value used to construct the iterator
to its prophecied sequence of yielded values.

```rust
{{#include ../../../../examples/guide/iterators.rs:iter_creation}}
```

### 5. Implementing `DoubleEndedIterator`

If your iterator supports backward traversal, implement the standard Rust
`DoubleEndedIterator` trait, which adds a `next_back` method:

```rust
{{#include ../../../../examples/guide/iterators.rs:double_iter_next_back}}
```

To allow reasoning about `.rev()`, you also need to implement `DoubleEndedIteratorSpecImpl`
(analogous to `IteratorSpecImpl`), providing a `peek_back` function that returns the item
at a given index from the back. Without it, Verus will not know what elements the reversed
iterator will produce.

```rust
{{#include ../../../../examples/guide/iterators.rs:double_iter_spec}}
```
