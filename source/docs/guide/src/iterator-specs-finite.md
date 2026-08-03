# Implementing Iterator Specifications for Finite Iterators

Let's start with the most common class of iterators: those that eventually
return `None` and then continue to return `None` on all subsequent calls to
`next()`.  To illustrate the [steps needed to verify an iterator implementation](iterator-specs.md) 
for a custom type, in the example below, we'll imagine that `Vec`
doesn't provide an iterator, so we're going to implement one for it.

### 1. The iterator struct

Our `VecIterator` struct holds a reference to the underlying `Vec` plus indices `i` and `j`
marking the current and end positions. The type invariant enforces that `i <= j <=
v.len()` at all times.  Because we're using a type invariant, the fields of `VecIterator`
need to remain private.  However, because we'll want to refer to the contents of `v` in
some of our specs, we provide a closed spec fn (`elts()`) to allow us to reason about them
abstractly.

```rust
{{#include ../../../../examples/guide/iterators.rs:iter_def}}
```

### 2. The `next` method

This is an ordinary Rust `Iterator` implementation with no Verus-specific annotations.
It uses the type invariant to prove that it meets the generic Verus specification for `Iterator::next()`.

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
  the Verus specification for `next`.  We include this spec function to avoid (unsoundly) assuming
  that every unverified iterator implementation satisfies our specs (this is a [common pattern](external_trait_specifications.md#the-obeys_-pattern-in-vstd) for `vstd` trait specifications).

  Verified iterator implementations should return `true` here,
  and most iterator adaptors should return their inner iterator's value.  Developers can choose
  to assume this is true for unverified iterators (e.g., those from unverified crates).
  That entails assuming that the iterator (a) obeys the specifications in `IteratorSpec`,
  and (b) always returns `Some`, or eventually returns `None`, and after that point, continues
  to return `None`. 
- **`remaining`** — a [prophetic](https://verus-lang.github.io/verus/verusdoc/vstd/proph) spec 
  function returning the sequence of items that the iterator will
  eventually produce for each call to `next()`. For `VecIterator`, this is the subrange `v[i..j]`.  Note that `remaining`
  returns a `Seq<Self::Item>`; as a result, because our `VecIterator`'s `Item` is `&T`, its
  `remaining` function will return `Seq<&T>`.  The sequence library in `vstd` provides the convenience
  function `as_ref` to convert `Seq<T>` to `Seq<&T>`, and `unref` for the reverse direction.
- **`will_return_none`** — return `true` if the iterator will eventually return `None`.
  Infinite iterators or iterators driven by a non-terminating closure may return `false`.
- **`decrease`** — a termination metric for Verus's [decreases checker](recursion.md).  By default,
  `for` loops expect this to return `Some(n)` where `n` decreases on every call to `next`. Here `j - i` works.  Infinite iterators should return `None`.
- **`peek`** — optionally returns the item at a given look-ahead index. Providing this
  helps Verus reason about the current element in the iteration.  Note that `peek` is **not** prophetic,
  so we can't define it in terms of `remaining()`.  

In summary, here's what our implementation of these specs looks like for `VecIterator`.
```rust
{{#include ../../../../examples/guide/iterators.rs:iter_spec}}
```

### 4. The constructor

Most iterator types will need to be constructed from some other type.  In our example,
our constructor `vec_iter` will take in a `&'a Vec<T>` and return a `VecIterator<'a, T>`.
As shown below, you'll typically want postconditions like those shown below.
The first one connects the iterator's prophetic sequence to the 
values it was constructed from (in this case, the elements of the `Vec<T>`).
The second one connects the prophetic sequence to the iterator's abstract `elts()`;
we need that connection, since peek is defined in terms of `elts()` (not `remaining()`).
The third postcondition enables a `for` loop to automatically prove termination.
The final postcondition  connects the value used to construct the iterator
to its prophecied sequence of yielded values.

```rust
{{#include ../../../../examples/guide/iterators.rs:iter_creation}}
```

### 5. Implementing `DoubleEndedIterator`

If your iterator supports backward traversal, implement the standard Rust
[`DoubleEndedIterator` trait]((https://doc.rust-lang.org/std/iter/trait.DoubleEndedIterator.html)), 
which adds a `next_back` method:

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
