# Implementing Iterator Specifications for Infinite Iterators

Somewhat surprisingly, we can also follow the same 
[steps verify an iterator implementation](iterator-specs.md)
for a custom type that implements an infinite iterator!

Let's start with an infinite iterator built on a counter that increments
each time we call `next()`, wrapping when we would otherwise overflow.

### 1. The iterator struct

`IterCtr` holds the 64-bit counter value (`ctr`), and a 
[prophetic](https://verus-lang.github.io/verus/verusdoc/vstd/proph)
length field that defines how long the sequence of return values will be.
At this point, we don't know what the length is; we just know it has 
some value.

```rust
{{#include ../../../../examples/guide/iterators.rs:ctr_iter_def}}
```

### 2. The `next` method

This is an ordinary Rust `Iterator` implementation.  However,
we do need to include a proof that `next()` meets its obligations, especially the obligation
that the value returned by `next()` matches the first element in the prophesized `remaining` 
sequence.  Here, the key idea is to swap the existing prophecy variable (in `self.len`)
with a newly created prophecy variable.  We then resolve the old prophecy variable in such
a way that its final value is one more than the prophecy variable we just created.  This
is enough to show that the prophetic sequence's length decreased by one, just as the spec
for `next()` demands.

```rust
{{#include ../../../../examples/guide/iterators.rs:ctr_normal_iter}}
```

### 3. The spec implementation

In `vstd`, Verus provides `IteratorSpec`, an extension of the Rust
[`Iterator`](https://doc.rust-lang.org/std/iter/trait.Iterator.html) trait that
defines a variety of specification functions, as well as the Verus specs for
the `next()` function.  To enable us to reason about our custom iterator, we
need to implement the Verus-provided `IteratorSpecImpl` trait (not the
`IteratorSpec` trait that defines the specs -- see ["External trait
specifications"](external_trait_specifications.md) for more details).
The discussion of [finite iterators](iterator-specs-finite.html#3-the-spec-implementation)
describes the purpose of each of these functions.
Here's how we define them for our custom iterator.

- **`obeys_prophetic_iter_laws`** — We return `true`, since our implementation
  is verified to obey the specs prescribed by `IteratorSpec`.
- **`remaining`** — Our prophetic sequence has some (unknown) length predicted
  by `self.len`.  The contents are simply the current value of the counter,
  incremented by 1 at each step and wrapping after `u64::MAX`.
- **`will_return_none`** — This is an infinite iterator, so we can return `false` here.
- **`decrease`** — This is an infinite iterator, so we don't have a valid decreases metric
  available, so we return `None`.
- **`peek`** — It's simple to predict what this value will be, and it helps improve 
  automation, so we return `Some` with the appropriate value.

```rust
{{#include ../../../../examples/guide/iterators.rs:ctr_iter_spec}}
```

### 4. The constructor

Our constructor's postconditions are simpler than in the finite case,
since we don't need to promise the iterator will terminate.


### Example Usage

Here's a small example that makes use of our new infinite iterator:
```rust
{{#include ../../../../examples/guide/iterators.rs:ctr_usage_example}}
```
Naturally we need to use the [`exec_allows_no_decreases_clause` attribute](reference-attributes.md#verifierexec_allows_no_decreases_clause), since this loop will never terminate.

### Soundness

It may initially seems troubling that we can specify the outputs of an infinite iterator
with a finite sequence.  One way to understand what's happening in this example
is that at each program point, we're quantifying over "all sequences that don't 
contradict the prefix that has been observed so far".  That set remains non-empty 
no matter how long the program executes.


## Implementing `DoubleEndedIterator`

We can extend this idea even further to support infinite iterators that nonetheless
implement  Rust's [`DoubleEndedIterator` trait](https://doc.rust-lang.org/std/iter/trait.DoubleEndedIterator.html).
Here's an example where `next()` always returns 42 and `next_back()` always returns 43.
Instead of prophesizing one length, we prophesize the number of 42s and the number of 43s we'll return:
```rust
{{#include ../../../../examples/guide/iterators.rs:inf_dbl_def}}
```

We then use the two prophecies to give the natural definition of `remaining`: 
```rust
{{#include ../../../../examples/guide/iterators.rs:inf_dbl_spec}}

```
As a result, the implementations of `next()` and `next_back()` are straightforward, 
following the earlier above and using the same "trick" of swapping in a new
prophecy variable whose value is one less than the old prophecy variable.


See the [full file](https://github.com/verus-lang/verus/blob/main/examples/guide/iterators.rs) for more details.

