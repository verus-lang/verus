# Iterators

**These will be available starting May 8th**

Verus supports verifying `for` loops over any type that implements the Rust
[`Iterator`](https://doc.rust-lang.org/std/iter/trait.Iterator.html) trait, as
long as that type comes with appropriate Verus specifications.  This page
explains how to write loop invariants using the specifications Verus provides
in `vstd`.  For information on how to add specifications to your own iterator
type, see [Iterator Specifications for a Custom Type](./iterator-specs.md).

## Ghost State in For Loops

Verus allows you to name the iterator that Rust uses inside a `for` loop:

```rust
for x in my_iter: some_expression
    invariant
        // can refer to iter.index() and iter.seq()
{
    // x is the current element; iter tracks ghost state
}
```
You can use this name (`my_iter` above) to refer to the number of iterations
thus far: `my_iter.index()`.  You can also use `my_iter.seq()` to refer to the
complete sequence of items the iterator will yield, from its starting position.
This is a *prophetic* value: Verus knows it up front even though the iterator
hasn't run yet.  In `for` loops without a `break`, after the loop completes, we
also know that `my_iter.index() == my_iter.seq().len()`.

### Example: checking all elements are positive

```rust
{{#include iterators.rs:usage_example}}
```

The invariant tracks progress via `iter.index()`. When the loop finishes, we know the
invariant held for every `i` up to `iter.seq().len()`, which equals `v.len()`.

### Range iterators

Standard Rust integer ranges work the same way:

```rust
{{#include iterators.rs:build_range}}
```

For a range `0..n`, `r_iter.seq()[k] == k`, so `r_iter.seq()[r_iter.index()]` equals the
current element `i`.

### Omitting the wrapper

If you don't need ghost state in your invariant, you can omit the `my_iter:` binding:

```rust
{{#include iterators.rs:no_binding}}
```

### Reversed iteration

The same specification style applies to Iterator adaptors.
For example, for iterators that implement Rust's
[`DoubleEndedIterator`](https://doc.rust-lang.org/std/iter/trait.DoubleEndedIterator.html),
you can call `.rev()` to iterate in reverse.  The `seq()` and `index()`
specifications work identically — they refer to the reversed sequence:

```rust
{{#include iterators.rs:rev_example}}
```

