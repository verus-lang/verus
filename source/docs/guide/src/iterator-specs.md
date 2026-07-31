# Iterator Specifications for a Custom Type

To reason about iteration over your own custom type,
you need to:
1. Define the iterator struct, similar to how various Rust types have a corresponding iterator
type; e.g., a Rust slice relies on a [`std::slice::Iter`](https://doc.rust-lang.org/std/slice/struct.Iter.html) struct.
2. Implement the standard Rust `Iterator` trait (`next`).
3. Implement the `IteratorSpecImpl` trait to provide a Verus specification.
4. Write a constructor function for your type and provide some useful postconditions about the constructed iterator.

In the following sections, we illustrate how to follow this process
for finite iterators (those that eventually return `None`) and for
infinite iterators (those that always return `Some`).  At present,
Verus does not support verifying iterators that return `None` and then
start returning `Some` again.


