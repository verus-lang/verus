# Memory safety is conditional on verification

Let's briefly compare and contrast the philosophies of Rust and Verus with regards to
memory safety. Memory safety, here, refers to a program being free of any
_undefined behavior (UB)_ in its memory access.
Both Rust and Verus _rely_ on memory safety being upheld; in turn,
they both do a great deal to _enforce_ it. However, they enforce it in different ways.

Rust's enforcement of memory safety is built around a contract between "safe" and
"unsafe" code.  The [first chapter of the Rustonomicon](https://doc.rust-lang.org/nomicon/safe-unsafe-meaning.html)
summarizes the philosophy. In short: any "safe" code (i.e., code free of the `unsafe` keyword) 
must be memory safe, enforced by Rust itself via its type-checker and borrow-checker,
regardless of user error. However, if any code uses `unsafe`, it is the responsibility
of the programmer to ensure that the program is memory safe---and if the programmer fails to
do so, then the behavior of the program is undefined (by definition).

In practice, of course, most code _does_ use `unsafe`, albeit only indirectly.
Most code relies on low-level utilities that can only be implemented with unsafe code,
including many from the standard library (e.g., `Arc`, `RefCell`, and so on), but also
from user-provided crates. In any case, the Rust philosophy is that the providers of these
low-level utilities should meet a standard of "unsafe encapsulation."
A programmer interacting using the library only through its safe API (and also not using
`unsafe` code anywhere else) should not be able to exhibit undefined behavior,
_not even by writing buggy code or using the API is an unintended way_.
As such, the library implementors need to code defensively against all possible ways the
client might use the safe API.
When they are successful in this, the clients once again gain the guarantee that they
cannot invoke UB without `unsafe` code.

By contrast, Verus does not have an "unsafe/safe" distinction, nor does it have a notion
of unsafe encapsulation. This is because it verifies _both_ memory safety and other
forms of correctness through [Verus specifications](./requires_ensures.md).

### Example

Consider, for example, the [index operation in Rust's standard `Vec` container](https://doc.rust-lang.org/std/vec/struct.Vec.html#method.index).
If the client calls this function with an index that is not in-range for the vector's
length, then it is likely a bug on the part of the client. However, the index operation
is part of the safe API, and therefore it must be robust to such things, and it can never
attempt to read out-of-bounds memory. Therefore, the implementation of this operation has
to do a bounds check (panicking if the bounds check fails).

On the other hand, consider this (possible) implementation of `index` for Verus's
`Vec` collection:

```rust,ignore
impl<A> Vec<A> {
    #[verifier::external_body]
    pub fn index(&self, i: usize) -> (r: &A)
        requires
            i < self.len(),
        ensures
            *r === self[i as int],
    {
        unsafe { self.vec.get_unchecked(i) }
    }
}
```

Unlike Rust's `index`, this implementation has no bounds checks, and it exhibits UB if called
for a value of `i` that is out-of-bounds. Therefore, as ordinary Rust, it would not meet
the standards of unsafe encapsulation.

However, due to its `requires` clause,
Verus enforces that any call to this function _will_ satisfy the contract and be in-bounds.
Therefore, UB cannot occur in a _verified_ Verus program, but type-checking alone is not
sufficient to ensure this.

### Conclusion

Rust's concept of unsafe encapsulation means that programmers writing in safe Rust can be sure
that their programs will be memory safe as long as they type-check and pass the borrow-checker, 
even if their code otherwise has bugs.

In Verus, there is no staggered notion of correctness. If the program verifies, then it is
memory safe, and it will execute according to all its specifications.
If the program fails to verify, then all bets are off.
