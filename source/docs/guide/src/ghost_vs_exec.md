# Ghost code vs. exec code

The purpose of `exec` code is to manipulate physically real values ---
values that exist in physical electronic circuits when a program runs.
The purpose of ghost code, on the other hand,
is merely to *talk about* the values that `exec` code manipulates.
In a sense, this gives ghost code supernatural abilities:
ghost code can talk about things that could not be physically implemented at run-time.
We've already seen one example of this with the types `int` and `nat`,
which can only be used in ghost code.
As another example, ghost code can talk about the result of division by zero:

```rust
{{#include ../../../rust_verify/example/guide/modes.rs:ghost_abilities0}}
```

This simply reflects the SMT solver's willingness to reason about the result of division by zero
[as an unspecified integer value](https://microsoft.github.io/z3guide/docs/theories/Arithmetic/#division).
By contrast, Verus reports a verification failure if `exec` code attempts to divide by zero:

```
error: possible division by zero
    |
    |     let y = x / 0; // FAILS
    |             ^^^^^
```

Two particular abilities of ghost code[^note_tracked] are worth keeping in mind:
- Ghost code can copy values of any type,
  even if the type doesn't implement the Rust `Copy` trait.
- Ghost code can create a value of any type[^note_uninhabited],
  even if the type has no public constructors
  (e.g. even if the type is struct whose fields are all private to another module).

For example, the following `spec` functions create and duplicate values of type `S`,
defined in another module with private fields and without the `Copy` trait:

```rust
{{#include ../../../rust_verify/example/guide/modes.rs:ghost_abilities1}}
```

These operations are not allowed in `exec` code.
Furthermore, values from ghost code are not allowed to leak into `exec` code ---
what happens in ghost code stays in ghost code.
Any attempt to use a value from ghost code in `exec` code will result in a compile-time error:

```rust
{{#include ../../../rust_verify/example/guide/modes.rs:ghost_abilities2}}
```

```
error: cannot call function with mode spec
    |
    |         let pair = duplicate_S(s); // FAILS
    |                    ^^^^^^^^^^^^^^
```

As an example of ghost code that uses these abilities,
a call to the Verus [`Seq::index(...)` function](https://github.com/verus-lang/verus/blob/main/source/vstd/seq.rs)
can duplicate a value from the sequence, if the index `i` is within bounds,
and create a value out of thin air if `i` is out of bounds:
```
impl<A> Seq<A> {
...
    /// Gets the value at the given index `i`.
    ///
    /// If `i` is not in the range `[0, self.len())`, then the resulting value
    /// is meaningless and arbitrary.

    pub spec fn index(self, i: int) -> A
        recommends 0 <= i < self.len();
...
}
```

---

[^note_tracked]: Variables in `proof` code can opt out of these special abilities using
the `tracked` annotation (see section TODO),
but this is an advanced feature that can be ignored for now.

[^note_uninhabited]: This is true even if the type has no values in `exec` code,
like the Rust `!` "never" type
(see the "bottom" value in [this technical discussion](https://github.com/Chris-Hawblitzel/rust/wiki/Three-kinds-of-code-...-specification,-proof,-and-executable)).
