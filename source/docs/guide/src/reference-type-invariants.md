# Type invariants

Structs and enums may be augmented with a _type invariant_, a boolean predicate indicating
well-formedness of a value. The type invariant applies to **any exec object or tracked-mode ghost object** and **does not apply to spec objects**.

Type invariants are primarily intended for _encapsulating and hiding invariants_.

### Declaring a type invariant

A type invariant may be declared with the `#[verifier::type_invariant]` attribute.
It can be declared either as a top-level item or in an impl block.

```rust
#[verifier::type_invariant]
spec fn type_inv(x: X) -> bool { ... }
```

```rust
impl X {
    #[verifier::type_invariant]
    spec fn type_inv(self) -> bool { ... }
}
```

It can be inside an `impl` block and take `self`, of it can be declared as a top-level item.
It can have any name.

The invariant predicate must:

 * Be a spec function of type `(X) -> bool` or `(&X) -> bool`,
   where `X` is the type the invariant is applied to.
 * Be applied to a datatype (`struct` or `enum`) that:
   * Is declared in the same crate
   * Has no fields public outside of the crate

There is no restriction that the type invariant function have the same _visibility_ as the
type it is declared for, only that it is visible whenever the type invariant needs to be asserted
or assumed (as described below). Since type invariants are intended for encapsulation,
it is recommended that it be as private as possible.

### Enforcing that the type invariant holds

For any type `X` with a type invariant,
Verus enforces that the predicate always hold for any exec object or tracked-mode ghost object
of type `X`.  Therefore, Verus add a proof obligation that the predicate holds:

 * For any constructor expression of `X`
 * After any assignment to a field of `X`
 * After any function call that takes a mutable borrow to `X` 

Currently, there is no support for "temporarily breaking" a type invariant, though this
capability may be added in the future. This can often be worked around by taking mutable
borrows to the fields.

### Applying the type invariant

Though the type invariant is enforced automatically, it is not provided to the user automatically.
For any object `x: X` with a type invariant, you can call the builtin pseudo-lemma `use_type_invariant` to learn that the type invariant holds on `x`.

```
use_type_invariant(&x);
```

The value `x` must be a tracked or exec variable.
This statement is a proof feature, and if it appears in an `exec` function, it must be in
a `proof` block.

### Example

```rust
struct X {
    i: u8,
    j: u8,
}

impl X {
    #[verifier::type_invariant]
    spec fn type_inv(self) -> bool {
        self.i <= self.j
    }
}

fn example(x: X) {
    proof {
        use_type_invariant(&x);
    }

    assert(x.i <= x.j); // succeeds
}

fn example_caller() {
    let x = X { i: 20, j: 30 }; // succeeds
    example(x);
}

fn example_caller2() {
    let x = X { i: 30, j: 20 }; // fails
    example(x);
}
```
