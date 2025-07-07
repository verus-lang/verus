# Mutation, references, and borrowing

The cornerstone of Rust's type system is its formulation of [ownership, references, and borrowing](https://doc.rust-lang.org/book/ch04-00-understanding-ownership.html).
In this section, we'll discuss how Verus handles these concepts.

## Rust review

In short, ownership is Rust's way of managing memory safely. Every piece of memory that is allocated and used in a Rust program has one owner. For example, when assigning 42 to the variable x, x is the owner of that particular numerical value. Owners can be variables, structs, inputs to functions, etc. Owners can change through an action called move — but, at any given time, a particular piece of memory can only have one owner. Finally, when a piece of memory's owner goes out of scope, the piece of memory is no longer considered valid and cannot be accessed in the program.

Since it can often be cumbersome or expensive to transfer ownership and make copies of data,
Rust also provides a _reference_ system to allow access to data via pointers
without obtaining full ownership.
To maintain memory safety, Rust enforces several restrictions on their use:
every memory location in a Rust program (e.g., stack variable, heap-allocated memory)
will always, at any point in time, have either:

 * No live references
 * One or more **immutable** references (denoted by the type `&T`)
 * Exactly one **mutable** reference (denoted by the type `&mut T`)

As suggested by the name, immutable references only grant read-only access to a particular
piece of memory, while mutable references grant write-access. However, even mutable references
don't have the same power as full ownership, for example, they cannot _deallocate_ the memory
being pointed to.

Though the system may seem restrictive, it has a number of compelling consequences,
such as the enforcement of temporal memory safety and data-race-freedom. It also has signficant
advantages for Verus, greatly simplifying the verification conditions needed to prove code correct.

## Borrowing in Verus

### Immutable borrows

Verus has full support for immutable borrows. These are the easiest to use, as Verus treats
them the same as non-references, e.g., to Verus, a `&u32` is the same as a `u32`.
In nearly all situations, there is no need to reason about the pointer address.

```rust
{{#include ../../../../examples/guide/references.rs:immut}}
```

### Mutable borrows

Currently, Verus only supports the use of mutable references as arguments to a function, such as in the following example.

```rust
{{#include ../../../../examples/guide/references.rs:mut}}
```

In the subsequent chapters, we'll discuss more how to verify code with mutable references,
e.g., how to write specifications on functions that take mutable arguments.

### Lifetime variables

Rust's type system sometimes requires the use of [lifetime variables](https://doc.rust-lang.org/book/ch10-03-lifetime-syntax.html?highlight=lifetime) to check that borrows are used correctly
(i.e., that they obey the mutual-exclusivity rules discussed above).
Fortunately, these have essentially no impact on verification.
Besides the lifetime checks that Rust always does, Verus ignores lifetime variables for the sake
of theorem-proving.
