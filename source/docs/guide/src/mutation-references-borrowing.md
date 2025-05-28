# Mutation, references, and borrowing

The Rust documentation provides a comprehensive overview of ownership, references, and borrowing [here](https://doc.rust-lang.org/book/ch04-00-understanding-ownership.html).

In short, ownership is Rust's way of managing memory safely. Every piece of memory that is allocated and used in a Rust program has one owner. For example, when assigning 42 to the variable x, x is the owner of that particular numerical value. Owners can be variables, structures, inputs to functions, etc. Owners can change through an action called move - but, at any given time, a particular piece of memory can only have one owner. Finally, when a piece of memory's owner goes out of scope, the piece of memory is no longer considered valid and cannot be accessed in the program.

Needing to move ownership between variables or make explicit copies of pieces of memory in order for multiple parts of the program to access to a particular piece of memory can be cumbersome. Therefore, in practice, references are used. References are like pointers to the particular piece of memory, but with additional memory-safety guarantees. Every piece of memory that is allocated and used in a Rust program has either no references, one or more immutable references, OR one mutable references - these three scenarios are exclusive. There are two types of references - mutable and immutable references. 

Immutable references grant read-only access to a particular piece of memory. As such, a particular piece of memory can have any number of immutable references at a time. Mutable references grant read-and-write access to a particular piece of memory. However, they do not have the same power as owners - for example, they cannot deallocate or free a particular piece of memory. Since mutable references can modify pieces of memory, a particular piece of memory can only have *one* mutable reference and no immutable references. This is to avoid data races, where multiple parties are reading or writing to a singular piece of memory and depending on the, at the time unknown, ordering of these operations, can yield very different results. 

The action of creating a reference is called borrowing - since the reference is "borrowing" some access to the piece of memory from the owner. This reference will have a lifetime, which determines for which part of the program it is a valid reference that can be used. This lifetime is determined by Rust's borrow checker and corresponds to where the reference is declared up until the last time that the reference is used in the program. In certain cases, Rust will require that this lifetime is marked manually, to make sure that the reference rules, for example, of having only one mutable reference at a time or no co-existing mutable and immutable references, are upheld.

The Rust documentation linked above provides many examples for these concepts. 

Currently, Verus fully supports the use of immutable references and partially supports the use of mutable references. 

```rust
{{#include ../../../../examples/guide/references.rs:immut}}
```

Verus only support the use of mutable references as arguments to a function, such as in the following example. 

```rust
{{#include ../../../../examples/guide/references.rs:mut}}
```

Given that the pieces of memory to which mutable references point can be modified during function calls, we need a particular way to talk about their old and updated in Verus spec code, particularly in the requires and ensures of functions and in asserts.