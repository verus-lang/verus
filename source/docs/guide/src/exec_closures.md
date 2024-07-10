# Closures

In the previous chapter, we saw how to pass functions as values, which we did by referencing
function items by name. However, it is more common in Rust to creating functions
using _closures_.

## Preconditions and postconditions on a closure

Verus allows you to specify `requires` and `ensures` on a closure just like you can for
any other function.
Here's an example, calling the `vec_map` function we defined in the
[previous chapter](./exec_funs_as_values.md'):

```rust
{{#include ../../../rust_verify/example/guide/higher_order_fns.rs:vec_map_example_with_closure}}
```

## Closure capturing

One of the most challenging aspects of closures, in general, is that closures
can capture variables from the surrounding context.
Rust resolves this challenge through its hierarcy of function traits:
`FnOnce`, `FnMut`, and `Fn`.
The declaration of the closure and the details of its context capture determine
which traits it has. In turn,
the traits determine what capabilities the caller has: Can they call it more than
once? Can they call it in parallel?

See [the Rust documentation](https://doc.rust-lang.org/book/ch13-01-closures.html#moving-captured-values-out-of-closures-and-the-fn-traits) for a more detailed introduction.

In brief, the traits provide the following capabilities to callers and
restrictions on the context capture:

|          | Caller capability                            | Capturing                               |
|----------|----------------------------------------------|-----------------------------------------|
| `FnOnce` | May call once                                | May move variables from the context     |
| `FnMut`  | May call multiple times via `&mut` reference | May borrow _mutably_ from the context   |
| `Fn`     | May call multiple times via `&` reference    | May borrow _immutably_ from the context |

Verus does not yet support borrowing mutably from the context,
though it does handle moving and immutable borrows easily.
Therefore, Verus has better support for `Fn` and `FnOnce`---it does not yet take advantage of the
capturing capabilities supported by Rust's `FnMut`.

Fortunately, both move-captures and immutable-reference-captures are easy to handle,
as we can simply take their values inside the closure to be whatever they are at the program
point of the closure expression.

Example:

```rust
{{#include ../../../rust_verify/example/guide/higher_order_fns.rs:closure_capture}}
```
