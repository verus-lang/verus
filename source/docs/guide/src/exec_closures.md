# Exec closures

In the previous sections, we discussed how Verus uses closure syntax `|x| { ... }`
as part of various `spec`-mode features (mathematical functions, quantifiers).
Verus also supports closures as they are used in ordinary Rust, that is,
to define anonymous, _executable_ functions that may be passed around and called.



## Closure Contexts and function traits: `FnOnce`, `FnMut`, and `Fn`

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


