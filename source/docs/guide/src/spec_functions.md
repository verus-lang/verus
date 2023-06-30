# spec functions

Let's start with a simple `spec` function that computes the minimum of two integers:

```rust
{{#include ../../../rust_verify/example/guide/modes.rs:spec_fun1}}
```

Unlike `exec` functions,
the bodies of `spec` functions are visible to other functions in the same module,
so the `test` function can see inside the `min` function,
which allows the assertions in `test` to succeed.

Across modules, the bodies of `spec` functions can be made public to other modules
or kept private to the current module.
The body is public if the function is marked `open`,
allowing assertions about the function's body to succeed in other modules:

```rust
{{#include ../../../rust_verify/example/guide/modes.rs:spec_fun_mod1}}
```

By contrast, if the function is marked `closed`,
then other modules cannot see the function's body,
even if they can see the function's declaration. By contrast,
functions within the same module can view a `closed spec fn`'s body. 
In other words, `pub` makes the declaration public,
while `open` and `closed` make the body public or private.
All `pub` `spec` functions must be marked either `open` or `closed`;
Verus will complain if the function lacks this annotation.

```rust
{{#include ../../../rust_verify/example/guide/modes.rs:spec_fun_mod2}}
```

In the example above with `min` being `closed`,
the module `M2` can still talk about the function `min`,
proving, for example, that `min(10, 20)` equals itself
(because everything equals itself, regardless of what's in it's body).
On the other hand, the assertion that `min(10, 20) == 10` fails,
because `M2` cannot see `min`'s body and therefore doesn't know that `min`
computes the minimum of two numbers:

```
error: assertion failed
   |
   |         assert(min(10, 20) == 10); // FAILS
   |                ^^^^^^^^^^^^^^^^^ assertion failed
```

After the call to `lemma_min`, the assertion that `min(10, 20) <= 10` succeeds because `lemma_min` exposes `min(x,y) <= x` as a post-condition. `lemma_min` can prove because this postcondition because it can see the body of `min` despite `min` being `closed`, as `lemma_min` and `min` are in the same module.

You can think of `pub open spec` functions as defining abbreviations
and `pub closed spec` functions as defining abstractions.
Both can be useful, depending on the situation.

`spec` functions may be called from other `spec` functions
and from specifications inside `exec` functions,
such as preconditions and postconditions.
For example, we can define the minimum of three numbers, `min3`,
in terms of the mininum of two numbers.
We can then define an `exec` function, `compute_min3`,
that uses imperative code with mutable updates to compute
the minimum of 3 numbers,
and defines its postcondition in terms of the `spec` function `min3`:

```rust
{{#include ../../../rust_verify/example/guide/modes.rs:spec_fun3}}
```

The difference between `min3` and `compute_min3` highlights some differences
between `spec` code and `exec` code.
While `exec` code may use imperative language features like mutation,
`spec` code is restricted to purely functional mathematical code.
On the other hand, `spec` code is allowed to use `int` and `nat`,
while `exec` code is restricted to compilable types like `u64`.
