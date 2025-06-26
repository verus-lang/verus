# Assertions about mutable references

Assertions containing mutable references allow us to make statements about the *prior* (at the beginning of the function call) and *current* state of the piece of memory to which the mutable reference points. Consider the following example: 

```rust
{{#include ../../../../examples/guide/references.rs:asserts}}
```

In the `check_and_assert` function call, `*old(a)` refers to the dereferenced value of the mutable reference `a` at the *beginning* of the function call and `*a` refers to the *current* dereferenced value of the mutable reference `a`.

Below is a slightly more complicated example involving both `assert`, `requires`, and `ensures`:

```rust
{{#include ../../../../examples/guide/references.rs:complex}}
```
